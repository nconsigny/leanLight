import LeanLightEvmProofs.Agree
import EthLib.Execution.Proofs.Transactions.Noninterference
import EthLib.Execution.Proofs.Transactions.NoninterferenceRun
import EthLib.Execution.Proofs.Transactions.Observe
import EthLib.Execution.Proofs.Transactions.CodeOrigin
import EthLib.Execution.Proofs.Evm.Call.NoninterferenceRun
import EthLib.Execution.Proofs.Evm.Call.Candidate
import EthLib.Execution.Proofs.State.CodeAvailability

/-!
# `prepare` and the run on agreeing states

`prepare` reads its state through two terms only: the sender's account, and the state with the
sender's nonce incremented (whose sender's balance and recipient's code it then reads).
`prepareFrom` is `prepare` with those two terms as arguments (`prepare_eq`, by `rfl`), so that
`prepare` on the facts' state and on a full state that agrees with it on the sender can be
compared step by step.
-/

namespace LeanLightEvmProofs

open LeanLightEvm
open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.Evm
open EthLib.Execution.Transactions

/-- `prepare`, with the sender's account and the state after the sender's nonce increment given
as arguments; `prepare_eq` says that it is `prepare`. -/
def prepareFrom (rules : LeanLightEvm.Activation) (chainId : Nat) (h : Header)
    (ancestors : Option (List Hash32)) (cap : Nat) (r : Request) (account : Account)
    (incremented : Except StateError TransactionState) : Except PrepareStop Prepared := do
  let fork := rules.fork
  let env := environment fork rules.blobSchedule chainId h (blockHashes h ancestors)
  let sender := r.sender
  let gas := r.gas.getD env.gasLimit
  let t : Transaction := .legacy
    { nonce := ← word "nonce" account.nonce, gasPrice := 0, gas := ← word "gas" gas, to := r.to,
      value := ← word "value" r.value, data := r.data, v := 0, r := 0, s := 0 }
  unless t.value.toNat ≤ account.balance.toNat do throw (.refused .insufficientFunds)
  let target ← (messageTarget sender account.nonce t).mapError fun _ => .refused .noCreationAddress
  let state ← incremented.mapError fun _ => .refused .senderAccount
  unless t.value.toNat ≤ (state.getAccount sender).balance.toNat do
    throw (.refused .insufficientFunds)
  let initCodeFits : Except PrepareStop Unit :=
    unless (fork ≥ .shapella → t.to = none → t.data.size ≤ maxInitCodeSize fork) do
      throw (.refused (.initCodeTooLarge t.data.size))
  let coversMinimum : Except PrepareStop Unit :=
    unless minimumGas fork sender t ≤ gas do throw (.refused .intrinsicGasTooLow)
  if fork ≥ .glamsterdam then
    initCodeFits
    coversMinimum
  else
    coversMinimum
    initCodeFits
  let intrinsic := intrinsicGas fork sender t
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice := 0, blobVersionedHashes := fun _ => t.blobHashes }
  let alloc := allocateGas fork t intrinsic
  let execution := min alloc.execution cap
  let message ← (transactionMessage env txEnv state sender target execution t).mapError fun
    | .state (.missingCode c) => .missingCode c
    | _ => .internal
  return { fork, env, sender, transaction := t, state
           message := { message with reservoir := alloc.reservoir }
           substate := startSubstate fork env.coinbase sender target t
           intrinsic, execution, reservoir := alloc.reservoir
           capped := cap < alloc.execution }

theorem prepare_eq (rules : LeanLightEvm.Activation) (chainId : Nat) (h : Header)
    (ancestors : Option (List Hash32)) (cap : Nat) (r : Request) (S : State) :
    prepare rules chainId h ancestors cap r S =
      prepareFrom rules chainId h ancestors cap r
        ((TransactionState.ofBlock (blockOf S)).getAccount r.sender)
        ((TransactionState.ofBlock (blockOf S)).incrementNonce rules.fork r.sender) := rfl

/-! ## Copies of EthLib's private lemmas

The next four are EthLib's (CC0-1.0), at the pin `core/EthLib/PIN`, copied with their proofs
because they are `private` there: `exists_transactionMessage` and
`processMessageCall_transactionMessage` (`Proofs/Transactions/NoninterferenceRun.lean:287,302`,
same names here), and `keepsCandidates_modifyState` and `keepsCandidates_incrementNonce`, EthLib's
`KeepsCandidates.modifyState` and `KeepsCandidates.incrementNonce`
(`Proofs/Evm/Call/Candidate.lean:73,138`; the lines are those of the `private theorem`). -/

section Copies

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- On a state that holds every code, the message of a transaction is built. -/
theorem exists_transactionMessage {env : BlockEnvironment fork}
    (txEnv : TransactionEnvironment fork) {state : TransactionState} (hcodes : HasCodes state)
    (sender target : Address) (gas : Nat) (t : Transaction) :
    ∃ message, transactionMessage env txEnv state sender target gas t = .ok message := by
  unfold transactionMessage
  split
  · rename_i to _
    obtain ⟨c, hc⟩ := hcodes to
    rw [hc]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Two messages of a transaction, built on two states, give the same run.

They differ at most in the code that a call fetches, which the run ignores. -/
theorem processMessageCall_transactionMessage [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {txEnv : TransactionEnvironment fork}
    {state state' : TransactionState} {sender target : Address} {gas : Nat} {t : Transaction}
    {message message' : Message fork}
    (h : transactionMessage env txEnv state sender target gas t = .ok message)
    (h' : transactionMessage env txEnv state' sender target gas t = .ok message')
    (chainId reservoir : Nat) (start : TransactionState) (substate : Substate)
    (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    processMessageCall (Meter := Meter) chainId { message' with reservoir } start substate auths
        paid =
      processMessageCall (Meter := Meter) chainId { message with reservoir } start substate auths
        paid := by
  have htarget := (target_transactionMessage h).1
  unfold transactionMessage at h h'
  cases hto : t.to with
  | some to =>
    simp only [hto] at h h' htarget
    obtain ⟨c, -, hm⟩ := EthLib.Base.map_ok_iff.mp h
    obtain ⟨c', -, hm'⟩ := EthLib.Base.map_ok_iff.mp h'
    have hcode : message' = { message with code := c' } := by
      rw [← hm, ← hm']
    rw [hcode]
    exact processMessageCall_withCode (Meter := Meter) (message := { message with reservoir })
      htarget c' start substate auths paid
  | none =>
    simp only [hto] at h h'
    cases h
    cases h'
    rfl

/-- A change of one account keeps the candidates when it makes none there. -/
theorem keepsCandidates_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ updated, f (tx.getAccount address) = .ok updated → updated.nonce = 0 →
      updated.codeHash = EMPTY_CODE_HASH →
      address ∈ tx.storageClears ∨
        ((tx.getAccount address).nonce = 0 ∧ (tx.getAccount address).codeHash = EMPTY_CODE_HASH))
    (h : tx.modifyState fork address f = .ok tx') : KeepsCandidates tx tx' := by
  have hclears : ∀ x, x ∈ tx.storageClears → x ∈ tx'.storageClears := by
    obtain ⟨updated, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
    intro x hx
    split
    · simp [TransactionState.destroyAccount, TransactionState.destroyStorage,
        TransactionState.setAccount, TransactionState.recordAccountRead, hx]
    · exact hx
  obtain ⟨updated, hupd, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  refine ⟨TransactionState.parent_modifyState h, hclears, fun x hn hc => ?_⟩
  by_cases hx : x = address
  · subst hx
    rw [hself] at hn hc
    exact (hf updated hupd hn hc).imp_left (hclears x)
  · rw [hother x hx] at hn hc
    exact .inr ⟨hn, hc⟩

/-- A rise of a nonce keeps the candidates. -/
theorem keepsCandidates_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : KeepsCandidates tx tx' :=
  keepsCandidates_modifyState (fun _ hupd hn _ => by
    cases hupd; exact absurd hn (Nat.succ_ne_zero _)) h

end Copies

/-! ## The message on agreeing states -/

/-- The message a transaction builds runs alike on two agreeing states, the first one's reads
in the sets: EthLib's `processMessageCall_agrees`, after swapping the second state's message
(which may hold other code for the recipient, which the run ignores) for the first's. -/
theorem message_agrees {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {fork : Fork}
    {block : BlockState} {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} (covers : CoversBlock block account allStorage code)
    {st1 st2 : TransactionState} (hagree : TransactionState.AgreesOn account allStorage slot code st1 st2)
    (hparent : st1.parent = block) (horigin : CodeOrigin block st1)
    (hcand : TransactionState.NoNewCandidate block st1)
    {env : BlockEnvironment fork} {txEnv : TransactionEnvironment fork} {sender target : Address}
    {gas : Nat} {t : Transaction} {m1 m2 : Message fork}
    (hm1 : transactionMessage env txEnv st1 sender target gas t = .ok m1)
    (hm2 : transactionMessage env txEnv st2 sender target gas t = .ok m2)
    (htarget : ∀ x, t.to = some x → x = target)
    (chainId reservoir : Nat) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) {o : CallOutput}
    (hrun : processMessageCall (Meter := Meter) chainId { m1 with reservoir } st1 substate auths paid
      = .ok o)
    (hreads : ReadsIn account slot o.state) :
    ∃ o', processMessageCall (Meter := Meter) chainId { m2 with reservoir } st2 substate auths paid
      = .ok o' ∧ o' = { o with state := o'.state } := by
  rw [processMessageCall_transactionMessage hm1 hm2]
  have hrecipient : ∀ x, ({ m1 with reservoir } : Message fork).target = some x →
      x = ({ m1 with reservoir } : Message fork).currentTarget := by
    intro x hx
    obtain ⟨hmt, hmc⟩ := target_transactionMessage hm1
    dsimp only at hx ⊢
    rw [hmc]
    rw [hmt] at hx
    exact htarget x hx
  obtain ⟨o', ho', hsame, -⟩ := processMessageCall_agrees covers hagree hparent horigin hcand
    hrecipient hrun hreads
  exact ⟨o', ho', hsame⟩

/-! ## `prepare`'s tail on two incremented states -/

private theorem mapError_ne_error {α : Type} {f : EvmError → PrepareStop} {e : PrepareStop}
    (hf : ∀ x, f x ≠ e) (tm : Except EvmError α) : tm.mapError f ≠ .error e := by
  cases tm with
  | error x => exact fun h => hf x (Except.error.inj h)
  | ok _ => exact fun h => by cases h

private theorem mapError_ok' {ε ε' α : Type} (f : ε → ε') (x : α) :
    Except.mapError f (Except.ok x) = Except.ok x := rfl

/-- `prepareFrom` on two incremented states that agree, with the same sender's balance: when the
first prepares a call that runs, the second prepares one that runs to the same result. The
second state must hold the code of every account; the first's reads must be in the sets. -/
theorem prepareFrom_run {rules : LeanLightEvm.Activation} {chainId : Nat} {h : Header}
    {ancestors : Option (List Hash32)} {cap : Nat} {r : Request} {account : Account}
    {st1 st2 : TransactionState} {p : Prepared} {o : CallOutput}
    {block : BlockState} {accounts allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} (covers : CoversBlock block accounts allStorage code)
    (hagree : TransactionState.AgreesOn accounts allStorage slot code st1 st2)
    (hparent : st1.parent = block) (horigin : CodeOrigin block st1)
    (hcand : TransactionState.NoNewCandidate block st1)
    (hbal : st2.getAccount r.sender = st1.getAccount r.sender) (hcodes : HasCodes st2)
    (hp : prepareFrom rules chainId h ancestors cap r account (.ok st1) = .ok p)
    (hrun : p.run = .ok o) (hreads : ReadsIn accounts slot o.state) :
    ∃ p' o', prepareFrom rules chainId h ancestors cap r account (.ok st2) = .ok p' ∧
      p'.run = .ok o' ∧ p'.result o' = p.result o := by
  have hTM : ∀ {fork : Fork} (env : BlockEnvironment fork) (txEnv : TransactionEnvironment fork)
      (target : Address) (gas : Nat) (t : Transaction),
      transactionMessage env txEnv st2 r.sender target gas t =
        .ok (Classical.choose (exists_transactionMessage txEnv hcodes r.sender target gas t)) :=
    fun _ txEnv target gas t =>
      Classical.choose_spec (exists_transactionMessage txEnv hcodes r.sender target gas t)
  unfold prepareFrom at hp ⊢
  simp only [bind, Except.bind, pure, Except.pure, mapError_ok', hbal] at hp ⊢
  repeat' (first
    | (cases hp; done)
    | (rename_i heq; simp only [heq, ↓reduceIte] at ⊢)
    | split at hp)
  all_goals
    rename_i m1 hm1
    rename_i target hmt _ _ _ _ _ _ _ _
    cases hp
    have hm1' := EthLib.Base.mapError_ok_iff.mp hm1
    have htarget : ∀ x, r.to = some x → x = target := by
      intro x hx
      have := EthLib.Base.mapError_ok_iff.mp hmt
      unfold messageTarget at this
      simp only [hx] at this
      exact Except.ok.inj this
    split
    · rename_i e he
      rw [hTM] at he
      cases he
    rename_i m2 hm2
    have hm2' := EthLib.Base.mapError_ok_iff.mp hm2
    have hct1 := (target_transactionMessage hm1').2
    have hct2 := (target_transactionMessage hm2').2
    unfold Prepared.run at hrun
    dsimp only at hrun
    by_cases hg : rules.fork ≥ .glamsterdam
    · simp only [hg, ↓reduceIte] at hrun
      obtain ⟨o', ho', hsame⟩ := message_agrees (Meter := StateGasMeter) covers hagree hparent
        horigin hcand hm1' hm2' htarget _ _ _ _ _ hrun hreads
      refine ⟨_, o', rfl, ?_, ?_⟩
      · unfold Prepared.run
        dsimp only
        simp only [hg, ↓reduceIte]
        simp only [hct1, hct2] at ho' ⊢
        exact ho'
      · rw [hsame]
        rfl
    · simp only [hg, ↓reduceIte] at hrun
      obtain ⟨o', ho', hsame⟩ := message_agrees (Meter := Nat) covers hagree hparent
        horigin hcand hm1' hm2' htarget _ _ _ _ _ hrun hreads
      refine ⟨_, o', rfl, ?_, ?_⟩
      · unfold Prepared.run
        dsimp only
        simp only [hg, ↓reduceIte]
        simp only [hct1, hct2] at ho' ⊢
        exact ho'
      · rw [hsame]
        rfl

/-- `prepareFrom` refuses alike on two incremented states that both fail alike, or that both
succeed with the same sender's balance: a refusal comes before the message is built. -/
theorem prepareFrom_refused {rules : LeanLightEvm.Activation} {chainId : Nat} {h : Header}
    {ancestors ancestors' : Option (List Hash32)} {cap : Nat} {r : Request} {account : Account}
    {inc1 inc2 : Except StateError TransactionState}
    (hinc : (∃ e, inc1 = .error e ∧ inc2 = .error e) ∨
      ∃ st1 st2, inc1 = .ok st1 ∧ inc2 = .ok st2 ∧
        st2.getAccount r.sender = st1.getAccount r.sender)
    {why : Refusal}
    (hp : prepareFrom rules chainId h ancestors cap r account inc1 = .error (.refused why)) :
    prepareFrom rules chainId h ancestors' cap r account inc2 = .error (.refused why) := by
  have hgas : ∀ hashes, (environment rules.fork rules.blobSchedule chainId h hashes).gasLimit =
      h.gasLimit := fun _ => rfl
  rcases hinc with ⟨e, rfl, rfl⟩ | ⟨st1, st2, rfl, rfl, hbal⟩
  · unfold prepareFrom at hp ⊢
    simp only [bind, Except.bind, pure, Except.pure, hgas] at hp ⊢
    repeat' (first
      | (cases hp; done)
      | (cases hp; rfl)
      | (rename_i heq; simp only [heq, ↓reduceIte] at ⊢)
      | split at hp)
  unfold prepareFrom at hp ⊢
  simp only [bind, Except.bind, pure, Except.pure, mapError_ok', hbal, hgas] at hp ⊢
  repeat' (first
    | (cases hp; done)
    | (cases hp; rfl)
    | (rename_i heq; simp only [heq, ↓reduceIte] at ⊢)
    | split at hp)
  all_goals
    cases hp
    rename_i hx
    exact absurd hx (mapError_ne_error (fun x hx' => by
      split at hx' <;> cases hx') _)

/-- With the held hashes given as the ancestors, `blockHashes` gives them back. -/
theorem blockHashes_held (h : Header) (ancestors : Option (List Hash32)) :
    blockHashes h (some (blockHashes h ancestors)) = blockHashes h ancestors := by
  unfold blockHashes
  cases ancestors with
  | none => simp
  | some hs =>
    by_cases he : hs.isEmpty <;> simp [he]

/-- `prepare` with the hashes `call` holds given as the full list is `prepare` with `call`'s
ancestors. -/
theorem prepare_held (rules : LeanLightEvm.Activation) (chainId : Nat) (h : Header)
    (ancestors : Option (List Hash32)) (cap : Nat) (r : Request) (S : State) :
    prepare rules chainId h (some (blockHashes h ancestors)) cap r S =
      prepare rules chainId h ancestors cap r S := by
  unfold prepare
  rw [blockHashes_held]

end LeanLightEvmProofs
