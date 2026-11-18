import LeanLightEvmProofs.Call

/-!
# `call` agrees with the plain run on every full state the facts hold in

`call_answers_held`: an answer of `call` is what `reference` gives on every full state `F` the
facts hold in (`Facts.HoldIn`), with storage only at existing accounts and every code, when
`reference` is given the block hashes `call` held. `call_refuses`: a refusal of `call` is
`reference`'s, whatever ancestors it is given. `call_agrees_of_hashesSuffice`: `CallAgrees` as
`Call.lean` states it, from `HashesSuffice` (below), which `LeanLightEvmProofs/Hashes` proves
(`hashesSuffice`, and `call_agrees` in full).
`call_agrees_of_all_held`: `CallAgrees`'s conclusion without `HashesSuffice` for an input that
holds all `min 256 number` ancestors.
-/

namespace LeanLightEvmProofs

open LeanLightEvm
open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.Evm
open EthLib.Execution.Transactions

/-! ## The input checks -/

theorem checkInput_ok {b : Budgets} {i : Input} {rules : LeanLightEvm.Activation}
    (h : checkInput b i = .ok rules) :
    rulesAt i.table i.chainId i.header.timestamp = .ok rules ∧ i.facts.check = .ok () := by
  unfold checkInput at h
  by_cases h1 : b.rounds ≤ i.round
  · simp only [h1, ↓reduceIte] at h
    cases h
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : maxExecutionGas < b.executionGas
  · simp only [h2, ↓reduceIte] at h
    cases h
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : maxRequestData < i.request.data.size
  · simp only [h3, ↓reduceIte] at h
    cases h
  simp only [h3, ↓reduceIte] at h
  cases hr : rulesAt i.table i.chainId i.header.timestamp with
  | error e =>
    simp only [hr, Except.mapError, bind, Except.bind] at h
    cases h
  | ok rules' =>
  cases hc : i.facts.check with
  | error e =>
    simp only [hr, hc, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      at h
    repeat' (first | (cases h; done) | split at h)
  | ok u =>
    simp only [hr, hc, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      pure] at h
    repeat' (first | (cases h; done) | split at h)
    all_goals (cases h; exact ⟨rfl, rfl⟩)

/-- `CodesAvailable` is EthLib's `HasCodes` of the state with no write. -/
theorem hasCodes_of_codesAvailable {F : State} (h : CodesAvailable F) :
    HasCodes (TransactionState.ofBlock (blockOf F)) := by
  intro a
  obtain ⟨c, hc⟩ := h a
  refine ⟨c, ?_⟩
  rw [getCode_blockOf, getAccount_blockOf]
  exact hc

/-! ## A refusal -/

/-- What `call` checked before it refused. -/
private theorem refused_inv {b : Budgets} {i : Input} {why : Refusal}
    (h : call b i = .refused why) :
    ∃ rules, checkInput b i = .ok rules ∧
      i.facts.accounts.contains i.request.sender = true ∧
      prepare rules i.chainId i.header i.ancestors b.executionGas i.request i.facts.toState =
        .error (.refused why) := by
  unfold call at h
  split at h
  · cases h
  rename_i rules hin
  dsimp only at h
  split at h
  · cases h
  rename_i hmissing
  have hsender : i.facts.accounts.contains i.request.sender = true := by
    have hm : ((i.request.sender :: i.request.to.toList).filter
        fun a => !i.facts.accounts.contains a).isEmpty = true := by simpa using hmissing
    rw [List.isEmpty_iff, List.filter_eq_nil_iff] at hm
    simpa using hm i.request.sender (List.mem_cons_self ..)
  split at h
  · rename_i w hp
    cases h
    exact ⟨rules, hin, hsender, hp⟩
  all_goals
    repeat' split at h
    all_goals cases h

/-- The sender's account and the result of its nonce increment, on the facts' state and on a
full state the facts hold in, when the sender is among the facts. -/
private theorem sender_agrees {f : Facts} {F : State} (hF : f.HoldIn F) {sender : Address}
    (hs : f.accounts.contains sender = true) (fork : Fork) :
    (TransactionState.ofBlock (blockOf F)).getAccount sender =
        (TransactionState.ofBlock (blockOf f.toState)).getAccount sender ∧
      EthLib.Base.ExceptRel (TransactionState.AgreesOn (· = sender) (fun _ => False)
        (fun _ _ => False) (fun _ => False))
        ((TransactionState.ofBlock (blockOf f.toState)).incrementNonce fork sender)
        ((TransactionState.ofBlock (blockOf F)).incrementNonce fork sender) := by
  have hblock : BlockState.AgreesOn (· = sender) (fun _ => False) (fun _ _ => False)
      (fun _ => False) (blockOf f.toState) (blockOf F) := by
    refine ⟨fun a ha => ?_, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim⟩
    subst ha
    rw [getAccountOptional_blockOf, getAccountOptional_blockOf, accounts_toState]
    rw [Std.ExtTreeMap.contains_iff_mem, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hs
    cases hfact : f.accounts[a]? with
    | none => rw [hfact] at hs; cases hs
    | some fact =>
      have := hF.accounts a fact hfact
      cases fact with
      | absent => exact this
      | present => exact this
  have htx := TransactionState.AgreesOn.ofBlock hblock
  exact ⟨htx.getAccount_eq (.inr rfl), htx.incrementNonce fork (.inr rfl)⟩

/-- **A refusal of `call` is the plain run's.** If `call` refuses a request, `reference` refuses
it for the same reason on every full state the facts hold in, whatever ancestors it is given:
the refusal is decided on the sender's account, which is a fact, before any message is built. -/
theorem call_refuses {b : Budgets} {i : Input} {F : State} (full : List Hash32)
    (hF : i.facts.HoldIn F) {why : Refusal} (h : call b i = .refused why) :
    reference b i full F = some (.error why) := by
  obtain ⟨rules, hin, hsender, hp⟩ := refused_inv h
  obtain ⟨hrules, -⟩ := checkInput_ok hin
  obtain ⟨hacc, hinc⟩ := sender_agrees hF hsender rules.fork
  unfold reference
  rw [hrules]
  dsimp only
  rw [prepare_eq] at hp
  rw [prepare_eq, hacc]
  have hinc' : (∃ e, (TransactionState.ofBlock (blockOf i.facts.toState)).incrementNonce
        rules.fork i.request.sender = .error e ∧
        (TransactionState.ofBlock (blockOf F)).incrementNonce rules.fork i.request.sender =
          .error e) ∨
      ∃ st1 st2, (TransactionState.ofBlock (blockOf i.facts.toState)).incrementNonce
        rules.fork i.request.sender = .ok st1 ∧
        (TransactionState.ofBlock (blockOf F)).incrementNonce rules.fork i.request.sender =
          .ok st2 ∧ st2.getAccount i.request.sender = st1.getAccount i.request.sender := by
    revert hinc
    cases (TransactionState.ofBlock (blockOf i.facts.toState)).incrementNonce rules.fork
      i.request.sender <;>
    cases (TransactionState.ofBlock (blockOf F)).incrementNonce rules.fork i.request.sender
    · intro he
      exact .inl ⟨_, rfl, by rw [show _ = _ from he]⟩
    · intro he; exact he.elim
    · intro he; exact he.elim
    · intro he
      exact .inr ⟨_, _, rfl, rfl, he.getAccount_eq (.inr rfl)⟩
  rw [prepareFrom_refused hinc' hp]

/-! ## An answer -/

/-- The run `call` observed is the plain run. -/
theorem run_of_runObserved {p : Prepared} {f : Facts} {number : Nat} {o : CallOutput}
    {notes : Notes} (h : p.runObserved f number = .ok (o, notes)) : p.run = .ok o := by
  unfold Prepared.runObserved at h
  unfold Prepared.run
  dsimp only at h ⊢
  by_cases hg : p.fork ≥ .glamsterdam
  · simp only [hg, ↓reduceIte] at h ⊢
    rw [← processMessageCallWith_modify (fun evm res => record f number evm res) _ _ _ _ _ _
      ({} : Notes)]
    simp only [StateT.run] at h
    rw [h]
    rfl
  · simp only [hg, ↓reduceIte] at h ⊢
    rw [← processMessageCallWith_modify (fun evm res => record f number evm res) _ _ _ _ _ _
      ({} : Notes)]
    simp only [StateT.run] at h
    rw [h]
    rfl

/-- An increment that succeeds on a state with no write keeps the block, the origin of every
code hash and the deployment candidates. -/
private theorem incremented_invariants {S : State} {fork : Fork} {sender : Address}
    {st : TransactionState}
    (h : (TransactionState.ofBlock (blockOf S)).incrementNonce fork sender = .ok st) :
    st.parent = blockOf S ∧ CodeOrigin (blockOf S) st ∧
      TransactionState.NoNewCandidate (blockOf S) st :=
  ⟨TransactionState.parent_incrementNonce h,
    (CodeOrigin.ofBlock _).of_keepsCodeOrigin (KeepsCodeOrigin.incrementNonce h),
    (TransactionState.NoNewCandidate.ofBlock _).of_keepsCandidates
      (keepsCandidates_incrementNonce h)⟩

private theorem prepareFrom_error {rules : LeanLightEvm.Activation} {chainId : Nat} {h : Header}
    {ancestors : Option (List Hash32)} {cap : Nat} {r : Request} {account : Account}
    {e : StateError} {p : Prepared}
    (hp : prepareFrom rules chainId h ancestors cap r account (.error e) = .ok p) : False := by
  unfold prepareFrom at hp
  simp only [bind, Except.bind, pure, Except.pure] at hp
  repeat' (first | (cases hp; done) | split at hp)

/-- **An answer of `call` is the plain run's, with the hashes `call` held.** If `call` answers
`a`, then on every full state `F` in which the facts hold (`Facts.HoldIn`, which includes that an
account whose proved storage root is the empty root has no slot in `F`), whose storage sits at
existing accounts (`StorageAtAccounts`) and which holds every account's code
(`CodesAvailable`), `reference` given the block hashes `call` held
(`blockHashes i.header i.ancestors`) gives `a.result`: the same success flag, output, error, gas
used, refund and logs. With all of the chain's ancestors instead, see `HashesSuffice`. -/
theorem call_answers_held {b : Budgets} {i : Input} {F : State} (hstor : StorageAtAccounts F)
    (hcodes : CodesAvailable F) (hF : i.facts.HoldIn F) {a : Answer}
    (h : call b i = .answer a) :
    reference b i (blockHashes i.header i.ancestors) F = some (.ok a.result) := by
  obtain ⟨⟨rules, p, o, notes, hin, hsender, -, hp, hran, hc, hn, hres⟩⟩ := answered h
  obtain ⟨hrules, hcheck⟩ := checkInput_ok hin
  have hrun := run_of_runObserved hran
  obtain ⟨haccChecked, hslots, -⟩ := checkRun_sound hc hn
  -- the sets, and the block states' agreement on them
  have hblock := agrees_of_checks hcheck hF hstor haccChecked hslots
  have hsenderIn : (sets i.request o i.facts.toState).account i.request.sender :=
    mem_accessedAccounts.mpr (.inl rfl)
  have htx := TransactionState.AgreesOn.ofBlock hblock
  have hacc := htx.getAccount_eq (.inr hsenderIn)
  have hinc := htx.incrementNonce rules.fork (.inr hsenderIn)
  rw [prepare_eq] at hp
  -- the increment succeeded on the facts' state, so on `F` too
  cases hst1 : (TransactionState.ofBlock (blockOf i.facts.toState)).incrementNonce rules.fork
      i.request.sender with
  | error e =>
    rw [hst1] at hp
    exact (prepareFrom_error hp).elim
  | ok st1 =>
    rw [hst1] at hp hinc
    cases hst2 : (TransactionState.ofBlock (blockOf F)).incrementNonce rules.fork
        i.request.sender with
    | error e => rw [hst2] at hinc; exact hinc.elim
    | ok st2 =>
      rw [hst2] at hinc
      obtain ⟨hparent, horigin, hcand⟩ := incremented_invariants hst1
      have covers : CoversBlock (blockOf i.facts.toState)
          (sets i.request o i.facts.toState).account (sets i.request o i.facts.toState).allStorage
          (sets i.request o i.facts.toState).code :=
        ⟨fun a ha => ⟨a, ha, rfl⟩, fun _ ha hn hcd => ⟨ha, hn, hcd⟩⟩
      have hreads : ReadsIn (sets i.request o i.facts.toState).account
          (sets i.request o i.facts.toState).slot o.state :=
        ⟨fun a ha => mem_accessedAccounts.mpr (.inr (.inr (.inl ha))), fun _ _ hk => .inl hk⟩
      obtain ⟨p', o', hp', hrun', hres'⟩ := prepareFrom_run covers hinc hparent horigin hcand
        (hinc.getAccount_eq (.inr hsenderIn))
        (hasCodes_incrementNonce hst2 (hasCodes_of_codesAvailable hcodes))
        hp hrun hreads
      unfold reference
      rw [hrules]
      dsimp only
      rw [prepare_held, prepare_eq, hacc, hst2, hp']
      dsimp only
      simp only [hrun', hres', hres]

/-! ## The ancestors `call` did not hold -/

/-- **The step proved in `LeanLightEvmProofs/Hashes`** (`hashesSuffice`). On the facts' state, the
plain run of a call prepared with all of the chain's ancestors (`full`, `AncestorsOf`) ends as the run `call` observed with
the hashes it held, when every `BLOCKHASH` the observer noted within the 256-block window asked
for a hash among those held (R5). It holds if EthLib's run reads `blockHashes` only through
`BLOCKHASH` (`Instructions/EnvironmentData.lean`, `blockHash`: the `k`-th hash from the end) and
the observer notes every `BLOCKHASH` step, in every frame, before it runs: both are proved there. -/
def HashesSuffice : Prop :=
  ∀ (b : Budgets) (i : Input) (full : List Hash32) (rules : LeanLightEvm.Activation) (p : Prepared)
    (o : CallOutput) (notes : Notes),
    AncestorsOf i full →
    prepare rules i.chainId i.header i.ancestors b.executionGas i.request i.facts.toState =
      .ok p →
    p.runObserved i.facts i.header.number = .ok (o, notes) →
    (∀ n ∈ notes.blockNumbers, i.header.number - n ≤ (blockHashes i.header i.ancestors).length) →
    ∃ p', prepare rules i.chainId i.header (some full) b.executionGas i.request
        i.facts.toState = .ok p' ∧ p'.run = .ok o ∧ p'.result o = p.result o

/-- **`CallAgrees` from `HashesSuffice`.** The statement `Call.lean` gives (`CallAgrees`), proved
from the agreement above and `HashesSuffice` (proved in `LeanLightEvmProofs/Hashes`: `call_agrees`). -/
theorem call_agrees_of_hashesSuffice (H : HashesSuffice) : CallAgrees := by
  intro b i F full hstor hcodes hF hanc
  refine ⟨fun a h => ?_, fun why h => call_refuses full hF h⟩
  obtain ⟨⟨rules, p, o, notes, hin, hsender, -, hp, hran, hc, hn, hres⟩⟩ := answered h
  obtain ⟨hrules, hcheck⟩ := checkInput_ok hin
  obtain ⟨haccChecked, hslots, hR5⟩ := checkRun_sound hc hn
  -- on the facts' state, the run with all ancestors ends as the observed one
  obtain ⟨pf, hpf, hrunf, hresf⟩ := H b i full rules p o notes hanc hp hran hR5
  have hblock := agrees_of_checks hcheck hF hstor haccChecked hslots
  have hsenderIn : (sets i.request o i.facts.toState).account i.request.sender :=
    mem_accessedAccounts.mpr (.inl rfl)
  have htx := TransactionState.AgreesOn.ofBlock hblock
  have hacc := htx.getAccount_eq (.inr hsenderIn)
  have hinc := htx.incrementNonce rules.fork (.inr hsenderIn)
  rw [prepare_eq] at hpf
  cases hst1 : (TransactionState.ofBlock (blockOf i.facts.toState)).incrementNonce rules.fork
      i.request.sender with
  | error e =>
    rw [hst1] at hpf
    exact (prepareFrom_error hpf).elim
  | ok st1 =>
    rw [hst1] at hpf hinc
    cases hst2 : (TransactionState.ofBlock (blockOf F)).incrementNonce rules.fork
        i.request.sender with
    | error e => rw [hst2] at hinc; exact hinc.elim
    | ok st2 =>
      rw [hst2] at hinc
      obtain ⟨hparent, horigin, hcand⟩ := incremented_invariants hst1
      have covers : CoversBlock (blockOf i.facts.toState)
          (sets i.request o i.facts.toState).account (sets i.request o i.facts.toState).allStorage
          (sets i.request o i.facts.toState).code :=
        ⟨fun a ha => ⟨a, ha, rfl⟩, fun _ ha hn hcd => ⟨ha, hn, hcd⟩⟩
      have hreads : ReadsIn (sets i.request o i.facts.toState).account
          (sets i.request o i.facts.toState).slot o.state :=
        ⟨fun a ha => mem_accessedAccounts.mpr (.inr (.inr (.inl ha))), fun _ _ hk => .inl hk⟩
      obtain ⟨p', o', hp', hrun', hres'⟩ := prepareFrom_run covers hinc hparent horigin hcand
        (hinc.getAccount_eq (.inr hsenderIn))
        (hasCodes_incrementNonce hst2 (hasCodes_of_codesAvailable hcodes))
        hpf hrunf hreads
      unfold reference
      rw [hrules]
      dsimp only
      rw [prepare_eq, hacc, hst2, hp']
      dsimp only
      simp only [hrun', hres', hresf, hres]

/-! ## When `call` held every ancestor -/

/-- **`CallAgrees`'s conclusion, without `HashesSuffice`, when the input holds every ancestor.**
For an input whose held hashes (`blockHashes header ancestors`) number `min 256 number`, that
is, all the ancestors `BLOCKHASH` can name, `CallAgrees`'s two halves hold for that input, on
every `F` and `full` its hypotheses allow: `AncestorsOf` makes the held list a suffix of `full`
of the same length, so the two are equal and `call_answers_held` applies. Found in review
(review-agrees-statement-and-audit, 2026-11-17). -/
theorem call_agrees_of_all_held {b : Budgets} {i : Input} {F : State} {full : List Hash32}
    (hstor : StorageAtAccounts F) (hcodes : CodesAvailable F) (hF : i.facts.HoldIn F)
    (hanc : AncestorsOf i full)
    (hall : (blockHashes i.header i.ancestors).length = min 256 i.header.number) :
    (∀ a, call b i = .answer a → reference b i full F = some (.ok a.result)) ∧
      (∀ r, call b i = .refused r → reference b i full F = some (.error r)) := by
  obtain ⟨hlen, -, hsuf⟩ := hanc
  have heq : blockHashes i.header i.ancestors = full :=
    hsuf.eq_of_length (by rw [hall, hlen])
  refine ⟨fun a h => ?_, fun r h => call_refuses full hF h⟩
  rw [← heq]
  exact call_answers_held hstor hcodes hF h

end LeanLightEvmProofs
