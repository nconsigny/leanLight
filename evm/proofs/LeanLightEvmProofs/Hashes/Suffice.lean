import LeanLightEvmProofs.Hashes.Call

/-!
# `HashesSuffice`, and `CallAgrees` in full

`LeanLightEvm.record` notes every block number BLOCKHASH asks for within the 256-block window
(`record_blockhash`), and its notes only grow (`record_mono`). So when every noted number is
within the hashes `call` held (R5), every BLOCKHASH of the run is answered alike by the held
hashes and the chain's full list, of which they are a suffix (`blockHash_suffix`, G1;
`safe_of_notes`). `prepare` with the full list prepares the same call with those hashes
(`prepare_withHashes`, G3), and `processMessageCall_withHashes` gives its run. Hence
`hashesSuffice`, and with `call_agrees_of_hashesSuffice`, `call_agrees`: `CallAgrees` as
`Call.lean` states it.
-/

namespace LeanLightEvmProofs.Hashes

open EthLib.Base (Fork U256 Hash32 Address)
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions
open LeanLightEvm

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- G1. Two hash lists, the held one a suffix of the full one, answer `BLOCKHASH` alike on every
block number whose distance from `current` is at most the held list's length. -/
theorem blockHash_suffix {held full : List Hash32} (h : held.IsSuffix full) {current n : Nat}
    (hn : current - n ≤ held.length) : blockHash held current n = blockHash full current n := by
  unfold blockHash
  split
  · rename_i hw
    have hpre : held.reverse <+: full.reverse := List.reverse_prefix.mpr h
    have hi : current - n - 1 < held.reverse.length := by
      rw [List.length_reverse]; omega
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, List.getElem?_append_left hi]
  · rfl

/-- The notes only grow. -/
theorem record_mono (f : Facts) (number : Nat) (e : Evm fork Meter)
    (r : Except EvmError (StepResult fork Meter)) (n : Notes) (b : Nat)
    (hb : b ∈ n.blockNumbers) : b ∈ (record f number e r n).blockNumbers := by
  unfold record
  repeat' split
  all_goals (try dsimp only)
  all_goals (repeat' split)
  all_goals first
    | exact hb
    | exact Std.ExtTreeSet.mem_insert.mpr (.inr hb)


set_option maxHeartbeats 1000000 in
/-- A BLOCKHASH within the window is noted. -/
theorem record_blockhash (f : Facts) (number : Nat) (e : Evm fork Meter)
    (r : Except EvmError (StepResult fork Meter)) (n : Notes)
    (hpc : e.pc < e.code.size) (hop : e.code[e.pc] = 0x40) {w : U256} {rest : List U256}
    (hst : e.stack.val = w :: rest) (hwin : w.toNat < number ∧ number ≤ w.toNat + 256) :
    w.toNat ∈ (record f number e r n).blockNumbers := by
  obtain ⟨pc, ⟨vals, hl⟩, memory, code, v, gas, running, message, output, returnData, state,
    substate, error⟩ := e
  dsimp only at hst hpc hop
  subst hst
  unfold record
  repeat' split
  all_goals (try dsimp only)
  all_goals (repeat' split)
  all_goals first
    | exact Std.ExtTreeSet.mem_insert_self
    | contradiction
    | (obtain ⟨⟩ := ‹w :: rest = _ :: _›
       first | exact Std.ExtTreeSet.mem_insert_self | contradiction)
    | (obtain ⟨⟩ := ‹w :: rest = []›)


/-- The observer's guarantee: a final state whose noted numbers are all within the held hashes
gives, at every step of a frame of the block `E`, a BLOCKHASH the full list answers alike. -/
theorem safe_of_notes (f : Facts) {E : BlockEnvironment fork} {full : List Hash32}
    (hsuf : E.blockHashes.IsSuffix full) (e : Evm fork Meter) (s : Notes)
    (hE : e.message.blockEnv = E) (N : Nat) (hN : E.number = N)
    (hP : ∀ b ∈ (record f N e (step fork e) s).blockNumbers,
      E.number - b ≤ E.blockHashes.length) :
    BlockhashAgrees full e := by
  intro hpc hop w rest hst
  have h40 : e.code[e.pc] = 0x40 := by
    have := (Op.ofByte_eq_some_iff.mp hop).1
    rw [← this]; rfl
  rw [hE]
  by_cases hwin : w.toNat < E.number ∧ E.number ≤ w.toNat + 256
  · have hb := record_blockhash f N e (step fork e) s hpc h40 hst (hN ▸ hwin)
    exact (blockHash_suffix hsuf (hP _ hb)).symm
  · unfold blockHash
    rw [if_neg hwin, if_neg hwin]

/-- The prepared call with the hashes `hs` in its block and message. -/
def preparedWithHashes (hs : List Hash32) (p : Prepared) : Prepared :=
  { p with env := { p.env with blockHashes := hs }, message := Message.withHashes hs p.message }

theorem transactionMessage_env {fork : Fork} (blobs : _) (chainId : Nat) (h : Header)
    (X Y : List Hash32) (txEnv : TransactionEnvironment fork) (st : TransactionState)
    (sender target : Address) (gas : Nat) (tx : Transaction) :
    transactionMessage (environment fork blobs chainId h Y) txEnv st sender target gas tx =
      Message.withHashes Y <$>
        transactionMessage (environment fork blobs chainId h X) txEnv st sender target gas tx := by
  unfold transactionMessage
  split
  · simp only [Functor.map_map]
    cases Except.mapError _ _ <;> rfl
  · rfl

theorem mapError_map {ε ε' α β : Type} (g : α → β) (f : ε → ε') (x : Except ε α) :
    (g <$> x).mapError f = g <$> x.mapError f := by
  cases x <;> rfl

/-- G3. `prepare` with other ancestors prepares the same call, with their hashes. -/
theorem prepare_withHashes (rules : LeanLightEvm.Activation) (chainId : Nat) (h : Header)
    (a a' : Option (List Hash32)) (cap : Nat) (r : Request) (S : EthLib.Execution.State.State) :
    prepare rules chainId h a' cap r S =
      preparedWithHashes (blockHashes h a') <$> prepare rules chainId h a cap r S := by
  unfold prepare
  simp only [transactionMessage_env _ _ _ (blockHashes h a) (blockHashes h a'), mapError_map,
    bind_map_left, map_bind, map_pure, map_ite_except]
  repeat' (first
    | rfl
    | refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
    | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
    | (split <;> (try simp only [bind_map_left, map_bind, map_pure, map_ite_except])))


theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {v : α}
    (h : x.mapError f = .ok v) : x = .ok v := by
  cases x <;> simp_all [Except.mapError]

theorem transactionMessage_blockEnv {fork : Fork}
    {env : BlockEnvironment fork} {txEnv : TransactionEnvironment fork} {st : TransactionState}
    {sender target : Address} {gas : Nat} {tx : Transaction} {m : Message fork}
    (h : transactionMessage env txEnv st sender target gas tx = .ok m) :
    m.blockEnv = env := by
  unfold transactionMessage at h
  split at h
  · cases hc : (Except.mapError EvmError.state
        (st.getCode (st.getAccount _).codeHash)) with
    | error e => rw [hc] at h; cases h
    | ok c => rw [hc] at h; cases h; rfl
  · cases h; rfl

/-- What `prepare` puts in the block and the message. -/
theorem prepare_env {rules : LeanLightEvm.Activation} {chainId : Nat} {h : Header}
    {a : Option (List Hash32)} {cap : Nat} {r : Request} {S : EthLib.Execution.State.State}
    {p : Prepared} (hp : prepare rules chainId h a cap r S = .ok p) :
    p.env.number = h.number ∧ p.env.blockHashes = blockHashes h a ∧ p.message.blockEnv = p.env := by
  unfold prepare at hp
  simp only [bind, Except.bind, pure, Except.pure] at hp
  repeat' (first | (cases hp; done) | split at hp)
  all_goals first
    | (cases hp; rename_i heq; refine ⟨rfl, rfl, ?_⟩; have h2 := mapError_ok heq
       dsimp only
       exact transactionMessage_blockEnv h2)


/-- **`HashesSuffice` holds** (`CallAgrees.lean`): on the facts' state, the plain run of a call
prepared with all of the chain's ancestors ends as the run `call` observed with the hashes it
held, whenever every BLOCKHASH number the observer noted is within those hashes (R5). -/
theorem hashesSuffice : LeanLightEvmProofs.HashesSuffice := by
  intro b i full rules p o notes hanc hp hobs hR5
  obtain ⟨-, hlast, hsuf⟩ := hanc
  have hfull : blockHashes i.header (some full) = full := by
    have hne : full ≠ [] := by
      rintro rfl
      simp at hlast
    unfold blockHashes
    simp [hne]
  have hp' := prepare_withHashes rules i.chainId i.header i.ancestors (some full)
    b.executionGas i.request i.facts.toState
  rw [hp] at hp'
  refine ⟨preparedWithHashes (blockHashes i.header (some full)) p, by rw [hp']; rfl, ?_, rfl⟩
  obtain ⟨hnum, hhash, hmsg⟩ := prepare_env hp
  have hsufY : p.env.blockHashes.IsSuffix (blockHashes i.header (some full)) := by
    rw [hhash, hfull]; exact hsuf
  have hP : ∀ n ∈ notes.blockNumbers, p.env.number - n ≤ p.env.blockHashes.length := by
    rw [hnum, hhash]; exact hR5
  have back : ∀ {Meter : Type} [GasMeter Meter] (e : Evm p.fork Meter)
      (r : Except EvmError (StepResult p.fork Meter)) (s : Notes),
      (∀ n ∈ (record i.facts i.header.number e r s).blockNumbers,
        p.env.number - n ≤ p.env.blockHashes.length) →
      ∀ n ∈ s.blockNumbers, p.env.number - n ≤ p.env.blockHashes.length :=
    fun e r s hPs n hn => hPs n (record_mono i.facts i.header.number e r s n hn)
  have safe : ∀ {Meter : Type} [GasMeter Meter] (e : Evm p.fork Meter) (s : Notes),
      e.message.blockEnv = p.env → e.running = true →
      (∀ n ∈ (record i.facts i.header.number e (step p.fork e) s).blockNumbers,
        p.env.number - n ≤ p.env.blockHashes.length) →
      BlockhashAgrees (blockHashes i.header (some full)) e := by
    intro Meter _ e s hE _ hPs
    exact safe_of_notes i.facts hsufY e s hE _ hnum hPs
  unfold Prepared.runObserved at hobs
  unfold Prepared.run
  split at hobs <;> rename_i hf <;> split <;> rename_i hf'
  · exact processMessageCall_withHashes _ p.env (record i.facts i.header.number)
      (fun n => ∀ b ∈ n.blockNumbers, p.env.number - b ≤ p.env.blockHashes.length)
      (fun e r s => back e r s) (fun e s => safe e s) _ _ _ _ _ _ {} o notes hmsg hobs hP
  · exact absurd hf hf'
  · exact absurd hf' hf
  · exact processMessageCall_withHashes _ p.env (record i.facts i.header.number)
      (fun n => ∀ b ∈ n.blockNumbers, p.env.number - b ≤ p.env.blockHashes.length)
      (fun e r s => back e r s) (fun e s => safe e s) _ _ _ _ _ _ {} o notes hmsg hobs hP

end LeanLightEvmProofs.Hashes

namespace LeanLightEvmProofs

/-- **`CallAgrees`, proved** (`evm/LeanLightEvm/Call.lean`): for any budgets and input, an
answer of `call` is `reference`'s result (success flag, output, error, gas used, refund and
logs) on every state `F` in which the facts hold, whose storage sits at existing accounts and
which holds every account's code, with the chain's full ancestor list; a refusal of `call` is
`reference`'s. What the statement leaves out is `CallAgrees`' docstring's list (that `F` is the
chain's state, `prepare` against EthLib's `prepareCall`, the answer's other fields). -/
theorem call_agrees : LeanLightEvm.CallAgrees :=
  call_agrees_of_hashesSuffice Hashes.hashesSuffice

end LeanLightEvmProofs
