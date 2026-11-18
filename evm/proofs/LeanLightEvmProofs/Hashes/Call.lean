import LeanLightEvmProofs.Hashes.Lift

/-!
# The block hashes, over the message of a transaction (`HashesSuffice`)

`prepareFirstFrame` with the hashes `hs` in the message prepares the same first frame with them
(`prepareFirstFrame_withHashes`), whose message runs in the transaction's block
(`prepareFirstFrame_blockEnv`); hence `processMessageCall_withHashes`.
-/

namespace LeanLightEvmProofs.Hashes

open EthLib.Base (Fork U256 Hash32 Address)
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {σ : Type}

/-- The first frame with the hashes `hs` in its message. -/
def FirstFrame.withHashes (hs : List Hash32) (f : FirstFrame fork Meter) : FirstFrame fork Meter :=
  ⟨Message.withHashes hs f.message, f.state, f.substate, f.refund, f.meter, f.held⟩

theorem map_ite_except {ε α β : Type} (g : α → β) (c : Prop) [Decidable c]
    (a b : Except ε α) :
    (g <$> if c then a else b) = if c then g <$> a else g <$> b := by
  split <;> rfl

omit [LawfulGasMeter Meter] in
theorem prepareFirstFrame_withHashes (hs : List Hash32) (chainId : Nat) (m : Message fork)
    (st : TransactionState) (sub : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) :
    prepareFirstFrame (Meter := Meter) chainId (Message.withHashes hs m) st sub auths paid =
      FirstFrame.withHashes hs <$> prepareFirstFrame chainId m st sub auths paid := by
  unfold prepareFirstFrame
  simp only [mwh_gas, mwh_reservoir, mwh_target, mwh_currentTarget, mwh_value]
  split
  all_goals
    simp only [bind_map_left, map_bind, map_pure, map_ite_except]
    repeat' (first
      | rfl
      | refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
      | (split <;> (try simp only [bind_map_left, map_bind, map_pure, map_ite_except])))

omit [LawfulGasMeter Meter] in
theorem prepareFirstFrame_blockEnv' (chainId : Nat) (m : Message fork)
    (st : TransactionState) (sub : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) :
    (fun f : FirstFrame fork Meter => f.message.blockEnv) <$>
        prepareFirstFrame chainId m st sub auths paid =
      (fun _ => m.blockEnv) <$> prepareFirstFrame (Meter := Meter) chainId m st sub auths paid := by
  unfold prepareFirstFrame
  split
  all_goals
    simp only [bind_map_left, map_bind, map_pure, map_ite_except]
    repeat' (first
      | rfl
      | refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
      | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
      | (split <;> (try simp only [bind_map_left, map_bind, map_pure, map_ite_except])))

omit [LawfulGasMeter Meter] in
/-- The first frame of a message runs in the message's block. -/
theorem prepareFirstFrame_blockEnv {chainId : Nat} {m : Message fork}
    {st : TransactionState} {sub : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId m st sub auths paid = .ok first) :
    first.message.blockEnv = m.blockEnv := by
  have key := prepareFirstFrame_blockEnv' (Meter := Meter) chainId m st sub auths paid
  rw [h] at key
  simpa [Functor.map, Except.map] using key

/-- **The message of a transaction.** If the observed run of the message `m` (of the block `E`)
ends in `o` with a final state in `P`, the plain run of `m` with the hashes `hs` ends in `o`. -/
theorem processMessageCall_withHashes (hs : List Hash32) (E : BlockEnvironment fork)
    (rec : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ) (P : σ → Prop)
    (back : ∀ e r s, P (rec e r s) → P s)
    (safe : ∀ e s, e.message.blockEnv = E → e.running = true → P (rec e (step fork e) s) →
      BlockhashAgrees hs e)
    (chainId : Nat) (m : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization) (paid : Std.ExtTreeSet Address) (s : σ) (o : CallOutput) (s' : σ)
    (hE : m.blockEnv = E)
    (h : processMessageCallWith (Meter := Meter) (M := StateT σ (Except EvmError))
      (fun evm result => modify (rec evm result)) chainId m state substate auths paid s =
        .ok (o, s'))
    (hP : P s') :
    processMessageCall (Meter := Meter) chainId (Message.withHashes hs m) state substate auths
      paid = .ok o := by
  unfold processMessageCallWith at h
  unfold processMessageCall processMessageCallWith
  rw [prepareFirstFrame_withHashes]
  cases hpf : prepareFirstFrame (Meter := Meter) chainId m state substate auths paid with
  | error er =>
    obtain ⟨e, read⟩ := er
    simp only [hpf] at h
    simp only [Functor.map, Except.map]
    by_cases ha : e.aborts = true
    · simp [ha, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [ha, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, mwh_reservoir]
  | ok first =>
    simp only [hpf] at h
    simp only [Functor.map, Except.map, mwh_target]
    have hfE : first.message.blockEnv = E := (prepareFirstFrame_blockEnv hpf).trans hE
    cases ht : m.target with
    | none =>
      simp only [ht] at h
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at h
      cases hc : processCreateMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (rec evm result)) first.message first.state first.substate
          first.meter first.held s with
      | error err => rw [hc] at h; cases h
      | ok r =>
        rw [hc] at h
        obtain ⟨⟨evm, used⟩, s1⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, hrun⟩ := (process_withHashes hs E rec P back safe _ first.message rfl hfE).2
          _ _ _ _ _ _ _ hc hP
        simp only [processCreateMessage] at hrun
        simp only [bind, Except.bind, pure, Except.pure]
        erw [hrun]
        rfl
    | some target =>
      simp only [ht] at h
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at h
      cases hc : processMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (rec evm result)) first.message first.state first.substate
          first.meter first.held s with
      | error err => rw [hc] at h; cases h
      | ok r =>
        rw [hc] at h
        obtain ⟨⟨evm, used⟩, s1⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, hrun⟩ := (process_withHashes hs E rec P back safe _ first.message rfl hfE).1
          _ _ _ _ _ _ _ hc hP
        simp only [processMessage] at hrun
        simp only [bind, Except.bind, pure, Except.pure]
        erw [hrun]
        rfl

end LeanLightEvmProofs.Hashes
