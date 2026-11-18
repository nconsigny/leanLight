import LeanLightEvmProofs.Hashes.Free

/-!
# The block hashes, over a run (`HashesSuffice`)

The observed run of a frame (an observer that records each step in a state `σ`) and the plain
run of the same frame with the block hashes `hs` end in the same frame, up to the hashes, when
every BLOCKHASH the first run executes is answered alike by both lists. That condition is read
off the observer's final state through a predicate `P` that each record keeps backwards (`back`)
and that, at each step from a frame of the block `E`, implies the step's BLOCKHASH is answered
alike (`safe`). `runFrame_withHashes` is the frame, `process_withHashes` a message and a creation,
by induction on the gas as EthLib's `Proofs/Evm/Call/Observe.lean`. The `*_match_*` lemmas are
copies of EthLib's private ones there (CC0-1.0), with their proofs.
-/

namespace LeanLightEvmProofs.Hashes

open EthLib.Base (Fork U256 Hash32 Address)
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {σ : Type}

omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem resume_match_error {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {e : EvmError} (h : x = .error e) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    runFrameWith.match_1 (fun _ => β) x h_1 h_2 = h_1 e h :=
  eq_of_heq (runFrameWith.match_1.congr_eq_1 _ _ _ _ e h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem resume_match_ok {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {after : Evm fork Meter} (h : x = .ok after) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    runFrameWith.match_1 (fun _ => β) x h_1 h_2 = h_2 after h :=
  eq_of_heq (runFrameWith.match_1.congr_eq_2 _ _ _ _ after h)

omit [LawfulGasMeter Meter] in
/-- A resume reads nothing of the child's block hashes. -/
theorem resume_withHashes_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (hs : List Hash32)
    (child : Evm fork Meter) : resume (frameWithHashes hs child) = resume child := by
  rcases step_eq_child_resume h with ⟨n, a, b, rfl⟩ | ⟨n, a, rfl⟩
  · rfl
  · rfl


section Frame

variable (hs : List Hash32) (E : BlockEnvironment fork)
  (rec : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ) (P : σ → Prop)

/-- **A frame.** If the observed run of `evm` (of the block `E`) ends in `ended` with a final
state in `P`, then `P` held at its start, and the plain run of `evm` with the hashes `hs` ends in
`ended` with the hashes `hs`. Each message the frame sends must do the same (`children`). -/
theorem runFrame_withHashes
    (back : ∀ e r s, P (rec e r s) → P s)
    (safe : ∀ e s, e.message.blockEnv = E → e.running = true → P (rec e (step fork e) s) →
      BlockhashAgrees hs e)
    {bound : Nat} {runChild : MessageRunnerIn (StateT σ (Except EvmError)) fork Meter bound}
    {runChild' : MessageRunner fork Meter bound}
    (children : ∀ caller message lt s ended s', caller.message.blockEnv = E →
      message.blockEnv = E → runChild caller message lt s = .ok (ended, s') → P s' →
      P s ∧ runChild' (frameWithHashes hs caller) (Message.withHashes hs message) lt =
        .ok ⟨frameWithHashes hs ended.val, ended.property⟩)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) (s : σ)
    (hinv : evm.message.blockEnv = E) (ended : { after : Evm fork Meter //
      GasMeter.gasHeld after.gas ≤ bound }) (s' : σ)
    (h : runFrameWith (fun evm result => modify (rec evm result)) (step fork) (step_decreases fork)
      bound runChild evm within s = .ok (ended, s'))
    (hP : P s') :
    P s ∧ runFrameWith (fun _ _ => pure ()) (step fork) (step_decreases fork) bound runChild'
      (frameWithHashes hs evm) within = .ok ⟨frameWithHashes hs ended.val, ended.property⟩ := by
  induction hm : measure evm using Nat.strongRecOn generalizing evm s ended s' with
  | _ n ih =>
  subst hm
  generalize hl : runFrameWith (fun evm result => modify (rec evm result)) (step fork)
    (step_decreases fork) bound runChild evm within = l at h
  rw [runFrameWith] at hl
  have within' : GasMeter.gasHeld (frameWithHashes hs evm).gas ≤ bound := within
  show P s ∧ runFrameWith (fun _ _ => pure ()) (step fork) (step_decreases fork) bound runChild'
    (frameWithHashes hs evm) within' = .ok ⟨frameWithHashes hs ended.val, ended.property⟩
  rw [runFrameWith]
  by_cases running : evm.running
  · have running' : (frameWithHashes hs evm).running = true := running
    rw [dif_pos running] at hl
    rw [dif_pos running']
    split at hl <;> rename_i hstep <;> subst hl
    · -- the step failed
      rename_i e
      have hs1 : P (rec evm (.error e) s) ∧ ended.val = exceptionalHalt evm e ∧ e.aborts = false := by
        by_cases aborts : e.aborts <;>
          simp [aborts, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, modify,
            modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe,
            MonadExceptOf.throw, StateT.lift] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hP, rfl, by simpa using aborts⟩
      obtain ⟨hs1, hended, aborts⟩ := hs1
      have hH := step_withHashes evm hs (safe evm s hinv running (by rw [hstep]; exact hs1))
      rw [hstep] at hH
      refine ⟨back _ _ _ hs1, ?_⟩
      split <;> rename_i hstep'
      · rename_i e'
        rw [hH] at hstep'
        cases hstep'
        simp only [aborts, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ite_false]
        obtain ⟨v, hv⟩ := ended
        cases hended
        rfl
      · rw [hH] at hstep'; cases hstep'
      · rw [hH] at hstep'; cases hstep'
    · -- a step to the next frame
      rename_i after
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure] at h
      have hmsg : after.message = evm.message :=
        ((stepRules_messageCode (fork := fork) (Meter := Meter)).step hstep).1
      have hlt : measure after < measure evm := step_decreases fork running hstep
      obtain ⟨hs1, IH⟩ := ih _ hlt after _ _ (by rw [hmsg]; exact hinv) _ _ h hP rfl
      have hH := step_withHashes evm hs (safe evm s hinv running (by rw [hstep]; exact hs1))
      rw [hstep] at hH
      refine ⟨back _ _ _ hs1, ?_⟩
      split <;> rename_i hstep'
      · rw [hH] at hstep'; cases hstep'
      · rename_i after'
        rw [hH] at hstep'
        cases hstep'
        simp only [bind, Except.bind, pure, Except.pure]
        exact IH
      · rw [hH] at hstep'; cases hstep'
    · -- a message to run first
      rename_i caller message resume
      have hcall : caller.message = evm.message :=
        ((stepRules_messageCode (fork := fork) (Meter := Meter)).step hstep).1.1
      have hcallE : caller.message.blockEnv = E := by rw [hcall]; exact hinv
      have hmsgE : message.blockEnv = E := (step_child hstep).trans hcallE
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure] at h
      generalize Nat.lt_of_lt_of_le (step_decreases fork running hstep).1 within = lt at h
      cases hc : runChild caller message lt (rec evm (.ok (.child caller message resume)) s) with
      | error e => rw [hc] at h; cases h
      | ok a =>
        rw [hc] at h
        obtain ⟨⟨child, used⟩, s2⟩ := a
        dsimp only at h
        have hresH : ∀ ch, resume (frameWithHashes hs ch) = resume ch :=
          resume_withHashes_child hstep hs
        obtain ⟨e, hres⟩ | ⟨after, hres⟩ :
            (∃ e, resume child = .error e) ∨ ∃ after, resume child = .ok after := by
          cases resume child <;> simp
        · -- the resume failed: the frame halts
          rw [resume_match_error hres] at h
          have hs2 : s2 = s' ∧ ended.val = exceptionalHalt evm e ∧ e.aborts = false := by
            by_cases aborts : e.aborts <;>
              simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
                StateT.lift, bind, Except.bind, Except.pure] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, rfl, by simpa using aborts⟩
          obtain ⟨rfl, hended, aborts⟩ := hs2
          obtain ⟨hs1, hrun'⟩ := children caller message lt _ ⟨child, used⟩ s2 hcallE hmsgE hc hP
          have hH := step_withHashes evm hs (safe evm s hinv running (by rw [hstep]; exact hs1))
          rw [hstep] at hH
          refine ⟨back _ _ _ hs1, ?_⟩
          split <;> rename_i hstep'
          · rw [hH] at hstep'; cases hstep'
          · rw [hH] at hstep'; cases hstep'
          · rw [hH] at hstep'
            cases hstep'
            simp only [bind, Except.bind, pure, Except.pure]
            rw [hrun']
            dsimp only
            have hres' : frameWithHashes hs <$> resume (frameWithHashes hs child) = .error e := by
              rw [hresH, hres]; rfl
            rw [resume_match_error hres']
            simp only [aborts, Bool.false_eq_true, ite_false]
            obtain ⟨v, hv⟩ := ended
            cases hended
            rfl
        · -- the frame resumes
          rw [resume_match_ok hres] at h
          have hafter : after.message = evm.message := by
            rw [(sameContext_of_step_eq_child hstep hres).message, message_incorporateChild,
              hcall]
          have hlt : measure after < measure evm :=
            (step_decreases fork running hstep).2 child after used hres
          obtain ⟨hs2, IH⟩ := ih _ hlt after _ _ (by rw [hafter]; exact hinv) _ _ h hP rfl
          obtain ⟨hs1, hrun'⟩ := children caller message lt _ ⟨child, used⟩ s2 hcallE hmsgE hc hs2
          have hH := step_withHashes evm hs (safe evm s hinv running (by rw [hstep]; exact hs1))
          rw [hstep] at hH
          refine ⟨back _ _ _ hs1, ?_⟩
          split <;> rename_i hstep'
          · rw [hH] at hstep'; cases hstep'
          · rw [hH] at hstep'; cases hstep'
          · rw [hH] at hstep'
            cases hstep'
            simp only [bind, Except.bind, pure, Except.pure]
            rw [hrun']
            dsimp only
            have hres' : frameWithHashes hs <$> resume (frameWithHashes hs child) =
                .ok (frameWithHashes hs after) := by
              rw [hresH, hres]; rfl
            rw [resume_match_ok hres']
            exact IH
  · have running' : ¬(frameWithHashes hs evm).running = true := running
    rw [dif_neg running] at hl
    rw [dif_neg running']
    subst hl
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hP, rfl⟩

end Frame


omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem startState_withHashes (hs : List Hash32) (m : Message fork) (st : TransactionState) :
    startState fork (Message.withHashes hs m) st = startState fork m st := rfl

/-- The state that a message enters, before or after the move of its value (EthLib's private
`enterState`, `Proofs/Evm/Call/NoninterferenceRun.lean`, restated). -/
def enterState' (fork : Fork) (message : Message fork) (state : TransactionState) :
    Except EvmError TransactionState :=
  if message.shouldTransferValue = true ∧ message.value ≠ 0 then
    ((startState fork message state).moveEther fork message.caller message.currentTarget
      message.value).mapError .state
  else pure (startState fork message state)

/-- The substate that a message enters, with the log of the move of its value if any. -/
def enterSubstate' (fork : Fork) (message : Message fork) (substate : Substate) : Substate :=
  if message.shouldTransferValue = true ∧ message.value ≠ 0 then
    { substate with
      logs := pushTransferLog fork substate.logs message.caller message.currentTarget
        message.value
      simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs message.caller
        message.currentTarget message.value }
  else substate

/-- A message runs its code or its precompile from the state it enters, in the monad `M`. -/
def bodyWith {M : Type → Type} [Monad M] [MonadExceptOf EvmError M]
    (observe : StepObserver M fork Meter) (message : Message fork) (substate : Substate)
    (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas) (state : TransactionState) :
    M { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } :=
  let evm : Evm fork Meter := startFrame message state (enterSubstate' fork message substate) meter
  match precompileAddress fork message with
  | some address =>
    if message.disablePrecompiles then
      pure ⟨{ evm with running := false }, held⟩
    else
      match h : runPrecompile fork address evm with
      | some after => pure ⟨after, Nat.le_trans (gasHeld_runPrecompile_le h) held⟩
      | none => pure ⟨{ evm with running := false }, held⟩
  | none =>
    runFrameWith observe (step fork) (step_decreases fork) message.gas
      (fun caller child _ =>
        match child.target with
        | some _ =>
          processMessageWith fork observe child caller.state caller.substate.child
        | none =>
          processCreateMessageWith fork observe child caller.state caller.substate.child)
      evm held

omit [LawfulGasMeter Meter] in
theorem gasHeld_rollbackOnError_le' [LawfulGasMeter Meter] {message : Message fork}
    (state : TransactionState)
    (ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }) :
    GasMeter.gasHeld (rollbackOnError state ended.val).gas ≤ message.gas := by
  unfold rollbackOnError
  split
  · dsimp only
    split
    · exact Nat.le_trans (LawfulGasMeter.gasHeld_rollback _) ended.property
    · exact ended.property
  · exact ended.property

omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem precompile_match_some {β : Sort _} {x : Option (Evm fork Meter)}
    {after : Evm fork Meter} (h : x = some after)
    (h_1 : (after : Evm fork Meter) → x = some after → β) (h_2 : x = none → β) :
    processMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_1 after h :=
  eq_of_heq (processMessageWith.match_1.congr_eq_1 _ _ _ _ _ after h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem precompile_match_none {β : Sort _} {x : Option (Evm fork Meter)}
    (h : x = none) (h_1 : (after : Evm fork Meter) → x = some after → β) (h_2 : x = none → β) :
    processMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_2 h :=
  eq_of_heq (processMessageWith.match_1.congr_eq_2 _ _ _ _ _ h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem deposit_match_error {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {e : EvmError} (h : x = .error e) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    processCreateMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_1 e h :=
  eq_of_heq (processCreateMessageWith.match_1.congr_eq_1 _ _ _ _ _ e h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
theorem deposit_match_ok {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {after : Evm fork Meter} (h : x = .ok after) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    processCreateMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_2 after h :=
  eq_of_heq (processCreateMessageWith.match_1.congr_eq_2 _ _ _ _ _ after h)

section Message

variable (hs : List Hash32) (E : BlockEnvironment fork)
  (rec : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ) (P : σ → Prop)

theorem process_withHashes
    (back : ∀ e r s, P (rec e r s) → P s)
    (safe : ∀ e s, e.message.blockEnv = E → e.running = true → P (rec e (step fork e) s) →
      BlockhashAgrees hs e) (n : Nat) :
    ∀ message : Message fork, message.gas = n → message.blockEnv = E →
      (∀ state substate (meter : Meter) held s ended s',
        processMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (rec evm result)) message state substate meter held s =
            .ok (ended, s') → P s' →
        P s ∧ processMessage fork (Message.withHashes hs message) state substate meter held =
          .ok ⟨frameWithHashes hs ended.val, ended.property⟩) ∧
      (∀ state substate (meter : Meter) held s ended s',
        processCreateMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (rec evm result)) message state substate meter held s =
            .ok (ended, s') → P s' →
        P s ∧ processCreateMessage fork (Message.withHashes hs message) state substate meter held =
          .ok ⟨frameWithHashes hs ended.val, ended.property⟩) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro message gas hE
  have call : ∀ state substate (meter : Meter) held s ended s',
      processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (rec evm result)) message state substate meter held s =
          .ok (ended, s') → P s' →
      P s ∧ processMessage fork (Message.withHashes hs message) state substate meter held =
        .ok ⟨frameWithHashes hs ended.val, ended.property⟩ := by
    intro state substate meter held s ended s' h hP
    -- the messages the frame sends, on both sides
    have children : ∀ (caller : Evm fork Meter) (child : Message fork) (lt : child.gas < message.gas)
        (s0 : σ) (ended0 : { e : Evm fork Meter // GasMeter.gasHeld e.gas ≤ child.gas }) (s0' : σ),
        caller.message.blockEnv = E → child.blockEnv = E →
        (match child.target with
          | some _ => processMessageWith (M := StateT σ (Except EvmError)) fork
              (fun evm result => modify (rec evm result)) child caller.state caller.substate.child
          | none => processCreateMessageWith (M := StateT σ (Except EvmError)) fork
              (fun evm result => modify (rec evm result)) child caller.state
              caller.substate.child) s0 = .ok (ended0, s0') → P s0' →
        P s0 ∧ (match (Message.withHashes hs child).target with
          | some _ => processMessage fork (Message.withHashes hs child)
              (frameWithHashes hs caller).state (frameWithHashes hs caller).substate.child
          | none => processCreateMessage fork (Message.withHashes hs child)
              (frameWithHashes hs caller).state (frameWithHashes hs caller).substate.child) =
          .ok ⟨frameWithHashes hs ended0.val, ended0.property⟩ := by
      intro caller child lt s0 ended0 s0' _ hchildE hrun hP0
      have lt' : child.gas < n := gas ▸ lt
      cases ht : child.target with
      | some _ =>
        simp only [ht] at hrun
        simp only [mwh_target, ht]
        exact (ih _ lt' child rfl hchildE).1 _ _ _ _ _ _ _ hrun hP0
      | none =>
        simp only [ht] at hrun
        simp only [mwh_target, ht]
        exact (ih _ lt' child rfl hchildE).2 _ _ _ _ _ _ _ hrun hP0
    have held' : GasMeter.gasHeld meter ≤ (Message.withHashes hs message).gas := held
    show P s ∧ processMessage fork (Message.withHashes hs message) state substate meter held' = _
    rw [processMessage, processMessageWith]
    rw [processMessageWith] at h
    simp only [Functor.map, StateT.map, Except.map, bind, StateT.bind, Except.bind] at h ⊢
    try dsimp only at h ⊢
    split at h
    · cases h
    · rename_i v hv
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split at hv
      · rename_i ht
        have ht' : (Message.withHashes hs message).shouldTransferValue = true ∧
            (Message.withHashes hs message).value ≠ 0 := ht
        rw [if_pos ht']
        cases hmv : TransactionState.moveEther fork (startState fork message state) message.caller
            message.currentTarget message.value with
        | error err =>
          simp only [hmv, liftExcept, Except.mapError, bind, StateT.bind, throw, throwThe,
            MonadExceptOf.throw, StateT.lift, Except.bind] at hv
          cases hv
        | ok st1 =>
          have hmv' : TransactionState.moveEther fork (startState fork (Message.withHashes hs message)
              state) (Message.withHashes hs message).caller
              (Message.withHashes hs message).currentTarget (Message.withHashes hs message).value =
              .ok st1 := hmv
          rw [hmv']
          simp only [hmv, liftExcept, Except.mapError, StateT.bind, pure, StateT.pure, bind,
            Except.bind, Except.pure] at hv
          dsimp only
          rw [precompileAddress_withHashes]
          simp only [liftExcept, Except.mapError]
          cases hpa : precompileAddress fork message with
          | none =>
            simp only [hpa] at hv ⊢
            obtain ⟨hPs, hrun⟩ := runFrame_withHashes hs E rec P back safe
              (runChild' := fun caller child _ =>
                match child.target with
                | some _ => processMessage fork child caller.state caller.substate.child
                | none => processCreateMessage fork child caller.state caller.substate.child)
              children _ held s hE v.1 v.2 hv hP
            refine ⟨hPs, ?_⟩
            simp only [processMessage, processCreateMessage] at hrun
            simp only [pure, Except.pure]
            rw [if_pos ht']
            erw [hrun]
            simp only [Except.ok.injEq]
            apply Subtype.ext
            exact rollbackOnError_withHashes (Meter := Meter) hs state v.1.val
          | some a =>
            simp only [hpa] at hv ⊢
            simp only [pure, Except.pure]
            by_cases hd : message.disablePrecompiles = true
            · have hd' : (Message.withHashes hs message).disablePrecompiles = true := hd
              rw [if_pos hd] at hv
              rw [if_pos hd', if_pos ht']
              simp only [StateT.pure, pure, Except.pure, Except.ok.injEq] at hv
              subst hv
              refine ⟨hP, ?_⟩
              simp only [Except.ok.injEq]
              apply Subtype.ext
              dsimp only
              rw [← rollbackOnError_withHashes]
              rfl
            · have hd' : ¬(Message.withHashes hs message).disablePrecompiles = true := hd
              rw [if_neg hd] at hv
              rw [if_neg hd']
              have hfr : ∀ sub' : Substate,
                  runPrecompile fork a (startFrame (Message.withHashes hs message) st1 sub' meter) =
                    frameWithHashes hs <$> runPrecompile fork a (startFrame message st1 sub' meter) :=
                fun sub' => runPrecompile_withHashes hs a (startFrame message st1 sub' meter)
              have hr2 : runPrecompile fork a (startFrame (Message.withHashes hs message) st1
                  (if (Message.withHashes hs message).shouldTransferValue = true ∧
                      (Message.withHashes hs message).value ≠ 0 then
                    { substate with
                      logs := pushTransferLog fork substate.logs
                        (Message.withHashes hs message).caller
                        (Message.withHashes hs message).currentTarget
                        (Message.withHashes hs message).value
                      simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs
                        (Message.withHashes hs message).caller
                        (Message.withHashes hs message).currentTarget
                        (Message.withHashes hs message).value }
                  else substate) meter) =
                  frameWithHashes hs <$> runPrecompile fork a (startFrame message st1
                  (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
                    { substate with
                      logs := pushTransferLog fork substate.logs message.caller
                        message.currentTarget message.value
                      simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs
                        message.caller message.currentTarget message.value }
                  else substate) meter) := hfr _
              cases hr1 : runPrecompile fork a (startFrame message st1
                  (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
                    { substate with
                      logs := pushTransferLog fork substate.logs message.caller
                        message.currentTarget message.value
                      simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs
                        message.caller message.currentTarget message.value }
                  else substate) meter) with
              | none =>
                rw [hr1] at hr2
                rw [precompile_match_none hr1] at hv
                rw [precompile_match_none hr2]
                rw [if_pos ht']
                simp only [StateT.pure, pure, Except.pure, Except.ok.injEq] at hv
                subst hv
                refine ⟨hP, ?_⟩
                simp only [Except.ok.injEq]
                apply Subtype.ext
                dsimp only
                rw [← rollbackOnError_withHashes]
                rfl
              | some after =>
                rw [hr1] at hr2
                rw [precompile_match_some hr1] at hv
                rw [precompile_match_some hr2]
                simp only [StateT.pure, pure, Except.pure, Except.ok.injEq] at hv
                subst hv
                refine ⟨hP, ?_⟩
                simp only [Except.ok.injEq]
                apply Subtype.ext
                dsimp only
                rw [← rollbackOnError_withHashes]
      · rename_i ht
        have ht' : ¬((Message.withHashes hs message).shouldTransferValue = true ∧
            (Message.withHashes hs message).value ≠ 0) := ht
        rw [if_neg ht']
        simp only [StateT.bind, pure, StateT.pure, bind, Except.bind, Except.pure] at hv
        simp only [pure, Except.pure, startState_withHashes]
        generalize startState fork message state = st1 at hv ⊢
        rw [precompileAddress_withHashes]
        try simp only [liftExcept, Except.mapError]
        cases hpa : precompileAddress fork message with
        | none =>
          simp only [hpa] at hv ⊢
          obtain ⟨hPs, hrun⟩ := runFrame_withHashes hs E rec P back safe
            (runChild' := fun caller child _ =>
              match child.target with
              | some _ => processMessage fork child caller.state caller.substate.child
              | none => processCreateMessage fork child caller.state caller.substate.child)
            children _ held s hE v.1 v.2 hv hP
          refine ⟨hPs, ?_⟩
          simp only [processMessage, processCreateMessage] at hrun
          try simp only [pure, Except.pure]
          rw [if_neg ht']
          erw [hrun]
          simp only [Except.ok.injEq]
          apply Subtype.ext
          exact rollbackOnError_withHashes (Meter := Meter) hs state v.1.val
        | some a =>
          simp only [hpa] at hv ⊢
          try simp only [pure, Except.pure]
          by_cases hd : message.disablePrecompiles = true
          · have hd' : (Message.withHashes hs message).disablePrecompiles = true := hd
            rw [if_pos hd] at hv
            rw [if_pos hd', if_neg ht']
            simp only [StateT.pure, pure, Except.pure, Except.ok.injEq] at hv
            subst hv
            refine ⟨hP, ?_⟩
            simp only [Except.ok.injEq]
            apply Subtype.ext
            dsimp only
            rw [← rollbackOnError_withHashes]
            rfl
          · have hd' : ¬(Message.withHashes hs message).disablePrecompiles = true := hd
            rw [if_neg hd] at hv
            rw [if_neg hd']
            have hfr : ∀ sub' : Substate,
                runPrecompile fork a (startFrame (Message.withHashes hs message) st1 sub' meter) =
                  frameWithHashes hs <$> runPrecompile fork a (startFrame message st1 sub' meter) :=
              fun sub' => runPrecompile_withHashes hs a (startFrame message st1 sub' meter)
            have hr2 : runPrecompile fork a (startFrame (Message.withHashes hs message) st1
                (if (Message.withHashes hs message).shouldTransferValue = true ∧
                    (Message.withHashes hs message).value ≠ 0 then
                  { substate with
                    logs := pushTransferLog fork substate.logs
                      (Message.withHashes hs message).caller
                      (Message.withHashes hs message).currentTarget
                      (Message.withHashes hs message).value
                    simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs
                      (Message.withHashes hs message).caller
                      (Message.withHashes hs message).currentTarget
                      (Message.withHashes hs message).value }
                else substate) meter) =
                frameWithHashes hs <$> runPrecompile fork a (startFrame message st1
                (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
                  { substate with
                    logs := pushTransferLog fork substate.logs message.caller
                      message.currentTarget message.value
                    simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs
                      message.caller message.currentTarget message.value }
                else substate) meter) := hfr _
            cases hr1 : runPrecompile fork a (startFrame message st1
                (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
                  { substate with
                    logs := pushTransferLog fork substate.logs message.caller
                      message.currentTarget message.value
                    simulatedLogs := pushSimulatedTransferLog fork substate.simulatedLogs
                      message.caller message.currentTarget message.value }
                else substate) meter) with
            | none =>
              rw [hr1] at hr2
              rw [precompile_match_none hr1] at hv
              rw [precompile_match_none hr2]
              rw [if_neg ht']
              simp only [StateT.pure, pure, Except.pure, Except.ok.injEq] at hv
              subst hv
              refine ⟨hP, ?_⟩
              simp only [Except.ok.injEq]
              apply Subtype.ext
              dsimp only
              rw [← rollbackOnError_withHashes]
              rfl
            | some after =>
              rw [hr1] at hr2
              rw [precompile_match_some hr1] at hv
              rw [precompile_match_some hr2]
              simp only [StateT.pure, pure, Except.pure, Except.ok.injEq] at hv
              subst hv
              refine ⟨hP, ?_⟩
              simp only [Except.ok.injEq]
              apply Subtype.ext
              dsimp only
              rw [← rollbackOnError_withHashes]
  refine ⟨call, ?_⟩
  intro state substate meter held s ended s' h hP
  rw [processCreateMessageWith] at h
  have held' : GasMeter.gasHeld meter ≤ (Message.withHashes hs message).gas := held
  show P s ∧ processCreateMessage fork (Message.withHashes hs message) state substate meter held' = _
  rw [processCreateMessage_unfold]
  simp only [mwh_currentTarget]
  cases hpc : prepareCreation fork state message.currentTarget with
  | error err =>
    simp only [hpc, liftExcept, bind, StateT.bind, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, Except.bind] at h
    cases h
  | ok prepared =>
    simp only [hpc, liftExcept, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure] at h ⊢
    cases hpm : processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (rec evm result)) message prepared substate meter held s with
    | error err => rw [hpm] at h; cases h
    | ok r =>
      rw [hpm] at h
      obtain ⟨⟨evm, used⟩, s1⟩ := r
      dsimp only at h
      cases hd : depositCode fork state evm with
      | error err =>
        rw [deposit_match_error hd] at h
        simp only [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
        cases h
      | ok after =>
        rw [deposit_match_ok hd] at h
        simp only [StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hPs, hrun⟩ := call prepared substate meter held s ⟨evm, used⟩ s1 hpm hP
        refine ⟨hPs, ?_⟩
        rw [hrun]
        dsimp only
        have hd' : depositCode fork state (frameWithHashes hs evm) = .ok (frameWithHashes hs after) := by
          rw [depositCode_withHashes, hd]; rfl
        split <;> rename_i hd2
        · rw [hd'] at hd2; cases hd2
        · rw [hd'] at hd2; cases hd2; rfl

end Message

end LeanLightEvmProofs.Hashes
