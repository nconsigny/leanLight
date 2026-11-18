import LeanLightEvmProofs.CallAgrees

/-!
# The block hashes, step by step (`HashesSuffice`)

`frameWithHashes hs evm` is the frame `evm` with the block hashes of its message replaced by `hs`
(`Message.withHashes`); `StepResult.withHashes` does the same to a step's result, and to the frame
a resume gives. Every instruction of EthLib's dispatch but BLOCKHASH moves that replacement
through unchanged (`instruction_hashFree`, `HashFree`), and so do the calls and creations
(`messageInstruction_withHashes`); BLOCKHASH does when both lists give the same hash for the
number on top of the stack (`blockhashStep_withHashes`). Hence `step_withHashes`: a step of the
frame with the hashes `hs` is the step of the frame, with the hashes `hs`, unless it is a
BLOCKHASH the two lists answer differently (`BlockhashAgrees`). `step_child`: a message a step
sends runs in its caller's block. The proofs follow EthLib's `StateFree` proofs
(`Proofs/Evm/Noninterference.lean` at the pin), with the hashes in place of the state.
-/

namespace LeanLightEvmProofs.Hashes

open EthLib.Base (Fork U256 Hash32 Address)
open EthLib.Execution.Evm

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The message with the block hashes `hs`. -/
def Message.withHashes (hs : List Hash32) (m : Message fork) : Message fork :=
  { m with blockEnv := { m.blockEnv with blockHashes := hs } }

/-- The frame with the block hashes `hs` in its message. -/
def frameWithHashes (hs : List Hash32) (evm : Evm fork Meter) : Evm fork Meter :=
  { evm with message := Message.withHashes hs evm.message }

/-- A step result with the block hashes `hs` in every frame and message it holds; a resume gets
them in the frame it gives. -/
def StepResult.withHashes (hs : List Hash32) : StepResult fork Meter → StepResult fork Meter
  | .next after => .next (frameWithHashes hs after)
  | .child caller message resume =>
    .child (frameWithHashes hs caller) (Message.withHashes hs message)
      (fun child => frameWithHashes hs <$> resume child)


/-! Projections -/

omit [GasMeter Meter] in
@[simp] theorem fwh_pc (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).pc = e.pc := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_stack (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).stack = e.stack := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_memory (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).memory = e.memory := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_code (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).code = e.code := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_validJumpDestinations (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).validJumpDestinations = e.validJumpDestinations := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_gas (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).gas = e.gas := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_running (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).running = e.running := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_output (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).output = e.output := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_returnData (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).returnData = e.returnData := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_state (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).state = e.state := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_substate (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).substate = e.substate := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_error (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).error = e.error := rfl

omit [GasMeter Meter] in
@[simp] theorem fwh_message (hs : List Hash32) (e : Evm fork Meter) :
    (frameWithHashes hs e).message = Message.withHashes hs e.message := rfl

@[simp] theorem mwh_txEnv (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).txEnv = m.txEnv := rfl

@[simp] theorem mwh_caller (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).caller = m.caller := rfl

@[simp] theorem mwh_target (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).target = m.target := rfl

@[simp] theorem mwh_currentTarget (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).currentTarget = m.currentTarget := rfl

@[simp] theorem mwh_gas (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).gas = m.gas := rfl

@[simp] theorem mwh_reservoir (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).reservoir = m.reservoir := rfl

@[simp] theorem mwh_value (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).value = m.value := rfl

@[simp] theorem mwh_data (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).data = m.data := rfl

@[simp] theorem mwh_codeAddress (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).codeAddress = m.codeAddress := rfl

@[simp] theorem mwh_code (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).code = m.code := rfl

@[simp] theorem mwh_depth (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).depth = m.depth := rfl

@[simp] theorem mwh_shouldTransferValue (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).shouldTransferValue = m.shouldTransferValue := rfl

@[simp] theorem mwh_isStatic (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).isStatic = m.isStatic := rfl

@[simp] theorem mwh_disablePrecompiles (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).disablePrecompiles = m.disablePrecompiles := rfl

@[simp] theorem mwh_blockEnv (hs : List Hash32) (m : Message fork) :
    (Message.withHashes hs m).blockEnv = { m.blockEnv with blockHashes := hs } := rfl

omit [GasMeter Meter] in
/-- A frame written out with a message whose hashes were replaced is the frame with them replaced. -/
theorem mk_withHashes (hs : List Hash32) (pc : Nat) (stack : Stack) (memory code : ByteArray)
    (v : Array Bool) (gas : Meter) (running : Bool) (m : Message fork) (output returnData : ByteArray)
    (state : EthLib.Execution.State.TransactionState) (substate : Substate) (error : Option EvmError) :
    (Evm.mk pc stack memory code v gas running (Message.withHashes hs m) output returnData state
        substate error) =
      frameWithHashes hs (Evm.mk pc stack memory code v gas running m output returnData state
        substate error) := rfl

/-- A step that moves a replacement of the block hashes through unchanged. -/
def HashFree (run : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  ∀ evm hs, run (frameWithHashes hs evm) = frameWithHashes hs <$> run evm

omit [GasMeter Meter] in
theorem popWord_withHashes (evm : Evm fork Meter) (hs : List Hash32) :
    popWord (frameWithHashes hs evm) = (fun p => (p.1, frameWithHashes hs p.2)) <$> popWord evm := by
  simp only [popWord, frameWithHashes]
  cases evm.stack.pop <;> rfl

omit [GasMeter Meter] in
theorem pushWord_withHashes (evm : Evm fork Meter) (hs : List Hash32) (x : U256) :
    pushWord (frameWithHashes hs evm) x = frameWithHashes hs <$> pushWord evm x := by
  simp only [pushWord, frameWithHashes]
  cases evm.stack.push x <;> rfl

theorem chargeGas_withHashes (evm : Evm fork Meter) (hs : List Hash32) (amount : Nat) :
    chargeGas (frameWithHashes hs evm) amount = frameWithHashes hs <$> chargeGas evm amount := by
  simp only [chargeGas, frameWithHashes]
  cases GasMeter.charge evm.gas amount <;> rfl

theorem chargeStateGas_withHashes (evm : Evm fork Meter) (hs : List Hash32) (amount : Nat) :
    chargeStateGas (frameWithHashes hs evm) amount = frameWithHashes hs <$> chargeStateGas evm amount := by
  simp only [chargeStateGas, frameWithHashes]
  cases GasMeter.chargeState evm.gas amount <;> rfl

theorem chargeGasAndMemory_withHashes (evm : Evm fork Meter) (hs : List Hash32) (cost : Nat)
    (ranges : List (U256 × U256)) :
    chargeGasAndMemory (frameWithHashes hs evm) cost ranges =
      frameWithHashes hs <$> chargeGasAndMemory evm cost ranges := by
  simp only [chargeGasAndMemory, chargeGas_withHashes, bind_map_left, map_bind, map_pure]
  rfl

omit [GasMeter Meter] in
theorem popTopics_withHashes (evm : Evm fork Meter) (hs : List Hash32) (n : Nat) :
    popTopics (frameWithHashes hs evm) n =
      (fun p => (p.1, frameWithHashes hs p.2)) <$> popTopics evm n := by
  induction n generalizing evm with
  | zero => rfl
  | succ k ih =>
    simp only [popTopics, popWord_withHashes, bind_map_left, map_bind, map_pure, ih]


omit [GasMeter Meter] in
theorem recordAccountRead_withHashes (evm : Evm fork Meter) (hs : List Hash32) (a : Address) :
    recordAccountRead (frameWithHashes hs evm) a = frameWithHashes hs (recordAccountRead evm a) :=
  rfl

omit [GasMeter Meter] in
theorem recordStorageRead_withHashes (evm : Evm fork Meter) (hs : List Hash32) (a : Address)
    (k : EthLib.Base.Bytes32) :
    recordStorageRead (frameWithHashes hs evm) a k =
      frameWithHashes hs (recordStorageRead evm a k) :=
  rfl

omit [GasMeter Meter] in
theorem accessAddress_withHashes (evm : Evm fork Meter) (hs : List Hash32) (a : Address) :
    accessAddress (frameWithHashes hs evm) a =
      ((accessAddress evm a).1, frameWithHashes hs (accessAddress evm a).2) := by
  unfold accessAddress
  split <;> rfl

omit [GasMeter Meter] in
theorem accessStorageKey_withHashes (evm : Evm fork Meter) (hs : List Hash32) (a : Address)
    (k : EthLib.Base.Bytes32) :
    accessStorageKey (frameWithHashes hs evm) a k =
      ((accessStorageKey evm a k).1, frameWithHashes hs (accessStorageKey evm a k).2) := by
  unfold accessStorageKey
  split <;> rfl

omit [GasMeter Meter] in
theorem accountCode_withHashes (evm : Evm fork Meter) (hs : List Hash32) (a : Address) :
    accountCode (frameWithHashes hs evm) a = accountCode evm a :=
  rfl

theorem checkGas_withHashes (evm : Evm fork Meter) (hs : List Hash32) (n : Nat) :
    checkGas (frameWithHashes hs evm) n = checkGas evm n :=
  rfl

theorem refillStateGas_withHashes (evm : Evm fork Meter) (hs : List Hash32) (n : Nat) :
    refillStateGas (frameWithHashes hs evm) n = frameWithHashes hs (refillStateGas evm n) :=
  rfl

theorem exceptionalHalt_withHashes (evm : Evm fork Meter) (hs : List Hash32) (e : EvmError) :
    exceptionalHalt (frameWithHashes hs evm) e = frameWithHashes hs (exceptionalHalt evm e) :=
  rfl

theorem keepReads_withHashes (evm : Evm fork Meter) (hs : List Hash32)
    {rest' rest : Except EvmError (Evm fork Meter)} (h : rest' = frameWithHashes hs <$> rest) :
    keepReads (frameWithHashes hs evm) id rest' = frameWithHashes hs <$> keepReads evm id rest := by
  subst h
  unfold keepReads
  cases rest with
  | error e => by_cases h : e.aborts <;> simp [h, Functor.map, Except.map] <;> rfl
  | ok r => rfl

theorem map_ite_withHashes {α β : Type} (g : α → β) (c : Prop) [Decidable c]
    (a b : Except EvmError α) :
    (g <$> if c then a else b) = if c then g <$> a else g <$> b := by
  split <;> rfl

@[simp] theorem StepResult.withHashes_next (hs : List Hash32) (a : Evm fork Meter) :
    StepResult.withHashes hs (.next a) = .next (frameWithHashes hs a) := rfl

@[simp] theorem StepResult.withHashes_child (hs : List Hash32) (c : Evm fork Meter)
    (m : Message fork) (r : Evm fork Meter → Except EvmError (Evm fork Meter)) :
    StepResult.withHashes hs (.child c m r) =
      .child (frameWithHashes hs c) (Message.withHashes hs m)
        (fun child => frameWithHashes hs <$> r child) := rfl

theorem keepReads_next_withHashes (evm : Evm fork Meter) (hs : List Hash32)
    {rest' rest : Except EvmError (StepResult fork Meter)}
    (h : rest' = StepResult.withHashes hs <$> rest) :
    keepReads (frameWithHashes hs evm) StepResult.next rest' =
      StepResult.withHashes hs <$> keepReads evm StepResult.next rest := by
  subst h
  unfold keepReads
  cases rest with
  | error e => by_cases h : e.aborts <;> simp [h, Functor.map, Except.map] <;> rfl
  | ok r => rfl

theorem incorporateChild_withHashes (hs : List Hash32) (c ch : Evm fork Meter) :
    incorporateChild fork (frameWithHashes hs c) ch = frameWithHashes hs (incorporateChild fork c ch) := by
  unfold incorporateChild touchedOnError touchedOnSuccess
  split <;> rfl

theorem skipCall_withHashes (hs : List Hash32) (e : Evm fork Meter) (g r : Nat) :
    skipCall (frameWithHashes hs e) g r = frameWithHashes hs <$> skipCall e g r := by
  simp only [skipCall, pushWord, frameWithHashes, bind, Except.bind, pure, Except.pure]
  cases Stack.push _ _ <;> rfl

theorem ok_bind_withHashes {α β : Type} (a : α) (f : α → Except EvmError β) :
    (Except.ok a >>= f) = f a := rfl

/-- The rewrites that move the replaced hashes outwards. -/
local macro "hash_simp" : tactic =>
  `(tactic| simp only [popWord_withHashes, pushWord_withHashes, chargeGas_withHashes,
               chargeStateGas_withHashes, chargeGasAndMemory_withHashes, popTopics_withHashes,
               recordAccountRead_withHashes, recordStorageRead_withHashes, accessAddress_withHashes,
               accessStorageKey_withHashes, accountCode_withHashes, checkGas_withHashes,
               refillStateGas_withHashes, incorporateChild_withHashes, mk_withHashes,
               skipCall_withHashes, ok_bind_withHashes, Functor.map_map,
               StepResult.withHashes_next, StepResult.withHashes_child,
               fwh_pc, fwh_stack, fwh_memory, fwh_code, fwh_validJumpDestinations, fwh_gas, fwh_running, fwh_output, fwh_returnData, fwh_state, fwh_substate, fwh_error, fwh_message, mwh_txEnv, mwh_caller, mwh_target, mwh_currentTarget, mwh_gas, mwh_reservoir, mwh_value, mwh_data, mwh_codeAddress, mwh_code, mwh_depth, mwh_shouldTransferValue, mwh_isStatic, mwh_disablePrecompiles, mwh_blockEnv,
               map_ite_withHashes,
               bind_map_left, map_bind, map_pure, advance, bind_assoc, pure_bind])

/-- Unfold a step and move the replaced hashes through each of its parts. -/
local macro "hash_free" : tactic =>
  `(tactic| ((try hash_simp)
             repeat' (first
               | rfl
               | refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
               | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
               | (refine keepReads_next_withHashes _ _ ?_
                  try hash_simp)
               | (refine keepReads_withHashes _ _ ?_
                  try hash_simp)
               | (split <;> (try hash_simp) <;>
                   (try simp_all [map_pure, throw, throwThe, MonadExceptOf.throw])))
             all_goals (repeat' (first
               | rfl
               | (split <;> simp_all [Functor.map, Except.map, pure, Except.pure])
               | omega))))

theorem unaryOp_hashFree (cost : Nat) (f : U256 → U256) :
    HashFree (unaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm hs
  simp only [unaryOp]
  hash_free

theorem binaryOp_hashFree (cost : Nat) (f : U256 → U256 → U256) :
    HashFree (binaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm hs
  simp only [binaryOp]
  hash_free

theorem ternaryOp_hashFree (cost : Nat) (f : U256 → U256 → U256 → U256) :
    HashFree (ternaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm hs
  simp only [ternaryOp]
  hash_free

theorem readFrame_hashFree (cost : Nat) (value : Evm fork Meter → U256)
    (hvalue : ∀ evm hs, value (frameWithHashes hs evm) = value evm) :
    HashFree (readFrame cost value) := by
  intro evm hs
  simp only [readFrame]
  hash_free
  all_goals (try simp only [hvalue])
  all_goals rfl

theorem expStep_hashFree : HashFree (expStep (Meter := Meter) fork) := by
  intro evm hs; simp only [expStep]; hash_free

theorem keccak256Step_hashFree : HashFree (keccak256Step (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [keccak256Step]; hash_free

theorem popStep_hashFree : HashFree (popStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [popStep]; hash_free

theorem pushN_hashFree (n : Fin 33) : HashFree (pushN (fork := fork) (Meter := Meter) n) := by
  intro evm hs; simp only [pushN]; hash_free

theorem dupN_hashFree (n : Fin 16) : HashFree (dupN (fork := fork) (Meter := Meter) n) := by
  intro evm hs; simp only [dupN]; hash_free

theorem swapN_hashFree (n : Fin 16) : HashFree (swapN (fork := fork) (Meter := Meter) n) := by
  intro evm hs; simp only [swapN]; hash_free

theorem dupnStep_hashFree : HashFree (dupnStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [dupnStep]; hash_free

theorem swapnStep_hashFree : HashFree (swapnStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [swapnStep]; hash_free

theorem exchangeStep_hashFree : HashFree (exchangeStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [exchangeStep]; hash_free

omit [GasMeter Meter] in
theorem stopStep_hashFree : HashFree (stopStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [stopStep]; hash_free

theorem jumpStep_hashFree : HashFree (jumpStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [jumpStep]; hash_free

theorem jumpiStep_hashFree : HashFree (jumpiStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [jumpiStep]; hash_free

theorem jumpdestStep_hashFree : HashFree (jumpdestStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [jumpdestStep]; hash_free

theorem mloadStep_hashFree : HashFree (mloadStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [mloadStep]; hash_free

theorem mstoreStep_hashFree : HashFree (mstoreStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [mstoreStep]; hash_free

theorem mstore8Step_hashFree : HashFree (mstore8Step (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [mstore8Step]; hash_free

theorem mcopyStep_hashFree : HashFree (mcopyStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [mcopyStep]; hash_free

theorem calldataloadStep_hashFree :
    HashFree (calldataloadStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [calldataloadStep]; hash_free

theorem copyToMemory_hashFree (base : Nat) (source : Evm fork Meter → ByteArray)
    (hsource : ∀ evm hs, source (frameWithHashes hs evm) = source evm) :
    HashFree (fun evm => copyToMemory base (source evm) evm) := by
  intro evm hs; simp only [copyToMemory, hsource]; hash_free

theorem returndatacopyStep_hashFree :
    HashFree (returndatacopyStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [returndatacopyStep]; hash_free

theorem returnStep_hashFree : HashFree (returnStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [returnStep, haltWithOutput]; hash_free

theorem revertStep_hashFree : HashFree (revertStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [revertStep, haltWithOutput]; hash_free

theorem blobhashStep_hashFree (h : .dencun ≤ fork) :
    HashFree (blobhashStep (Meter := Meter) h) := by
  intro evm hs; simp only [blobhashStep]; hash_free

theorem logStep_hashFree (n : Nat) : HashFree (logStep (fork := fork) (Meter := Meter) n) := by
  intro evm hs; simp only [logStep]; hash_free

theorem balanceStep_hashFree : HashFree (balanceStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [balanceStep]; hash_free

theorem extcodesizeStep_hashFree : HashFree (extcodesizeStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [extcodesizeStep]; hash_free

theorem extcodecopyStep_hashFree : HashFree (extcodecopyStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [extcodecopyStep]; hash_free

theorem extcodehashStep_hashFree : HashFree (extcodehashStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [extcodehashStep]; hash_free

theorem sloadStep_hashFree : HashFree (sloadStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [sloadStep]; hash_free

theorem tloadStep_hashFree : HashFree (tloadStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [tloadStep]; hash_free

theorem tstoreStep_hashFree : HashFree (tstoreStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [tstoreStep]; hash_free

theorem sstoreStep_hashFree : HashFree (sstoreStep (fork := fork) (Meter := Meter)) := by
  intro evm hs; simp only [sstoreStep]; hash_free

theorem finishSelfdestruct_hashFree (b : Address) (r : Nat) :
    HashFree (finishSelfdestruct (Meter := Meter) fork b r) := by
  intro evm hs; simp only [finishSelfdestruct]; hash_free

theorem selfdestructStep_hashFree : HashFree (selfdestructStep (Meter := Meter) fork) := by
  intro evm hs; simp only [selfdestructStep]; hash_free
  all_goals exact finishSelfdestruct_hashFree _ _ _ _

/-! ## BLOCKHASH -/

/-- BLOCKHASH moves the replacement through when both lists give the same hash for the number on
top of the stack. -/
theorem blockhashStep_withHashes (evm : Evm fork Meter) (hs : List Hash32)
    (hb : ∀ w rest, evm.stack.val = w :: rest →
      blockHash hs evm.message.blockEnv.number w.toNat =
        blockHash evm.message.blockEnv.blockHashes evm.message.blockEnv.number w.toNat) :
    blockhashStep (frameWithHashes hs evm) = frameWithHashes hs <$> blockhashStep evm := by
  simp only [blockhashStep]
  rcases hst : evm.stack with ⟨_ | ⟨w, rest⟩, hlen⟩
  · simp [popWord, frameWithHashes, hst, Stack.pop, bind, Except.bind, Functor.map, Except.map]
  · have hw := hb w rest (by rw [hst])
    simp only [popWord, chargeGas, pushWord, frameWithHashes, hst, Stack.pop, bind, Except.bind,
      pure, Except.pure]
    cases GasMeter.charge evm.gas GasCosts.OPCODE_BLOCKHASH with
    | error e => rfl
    | ok g =>
      simp only [Message.withHashes]
      rw [hw]
      cases Stack.push _ _ <;> rfl

/-! ## The instructions but BLOCKHASH -/

theorem stackOnlyStep_hashFree {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) : HashFree run := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact unaryOp_hashFree _ _
    | with_reducible exact binaryOp_hashFree _ _
    | with_reducible exact ternaryOp_hashFree _ _
    | with_reducible exact expStep_hashFree
    | with_reducible exact keccak256Step_hashFree
    | with_reducible exact popStep_hashFree
    | with_reducible exact pushN_hashFree _
    | with_reducible exact dupN_hashFree _
    | with_reducible exact swapN_hashFree _
    | with_reducible exact dupnStep_hashFree
    | with_reducible exact swapnStep_hashFree
    | with_reducible exact exchangeStep_hashFree

theorem controlFlowStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) : HashFree run := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  · exact stopStep_hashFree
  · exact jumpStep_hashFree
  · exact jumpiStep_hashFree
  · exact readFrame_hashFree _ _ fun _ _ => rfl
  · exact readFrame_hashFree _ _ fun _ _ => rfl
  · exact jumpdestStep_hashFree

theorem memoryDataStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) : HashFree run := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  all_goals first
    | with_reducible exact mloadStep_hashFree
    | with_reducible exact mstoreStep_hashFree
    | with_reducible exact mstore8Step_hashFree
    | with_reducible exact mcopyStep_hashFree
    | with_reducible exact calldataloadStep_hashFree
    | with_reducible exact returndatacopyStep_hashFree
    | with_reducible exact readFrame_hashFree _ _ fun _ _ => rfl
    | with_reducible exact copyToMemory_hashFree _ (fun evm => evm.message.data) fun _ _ => rfl
    | with_reducible exact copyToMemory_hashFree _ (fun evm => evm.code) fun _ _ => rfl

theorem returnOpStep_hashFree {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) : HashFree run := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  · subst hstep
    exact returnStep_hashFree
  · split at hstep
    · cases hstep
      exact revertStep_hashFree
    · cases hstep

theorem environmentStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) (hne : op ≠ .blockhash) : HashFree run := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | exact absurd rfl hne
    | with_reducible exact blobhashStep_hashFree _
    | with_reducible exact readFrame_hashFree _ _ fun _ _ => rfl

theorem accountStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) : HashFree run := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact balanceStep_hashFree
    | with_reducible exact extcodesizeStep_hashFree
    | with_reducible exact extcodecopyStep_hashFree
    | with_reducible exact extcodehashStep_hashFree
    | (intro evm hs
       exact readFrame_hashFree _ _ (fun _ _ => rfl) (recordAccountRead evm _) hs)

theorem storageStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) : HashFree run := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  · exact sloadStep_hashFree
  · exact sstoreStep_hashFree

theorem transientStorageStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) : HashFree run := by
  cases op <;> simp only [transientStorageStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (split at hstep <;> simp only [Option.some.injEq, reduceCtorEq] at hstep)
  · subst hstep; exact tloadStep_hashFree
  · subst hstep; exact tstoreStep_hashFree

theorem logOpStep_hashFree {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) : HashFree run := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact logStep_hashFree _

theorem selfdestructOpStep_hashFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) : HashFree run := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact selfdestructStep_hashFree

/-- Every instruction of the dispatch but BLOCKHASH moves the replacement through. -/
theorem instruction_hashFree {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) (hne : op ≠ .blockhash) : HashFree run := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact stackOnlyStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact controlFlowStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact memoryDataStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact returnOpStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact environmentStep_hashFree hf hne
  rcases orElse_eq_some hrun with hf | hrun
  · exact accountStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact storageStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact transientStorageStep_hashFree hf
  rcases orElse_eq_some hrun with hf | hf
  · exact logOpStep_hashFree hf
  · exact selfdestructOpStep_hashFree hf

/-! ## Calls and creations -/

theorem resumeCall_withHashes (hs : List Hash32) (c : Evm fork Meter) (n : Nat) (a b : U256) :
    resumeCall fork (frameWithHashes hs c) n a b =
      fun ch => frameWithHashes hs <$> resumeCall fork c n a b ch := by
  funext ch; simp only [resumeCall]; hash_free

theorem resumeCreate_withHashes (hs : List Hash32) (c : Evm fork Meter) (n : Nat) (a : Address) :
    resumeCreate fork (frameWithHashes hs c) n a =
      fun ch => frameWithHashes hs <$> resumeCreate fork c n a ch := by
  funext ch; simp only [resumeCreate]; hash_free

theorem popCallOperands_withHashes (hs : List Hash32) (kind : CallKind) (e : Evm fork Meter) :
    popCallOperands kind (frameWithHashes hs e) =
      (fun p => (p.1, frameWithHashes hs p.2)) <$> popCallOperands kind e := by
  simp only [popCallOperands, popCallValue]; hash_free

theorem accessDelegation_withHashes (hs : List Hash32) (e : Evm fork Meter) (a : Address) (k : Nat) :
    accessDelegation (frameWithHashes hs e) a k =
      (fun p => (p.1, frameWithHashes hs p.2)) <$> accessDelegation e a k := by
  simp only [accessDelegation]; hash_free

theorem payCall_withHashes (hs : List Hash32) (kind : CallKind) (call : CallOperands)
    (m x n : Nat) (e : Evm fork Meter) :
    payCall kind call m x n (frameWithHashes hs e) =
      (fun p => (p.1, frameWithHashes hs p.2)) <$> payCall kind call m x n e := by
  simp only [payCall]; hash_free

theorem finishCall_withHashes (hs : List Hash32) (kind : CallKind) (call : CallOperands)
    (callee : Callee) (sub n x : Nat) (e : Evm fork Meter) :
    finishCall kind call callee sub n x (frameWithHashes hs e) =
      StepResult.withHashes hs <$> finishCall kind call callee sub n x e := by
  simp only [finishCall, genericCall, resumeCall_withHashes]; hash_free
  all_goals (simp only [resumeCall_withHashes, StepResult.withHashes_child, map_pure]; rfl)

theorem callStep_withHashes (hs : List Hash32) (kind : CallKind) (e : Evm fork Meter) :
    callStep kind (frameWithHashes hs e) = StepResult.withHashes hs <$> callStep kind e := by
  simp only [callStep]
  repeat (first | hash_simp | simp only [popCallOperands_withHashes, accessDelegation_withHashes,
    payCall_withHashes, finishCall_withHashes])
  hash_free

theorem popSalt_withHashes (hs : List Hash32) (c : Bool) (e : Evm fork Meter) :
    popSalt c (frameWithHashes hs e) = (fun p => (p.1, frameWithHashes hs p.2)) <$> popSalt c e := by
  simp only [popSalt]; hash_free

theorem launchCreate_withHashes (hs : List Hash32) (e : Evm fork Meter) (v : U256) (code : ByteArray)
    (salt : Option U256) :
    launchCreate (frameWithHashes hs e) v code salt =
      StepResult.withHashes hs <$> launchCreate e v code salt := by
  simp only [launchCreate, resumeCreate_withHashes]; hash_free
  all_goals (simp only [resumeCreate_withHashes, StepResult.withHashes_child, map_pure]; rfl)

theorem createStep_withHashes (hs : List Hash32) (c : Bool) (e : Evm fork Meter) :
    createStep c (frameWithHashes hs e) = StepResult.withHashes hs <$> createStep c e := by
  simp only [createStep, genericCreate]
  repeat (first | hash_simp | simp only [popSalt_withHashes, launchCreate_withHashes])
  hash_free

/-- Calls and creations move the replacement through: a message they send gets the hashes, and the
frame that resumes gets them too. -/
theorem messageInstruction_withHashes {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) (e : Evm fork Meter) (hs : List Hash32) :
    run (frameWithHashes hs e) = StepResult.withHashes hs <$> run e := by
  unfold messageInstruction at hrun
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hf
    all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf)
    all_goals (subst hf; exact callStep_withHashes _ _ _)
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hf
    all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf)
    all_goals (subst hf; exact createStep_withHashes _ _ _)


/-! ## The parts of a message -/

theorem precompileAddress_withHashes (hs : List Hash32) (m : Message fork) :
    precompileAddress fork (Message.withHashes hs m) = precompileAddress fork m := rfl

theorem runPrecompile_withHashes (hs : List Hash32) (a : Nat) (e : Evm fork Meter) :
    runPrecompile fork a (frameWithHashes hs e) = (frameWithHashes hs) <$> runPrecompile fork a e := by
  unfold runPrecompile
  simp only [fwh_message, mwh_data, fwh_gas]
  split
  · rfl
  · rfl
  · split <;> rfl

theorem rollbackOnError_withHashes (hs : List Hash32) (st : EthLib.Execution.State.TransactionState)
    (e : Evm fork Meter) :
    rollbackOnError st (frameWithHashes hs e) = frameWithHashes hs (rollbackOnError st e) := by
  unfold rollbackOnError
  by_cases h : e.error.isSome = true
  · rw [if_pos (show (frameWithHashes hs e).error.isSome = true from h), if_pos h]; rfl
  · rw [if_neg (show ¬(frameWithHashes hs e).error.isSome = true from h), if_neg h]

theorem depositCode_withHashes (hs : List Hash32) (st : EthLib.Execution.State.TransactionState)
    (e : Evm fork Meter) :
    depositCode fork st (frameWithHashes hs e) = frameWithHashes hs <$> depositCode fork st e := by
  simp only [depositCode]; hash_free

/-! ## A step -/

/-- The frame's next step is no BLOCKHASH that the two lists answer differently: when it runs
BLOCKHASH on a number, the hashes `hs` give the same word for it as the frame's own. -/
def BlockhashAgrees (hs : List Hash32) (evm : Evm fork Meter) : Prop :=
  ∀ (h : evm.pc < evm.code.size), Op.ofByte fork evm.code[evm.pc] = some .blockhash →
    ∀ w rest, evm.stack.val = w :: rest →
      blockHash hs evm.message.blockEnv.number w.toNat =
        blockHash evm.message.blockEnv.blockHashes evm.message.blockEnv.number w.toNat

/-- **A step moves the replacement through**, unless it is a BLOCKHASH the two lists answer
differently. -/
theorem step_withHashes (evm : Evm fork Meter) (hs : List Hash32) (hb : BlockhashAgrees hs evm) :
    step fork (frameWithHashes hs evm) = StepResult.withHashes hs <$> step fork evm := by
  unfold step
  by_cases hpc : evm.pc < evm.code.size
  · have hpc' : (frameWithHashes hs evm).pc < (frameWithHashes hs evm).code.size := hpc
    rw [dif_pos hpc', dif_pos hpc]
    have hbyte : (frameWithHashes hs evm).code[(frameWithHashes hs evm).pc]'hpc' =
        evm.code[evm.pc]'hpc := rfl
    rw [hbyte]
    dsimp only
    cases hop : Op.ofByte fork evm.code[evm.pc] with
    | none => rfl
    | some op =>
      dsimp only
      by_cases hbh : op = .blockhash
      · subst hbh
        have hb' := hb hpc hop
        simp only [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
          environmentStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]
        rw [blockhashStep_withHashes _ hs hb', Functor.map_map, Functor.map_map]
        rfl
      · cases hrun : instruction (Meter := Meter) fork op with
        | some run =>
          dsimp only
          rw [instruction_hashFree hrun hbh _ hs, Functor.map_map, Functor.map_map]
          rfl
        | none =>
          dsimp only
          cases hmsg : messageInstruction (Meter := Meter) fork op with
          | some run => exact messageInstruction_withHashes hmsg _ hs
          | none => rfl
  · have hpc' : ¬(frameWithHashes hs evm).pc < (frameWithHashes hs evm).code.size := hpc
    rw [dif_neg hpc', dif_neg hpc, stopStep_hashFree _ hs, Functor.map_map, Functor.map_map]
    rfl

end LeanLightEvmProofs.Hashes

namespace LeanLightEvmProofs.Hashes
open EthLib.Base (Fork U256 Hash32 Address)
open EthLib.Execution.Evm
variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A message a step sends runs in its caller's block -/

omit [GasMeter Meter] in
theorem next_map_ne_child (x : Except EvmError (Evm fork Meter)) (c : Evm fork Meter)
    (m : Message fork) (r : Evm fork Meter → Except EvmError (Evm fork Meter)) :
    (StepResult.next <$> x) ≠ .ok (.child c m r) := by
  cases x <;> simp [Functor.map, Except.map]

theorem keepReads_child {e c : Evm fork Meter} {x : Except EvmError (StepResult fork Meter)}
    {m : Message fork} {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : keepReads e StepResult.next x = .ok (.child c m r)) : x = .ok (.child c m r) := by
  unfold keepReads at h
  split at h
  · split at h <;> cases h
  · exact h

theorem finishCall_child {kind : CallKind} {call : CallOperands} {callee : Callee}
    {sub n x : Nat} {e c : Evm fork Meter} {m : Message fork}
    {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : finishCall kind call callee sub n x e = .ok (.child c m r)) :
    m.blockEnv = c.message.blockEnv := by
  unfold finishCall genericCall at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · exact absurd h (next_map_ne_child _ _ _ _)
  split at h
  · exact absurd h (next_map_ne_child _ _ _ _)
  cases h
  rfl

theorem callStep_child {kind : CallKind} {e c : Evm fork Meter} {m : Message fork}
    {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind e = .ok (.child c m r)) : m.blockEnv = c.message.blockEnv := by
  unfold callStep at h
  simp only [bind, Except.bind] at h
  repeat' (first
    | (cases h; done)
    | exact finishCall_child h
    | (replace h := keepReads_child h)
    | (split at h))


theorem launchCreate_child {e c : Evm fork Meter} {v : U256} {code : ByteArray}
    {salt : Option U256} {m : Message fork} {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : launchCreate e v code salt = .ok (.child c m r)) : m.blockEnv = c.message.blockEnv := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · exact absurd h (next_map_ne_child _ _ _ _)
  simp only [bind, Except.bind] at h
  repeat' (first
    | (cases h; done)
    | (cases h; rfl)
    | (replace h := keepReads_child h)
    | (split at h))

theorem createStep_child {c2 : Bool} {e c : Evm fork Meter} {m : Message fork}
    {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : createStep c2 e = .ok (.child c m r)) : m.blockEnv = c.message.blockEnv := by
  unfold createStep genericCreate at h
  simp only [bind, Except.bind] at h
  repeat' (first
    | (cases h; done)
    | exact launchCreate_child h
    | (split at h))

theorem messageInstruction_child {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) {e c : Evm fork Meter} {m : Message fork}
    {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : run e = .ok (.child c m r)) : m.blockEnv = c.message.blockEnv := by
  unfold messageInstruction at hrun
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hf
    all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf)
    all_goals (subst hf; exact callStep_child h)
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hf
    all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf)
    all_goals (subst hf; exact createStep_child h)

/-- A message that a step sends has its caller's block. -/
theorem step_child {e c : Evm fork Meter} {m : Message fork}
    {r : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork e = .ok (.child c m r)) : m.blockEnv = c.message.blockEnv := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · exact absurd h (next_map_ne_child _ _ _ _)
      · split at h
        · rename_i hcall
          exact messageInstruction_child hcall h
        · cases h
  · exact absurd h (next_map_ne_child _ _ _ _)

end LeanLightEvmProofs.Hashes
