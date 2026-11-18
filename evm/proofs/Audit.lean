import LeanLightEvmProofs
import Lean

/-!
The axiom audit of leanlight-evm, run by `evm/scripts/check-axioms.sh`: every constant declared
in a module of `LeanLightEvm`, `LeanLightEvmProofs` or the vendored `EthLib` (the EVM and
EthLib's proofs), theorem or definition, may rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). A `sorry` (`sorryAx`), `native_decide`
(`Lean.ofReduceBool`) or any new axiom fails it. Nothing is listed by hand, so a new theorem
cannot be left out; the headline theorems are printed below as well.

It also fails if the environment holds a module of `LeanLightProofs.Vendor` (EthLib's
BLS12-381 at leanLight's other pin, whose declarations clash with the EVM's): the proofs here
import only modules of `leanlight-proofs` whose closure has none.
-/

open Lean Elab Command

elab "#audit_leanlight_evm" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List Name := [`LeanLightEvm, `LeanLightEvmProofs, `EthLib]
  for m in env.header.moduleNames do
    if (`LeanLightProofs.Vendor).isPrefixOf m then
      logError m!"{m} is in the environment: the EVM's proofs must not import leanLight's vendored EthLib"
  let mut checked := 0
  let mut theorems := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (nm, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? nm | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless roots.contains m.getRoot do continue
    if nm.isInternal then continue
    checked := checked + 1
    if ci matches .thmInfo _ then theorems := theorems + 1
    let axs ← liftCoreM (Lean.collectAxioms nm)
    let extra := axs.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do bad := bad.push (nm, extra)
  for (nm, axs) in bad do
    logError m!"{nm} depends on {axs}"
  logInfo m!"audited {checked} constants ({theorems} theorems): {bad.size} outside the allowed axioms"

#audit_leanlight_evm

-- The agreement of `LeanLightEvm.call` with the plain run (`LeanLightEvm.CallAgrees`).
#print axioms LeanLightEvmProofs.call_agrees
#print axioms LeanLightEvmProofs.Hashes.hashesSuffice
#print axioms LeanLightEvmProofs.call_answers_held
#print axioms LeanLightEvmProofs.call_refuses
-- The composition with the light client (`LeanLightEvmProofs/Driver.lean`).
#print axioms LeanLightEvmProofs.Driver.reaches_run_agrees
#print axioms LeanLightEvmProofs.Driver.run_agrees
#print axioms LeanLightEvmProofs.Driver.inputAt_agrees
#print axioms LeanLightEvmProofs.Driver.factsAt_holdIn
#print axioms LeanLightEvmProofs.Driver.ancestorsOf_spec
#print axioms LeanLightEvmProofs.Driver.represents_empty
-- EthLib's theorems at the pin that it rests on.
#print axioms EthLib.Execution.Transactions.processMessageCall_agrees
#print axioms EthLib.Execution.Transactions.processMessageCallWith_modify
