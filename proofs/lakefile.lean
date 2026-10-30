import Lake
open Lake DSL

/-!
The proofs about `LeanLight`: the runtime code is stated against readable specifications
(`LeanLightProofs.Spec`, the vendored ssz-specs, EthLib's BLS and VCVio's SHA-2 and Keccak) and
proved equal or sound. Mathlib is required here only; the runtime package imports nothing beyond
Lean core.
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

require leanlight from ".."

package «leanlight-proofs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target] lean_lib LeanLightProofs
