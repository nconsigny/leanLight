import Lake
open Lake DSL

/-!
leanlight-evm-proofs: the theorems about `LeanLightEvm` (`evm/`), and the part of EthLib's proofs
they build on (vendored in `evm/EthLib` with the EVM, the library `EthLibProofs` of
`leanlight-evm`).

* `LeanLightEvmProofs.call_agrees`: an answer of `LeanLightEvm.call` is the plain run's on every
  full state the facts hold in (`LeanLightEvm.CallAgrees`).
* `LeanLightEvmProofs.Driver.reaches_run_agrees`: an answer `LeanLightEvm.Driver.run` gives at a
  store the client reached is the plain run's on every state that represents the world state
  with the anchored header's state root, short of a Keccak-256 collision on named bytes:
  `call_agrees` composed with leanLight's readers (`Anchor.bind`, `Facts.storageAt`, the trie's
  soundness) and its store theorems (`reaches_anchored`).

It requires `leanlight-proofs` for those theorems, and so Mathlib, but imports only modules of it
whose closure holds none of `LeanLightProofs.Vendor` (EthLib's BLS12-381 at another pin, whose
names clash with the EVM's); `Audit.lean` (`../scripts/check-axioms.sh`) checks that.
-/

package «leanlight-evm-proofs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «leanlight-evm» from ".."

require «leanlight-proofs» from ".." / ".." / "proofs"

/-- The theorems about `LeanLightEvm`. -/
@[default_target] lean_lib LeanLightEvmProofs where
  globs := #[.andSubmodules `LeanLightEvmProofs]
