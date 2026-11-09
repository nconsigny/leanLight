import Lake
open Lake DSL

/-!
The tests, run as executables: BLS12-381's vectors and differential tests against EthLib's
readable layer (`leanlight-bls-test`), SSZ's (`leanlight-ssz-test`) and the store's against
consensus-specs' minimal-preset light-client vectors (`leanlight-store-test`, with the minimal
preset's decoders and a development chain table, `LeanLightDev`). A package of its own requiring
only `LeanLight`, so nothing of Mathlib is compiled into the executables. EthLib's readable layer
is compiled here again from `proofs/` (it imports nothing beyond Lean core and SHA-256).
-/

package «leanlight-tests» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanlight from ".."

/-- EthLib's BLS12-381, vendored into the proofs as the readable specification. -/
lean_lib EthLibBls where
  srcDir := "../proofs"
  globs := #[.submodules `LeanLightProofs.Vendor.EthLib]

/-- consensus-specs' sync protocol transcribed (`LeanLightProofs.Spec.SyncProtocol`, Lean core
and `LeanLight` only), run on the `sync` vectors beside the store. -/
lean_lib LeanLightSpec where
  srcDir := "../proofs"
  globs := #[.one `LeanLightProofs.Spec.SyncProtocol]

/-- The minimal preset's decoders and a development chain table (tests only). -/
lean_lib LeanLightDev

lean_lib LeanLightTests where
  globs := #[.submodules `LeanLightTests]

/-- `lake exe leanlight-bls-test` (`--quick`: no timings). -/
@[default_target] lean_exe «leanlight-bls-test» where
  root := `LeanLightTests.Bls

/-- `lake exe leanlight-ssz-test`: `LeanLight.Ssz` against consensus-specs' SSZ vectors. -/
@[default_target] lean_exe «leanlight-ssz-test» where
  root := `LeanLightTests.Ssz

/-- `lake exe leanlight-store-test`: `LeanLight.Store` against consensus-specs' light-client vectors. -/
@[default_target] lean_exe «leanlight-store-test» where
  root := `LeanLightTests.StoreMain

/-- `lake exe leanlight-committee-bench`: where taking in a committee spends its time. -/
@[default_target] lean_exe «leanlight-committee-bench» where
  root := `LeanLightTests.CommitteeBench

/-- `lake exe leanlight-client-test`: the client's decisions (`LeanLight.Driver`) on recorded
mainnet runs (`fixtures/`), offline: the honest run, and forgeries refused. -/
@[default_target] lean_exe «leanlight-client-test» where
  root := `LeanLightTests.ClientMain

/-- `lake exe leanlight-bench`: what verifying costs, offline, on the recorded runs. -/
@[default_target] lean_exe «leanlight-bench» where
  root := `LeanLightTests.BenchMain
