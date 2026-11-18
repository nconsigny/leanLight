import Lake
open Lake DSL

/-!
leanlight-evm: local `eth_call` over leanLight, opt-in. A package of its own, so that a consumer
who requires `leanlight` alone never fetches or builds the EVM. A consumer opts in with

    require «leanlight-evm» from git "https://github.com/nconsigny/leanLight" @ "<rev>" / "evm"

* `LeanLightEvm`: the checked entry (`LeanLightEvm.call`), the chain table, and the driver over
  leanLight's store and readers (`LeanLightEvm.Driver`). Its import closure is Lean core, `Std`'s
  two tree maps (`Std.Data.ExtTreeMap`, `Std.Data.ExtTreeSet`, which EthLib's state uses),
  EthLib's EVM vendored in `EthLib/` and `LeanLight` (`scripts/check-runtime.sh` checks it).
* `EthLibEvm`: EthLib's EVM, vendored unedited (`EthLib/VENDORED.md`, CC0-1.0), the import
  closure of its transaction processing.
* `EthLibProofs`: EthLib's proofs that `LeanLightEvm`'s theorems build on (`proofs/`), vendored
  the same way. Not a default target: nothing runtime imports it.
* `leanlight-evm`: the command-line client (`call`, `estimate`) over `LeanLightCli`'s fetching.
-/

package «leanlight-evm» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require leanlight from ".."

/-- EthLib's EVM, the import closure of `EthLib.Execution.Transactions.Process` (`EthLib/RUNTIME`
lists it). The globs name its directories one by one, never `EthLib.*` as a whole, so that the
proof modules belong to `EthLibProofs` alone. -/
lean_lib EthLibEvm where
  roots := #[]
  globs := #[
    .one `EthLib.Base.Address, .one `EthLib.Base.BigEndian, .one `EthLib.Base.BlobSchedule,
    .one `EthLib.Base.Bytes, .one `EthLib.Base.ChainConfig, .one `EthLib.Base.Except,
    .one `EthLib.Base.Fork, .one `EthLib.Base.Hash32, .one `EthLib.Base.U256,
    .submodules `EthLib.Cryptography, .submodules `EthLib.Execution.Evm,
    .submodules `EthLib.Execution.Fees, .submodules `EthLib.Execution.State,
    .submodules `EthLib.Execution.Transactions, .submodules `EthLib.Execution.Trie,
    .submodules `EthLib.Serialization]

/-- EthLib's proofs at the same pin (`EthLib/PROOFS` lists them), with upstream's default
`autoImplicit`, as EthLib builds these files. -/
lean_lib EthLibProofs where
  roots := #[]
  globs := #[.submodules `EthLib.Base.Proofs, .submodules `EthLib.Execution.Proofs]
  leanOptions := #[⟨`autoImplicit, true⟩]

/-- The checked `eth_call`, its chain table and its driver over leanLight. -/
@[default_target] lean_lib LeanLightEvm where
  libName := "leanlightevm"

/-- The command-line client's EVM commands. -/
lean_lib LeanLightEvmCli

/-- `leanlight-evm`: sync as `leanlight` does, then `call` or `estimate` at the anchored block. -/
@[default_target] lean_exe «leanlight-evm» where
  root := `EvmMain

/-- The tests' modules. -/
lean_lib LeanLightEvmTests where
  globs := #[.submodules `LeanLightEvmTests]

/-- `lake exe leanlight-evm-test [--quick]`, run from `evm/`: recorded mainnet and Sepolia calls
(`tests/vectors`), their sweeps, the proof-backed tier through leanLight's readers, synthetic
worlds against `LeanLightEvm.reference`, and cases built to be refused. -/
lean_exe «leanlight-evm-test» where
  root := `LeanLightEvmTests.Main
