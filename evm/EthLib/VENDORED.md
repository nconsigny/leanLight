# EthLib, vendored

This directory holds files from [github.com/ethereum/EthLib](https://github.com/ethereum/EthLib)
at the commit named in `PIN` (`230e355b`), the one place the pin is recorded. EthLib's authors
dedicated them to the public domain under CC0-1.0; `LICENSE` is upstream's, unchanged. Every
`.lean` file is upstream's, byte for byte, at its upstream path, so the module names are
EthLib's (`EthLib.*`) and no file is rewritten. Only `PIN`, `RUNTIME`, `PROOFS`, `SHA256SUMS`
and this file are leanLight's.

## What is here

Two import closures, listed in `RUNTIME` and `PROOFS`:

- **The EVM** (137 modules, `RUNTIME`): the import closure of
  `EthLib.Execution.Transactions.Process`, so transaction processing, the interpreter, every
  precompile, the state, RLP, and the hashes and curves those use. It is what `LeanLightEvm`
  runs, built by the library `EthLibEvm` of `evm/lakefile.lean`. Beyond Lean core's `Init` it
  imports only `Std.Data.ExtTreeMap` and `Std.Data.ExtTreeSet`.
- **EthLib's proofs** (74 modules, `PROOFS`): the import closure of the noninterference theorems
  `LeanLightEvmProofs` builds on (`processMessageCall_agrees`, `processMessageCallWith_modify`,
  the covering sets and the `incrementNonce` lemmas; `PROOF_ROOTS` in
  `evm/scripts/vendor-ethlib.py`), less the EVM's own modules. Every one is a proof module
  (`EthLib.*.Proofs.*`), built by the library `EthLibProofs` (upstream's default
  `autoImplicit`), which nothing at runtime imports. Their imports beyond the EVM are again
  only `Init` and the two `Std` tree maps: no Mathlib.

Both closures sit in one tree, so one build directory holds every `EthLib` module and
`lake env lean` finds them all; the two libraries' globs keep them apart (`EthLibEvm` names the
EVM's directories one by one, `EthLibProofs` the two `Proofs` directories).

The precompiles nothing in leanLight calls on purpose (KZG point evaluation, EIP-2537's
BLS12-381, P256 verification) are kept: removing them would edit upstream's precompile table, and
a call that reaches one would then run as a call to an empty account and disagree with the chain
instead of being answered or refused. They are about a third of the library's object code.
`Cryptography/Kzg/TrustedSetupData.lean` raises `maxRecDepth` and `maxHeartbeats` for its own
elaboration.

## Regenerating and checking

```sh
evm/scripts/vendor-ethlib.py --sums             # offline: every file matches SHA256SUMS, none extra
evm/scripts/vendor-ethlib.py --check CHECKOUT   # the tree is exactly what the pin gives
evm/scripts/vendor-ethlib.py CHECKOUT           # rewrite the tree, RUNTIME, PROOFS and SHA256SUMS
```

`CHECKOUT` is a git checkout of EthLib that holds the pinned commit. The script reads every file
from git's objects at that commit (`git cat-file`), never from the working tree, and runs nothing
of the checkout. To bump the pin: edit `PIN`, run the script, review the diff of this directory,
and rerun `evm/scripts/check-runtime.sh` and the proofs (`evm/proofs`).

## Why not `require` EthLib

EthLib's package requires Mathlib and builds its RPC layer on `Lean.Json`; its EVM does not.
Vendoring the EVM's own closure keeps `leanlight-evm` free of Mathlib, pins exactly the code that
runs, and lets `evm/scripts/check-runtime.sh` audit every line of it.
