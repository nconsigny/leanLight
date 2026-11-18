#!/usr/bin/env bash
# Fails if any constant of LeanLightEvm, LeanLightEvmProofs or the vendored EthLib (the EVM and
# EthLib's proofs) rests on `sorry`, `native_decide` or an axiom beyond propext,
# Classical.choice and Quot.sound, or if the proofs import leanLight's vendored EthLib BLS
# (evm/proofs/Audit.lean). Also refuses words that add no constant the audit could see (a
# `sorry` in an `example`) or that change what the kernel is shown, in the proofs' sources.
set -euo pipefail
cd "$(dirname "$0")/../proofs"
words='\b(sorry|admit|native_decide|ofReduceBool|ofReduceNat|trustCompiler|axiom|implemented_by|extern|unsafe|opaque|run_cmd|initialize)\b|decide +\+native|set_option +debug\.|skipKernelTC'
if grep -rnE --include='*.lean' "$words" LeanLightEvmProofs LeanLightEvmProofs.lean; then
  echo "error: a word above is not allowed in evm/proofs' sources" >&2
  exit 1
fi
lake build >/dev/null
out=$(lake env lean Audit.lean 2>&1) || { echo "$out"; exit 1; }
echo "$out"
grep -q ': 0 outside the allowed axioms' <<<"$out" || { echo "error: axiom audit failed" >&2; exit 1; }
echo "evm axiom check passed"
