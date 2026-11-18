#!/usr/bin/env bash
# Replays every module of LeanLightEvm, the vendored EthLib (the EVM and its proofs) and
# LeanLightEvmProofs through Lean's kernel, one module at a time, with leanLight's replay
# (scripts/CheckKernel.lean), so a proof accepted with the kernel skipped fails here. Run after
# `lake build` in evm/proofs. LEANLIGHT_KERNEL_JOBS sets the parallelism (default 4).
set -euo pipefail
evm=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$evm/.." && pwd)
cd "$evm/proofs"
jobs=${LEANLIGHT_KERNEL_JOBS:-4}

if grep -rnE 'set_option[[:space:]]+debug\.|skipKernelTC' --include='*.lean' \
    "$evm/LeanLightEvm" "$evm/EthLib" "$evm/proofs/LeanLightEvmProofs"; then
  echo "error: a debug option above can let a false proof past the kernel; none is allowed" >&2
  exit 1
fi

modules=$(
  { cat "$evm/EthLib/RUNTIME" "$evm/EthLib/PROOFS"
    (cd "$evm" && find LeanLightEvm -name '*.lean' && echo LeanLightEvm.lean) | sed 's/\.lean$//; s|/|.|g'
    find LeanLightEvmProofs -name '*.lean' | sed 's/\.lean$//; s|/|.|g'; echo LeanLightEvmProofs; }
)
leanpath=$(lake env printenv LEAN_PATH)
count=$(sort -u <<<"$modules" | wc -l)
start=$(date +%s)
if ! sort -u <<<"$modules" | LEAN_PATH=$leanpath xargs -P "$jobs" -n 16 lean --run "$root/scripts/CheckKernel.lean"; then
  echo "error: the kernel refused a module above" >&2
  exit 1
fi
echo "evm kernel replay passed: $count modules in $(($(date +%s) - start)) s"
