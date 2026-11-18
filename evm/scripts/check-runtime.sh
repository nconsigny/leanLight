#!/usr/bin/env bash
# The runtime rule of leanlight-evm, as scripts/check-runtime.sh is leanLight's: fails if the code
# the library LeanLightEvm runs could run something its proofs are not about, or imports beyond
# what the README admits. Run from anywhere; builds LeanLightEvm first.
#
# 1. EthLib's vendored files are upstream's at the pin (evm/EthLib/SHA256SUMS, offline).
# 2. The import closure of LeanLightEvm (Lean's own, scripts/Closure.lean) holds only Init, the
#    Std modules that Std.Data.ExtTreeMap and Std.Data.ExtTreeSet pull in, the EVM's EthLib
#    modules (EthLib/RUNTIME, none of EthLib's proofs), LeanLight and LeanLightEvm; and every
#    file under LeanLightEvm/ is in it.
# 3. No `@[implemented_by]`, `@[extern]`, `opaque`, `unsafe` or `partial` at the start of a line,
#    and no `sorry`, `admit`, `native_decide`, `axiom` or `debug.` option, in LeanLightEvm/ or in
#    the vendored EthLib modules of that closure (the words anywhere, comments included). Std,
#    like Lean core, is the toolchain's and trusted: it is not scanned. The axiom audit
#    (check-axioms.sh) covers the constants.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
cd "$here"

python3 -I scripts/vendor-ethlib.py --sums

lake build LeanLightEvm >/dev/null
closure=$(lake env lean --run scripts/Closure.lean LeanLightEvm)
stdAllowed=$(lake env lean --run scripts/Closure.lean Std.Data.ExtTreeMap Std.Data.ExtTreeSet | grep '^Std\.' || true)

bad=$(grep -vE '^(Init|EthLib|LeanLight|LeanLightEvm|Std)(\.|$)' <<<"$closure" || true)
if [ -n "$bad" ]; then
  echo "$bad"
  echo "error: LeanLightEvm imports modules outside Init, Std's tree maps, EthLib and LeanLight" >&2
  exit 1
fi
stdBad=$(comm -23 <(grep '^Std\.' <<<"$closure" | sort -u) <(sort -u <<<"$stdAllowed"))
if [ -n "$stdBad" ]; then
  echo "$stdBad"
  echo "error: LeanLightEvm imports Std modules beyond Std.Data.ExtTreeMap and ExtTreeSet's closure" >&2
  exit 1
fi
ethBad=$(comm -23 <(grep '^EthLib\.' <<<"$closure" | sort -u) <(sort -u EthLib/RUNTIME))
if [ -n "$ethBad" ]; then
  echo "$ethBad"
  echo "error: LeanLightEvm imports EthLib modules outside the vendored EVM (EthLib/RUNTIME)" >&2
  exit 1
fi
onDisk=$(find LeanLightEvm -name '*.lean' | sed 's/\.lean$//; s|/|.|g'; echo LeanLightEvm)
stray=$(comm -23 <(sort -u <<<"$onDisk") <(grep -E '^LeanLightEvm(\.|$)' <<<"$closure" | sort -u))
if [ -n "$stray" ]; then
  echo "$stray"
  echo "error: files under LeanLightEvm/ outside the library's import closure" >&2
  exit 1
fi

files=$( (find LeanLightEvm -name '*.lean'; echo LeanLightEvm.lean
          grep -E '^EthLib\.' <<<"$closure" | sed 's|^EthLib\.||; s|\.|/|g; s|^|EthLib/|; s|$|.lean|') | sort -u)
# Matches at the start of a line only: prose in comments naming the attributes is not code.
bad=$(xargs grep -nE '^\s*(@\[(implemented_by|extern)|(private |protected |noncomputable )*(opaque|unsafe|partial) )' <<<"$files" || true)
# Anywhere, comments included (none of these files names one): reword a comment rather than widen.
words=$(xargs grep -nwE 'sorry|admit|native_decide|axiom' <<<"$files" || true)
dbg=$(xargs grep -nE 'set_option\s+debug\.|skipKernelTC' <<<"$files" || true)
if [ -n "$bad$words$dbg" ]; then
  printf '%s\n' "$bad" "$words" "$dbg" | sed '/^$/d'
  echo "error: runtime code outside what the proofs cover" >&2
  exit 1
fi
echo "LeanLightEvm's closure: $(wc -l <<<"$closure") modules ($(grep -c '^EthLib\.' <<<"$closure") of EthLib, $(grep -c '^Std\.' <<<"$closure") of Std, $(grep -cE '^LeanLight(\.|$)' <<<"$closure") of LeanLight, $(grep -cE '^LeanLightEvm(\.|$)' <<<"$closure") of LeanLightEvm)"
echo "csimp equations in it (each a theorem the axiom audit checks):"
xargs grep -n '@\[csimp\]' <<<"$files" || echo "  none"
echo "evm runtime check passed"
