#!/usr/bin/env python3
"""Regenerates evm/EthLib, the part of EthLib leanlight-evm vendors, or checks it.

    evm/scripts/vendor-ethlib.py CHECKOUT           # write the tree from CHECKOUT
    evm/scripts/vendor-ethlib.py --check CHECKOUT   # fail unless the tree is what CHECKOUT gives
    evm/scripts/vendor-ethlib.py --sums             # offline: check SHA256SUMS only

CHECKOUT is a git checkout of github.com/ethereum/EthLib that holds the commit evm/EthLib/PIN
names (the one place the pin is recorded). Every file is read from git's objects at that commit
(`git cat-file`), never from the working tree, so local changes, untracked files and checkout
filters do not matter. The script never runs anything of the checkout: it only asks git for
objects.

The tree holds two import closures, every module copied byte for byte to its upstream path (so
the module names are upstream's), plus upstream's LICENSE (CC0-1.0):

- the runtime: the closure of RUNTIME_ROOT, EthLib's transaction processing (the interpreter,
  every precompile, the state, RLP and the hashes and curves they use). It is what the library
  `LeanLightEvm` runs; its imports outside the checkout must be Lean core's `Init` or one of
  EXTERNAL.
- the proofs: the closure of PROOF_ROOTS (EthLib's noninterference theorems, which
  `LeanLightEvmProofs` builds on) less the runtime's modules. Every module of it must be one of
  EthLib's proof modules (`EthLib.*.Proofs.*`): a runtime module the proofs need and the runtime
  closure lacks would be code that runs nowhere and is checked nowhere, so the script fails.

`SHA256SUMS` lists the SHA-256 of every vendored file; `--sums` checks it with no checkout, and
fails on a file under evm/EthLib it does not list (besides OURS). Bumping the pin is: edit PIN,
run this, and review the diff of evm/EthLib.
"""

import filecmp
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

RUNTIME_ROOT = "EthLib.Execution.Transactions.Process"
# The theorems LeanLightEvmProofs uses: processMessageCall_agrees and the observer's lemma, the
# covering sets, the incrementNonce lemmas, code availability, and runTransaction_agrees (whose
# private helpers LeanLightEvmProofs copies).
PROOF_ROOTS = [
    "EthLib.Execution.Proofs.Transactions.Noninterference",
    "EthLib.Execution.Proofs.Transactions.NoninterferenceRun",
    "EthLib.Execution.Proofs.Transactions.Observe",
    "EthLib.Execution.Proofs.Transactions.CodeOrigin",
    "EthLib.Execution.Proofs.Evm.Call.NoninterferenceRun",
    "EthLib.Execution.Proofs.Evm.Call.Candidate",
    "EthLib.Execution.Proofs.State.CodeAvailability",
]
# The modules beyond Init the vendored closures may import from Lean's toolchain.
EXTERNAL = {"Std.Data.ExtTreeMap", "Std.Data.ExtTreeSet"}
# Files of evm/EthLib that are leanLight's, not upstream's.
OURS = {"PIN", "VENDORED.md", "SHA256SUMS", "RUNTIME", "PROOFS"}

HERE = os.path.dirname(os.path.abspath(__file__))
TREE = os.path.join(HERE, "..", "EthLib")

IMPORT = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.']+)\s*$")


def die(msg):
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


def header_imports(text):
    """The modules a file's header imports: the lines after an optional `module` and before the
    first command, skipping blank lines and comments."""
    out = []
    depth = 0  # nesting of /- -/ block comments
    for raw in text.decode("utf-8").splitlines():
        line = raw.strip()
        if depth > 0 or line.startswith("/-"):
            depth += line.count("/-") - line.count("-/")
            continue
        if not line or line.startswith("--") or line == "module":
            continue
        m = IMPORT.match(line)
        if not m:
            break
        out.append(m.group(1))
    return out


def blob(checkout, rev, path):
    """The bytes of `path` at commit `rev`, from git's objects; None when there is no such file."""
    r = subprocess.run(["git", "-C", checkout, "cat-file", "-p", f"{rev}:{path}"],
                       capture_output=True, check=False)
    return r.stdout if r.returncode == 0 else None


def closure(checkout, rev, roots):
    seen, external, stack, texts = set(), set(), list(roots), {}
    while stack:
        mod = stack.pop()
        if mod in seen or mod in external:
            continue
        text = blob(checkout, rev, "/".join(mod.split(".")) + ".lean")
        if text is None:
            external.add(mod)
            continue
        seen.add(mod)
        texts[mod] = text
        stack.extend(header_imports(text))
    bad = sorted(m for m in external
                 if m not in EXTERNAL and m != "Init" and not m.startswith("Init."))
    if bad:
        die(f"the closure of {list(roots)} imports modules outside Init and {sorted(EXTERNAL)}: {bad}")
    return sorted(seen), texts


def git(checkout, *args):
    return subprocess.run(["git", "-C", checkout, *args], check=True, capture_output=True,
                          text=True).stdout.strip()


def write(mods, texts, out):
    for mod in mods:
        if not mod.startswith("EthLib."):
            die(f"{mod} is outside the checkout's EthLib directory")
        rel = os.path.join(*mod.split(".")[1:]) + ".lean"
        dst = os.path.join(out, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, "wb") as f:
            f.write(texts[mod])


def build(checkout, rev, out):
    """Both closures into `out`, with LICENSE and the two module lists."""
    runtime, rtexts = closure(checkout, rev, [RUNTIME_ROOT])
    proofs, ptexts = closure(checkout, rev, PROOF_ROOTS)
    proofs = [m for m in proofs if m not in set(runtime)]
    bad = [m for m in proofs if ".Proofs." not in m]
    if bad:
        die(f"the proofs need modules that are neither proofs nor in the runtime closure: {bad}")
    bad = [m for m in runtime if ".Proofs." in m]
    if bad:
        die(f"the runtime closure holds proof modules: {bad}")
    write(runtime, rtexts, out)
    write(proofs, ptexts, out)
    lic = blob(checkout, rev, "LICENSE")
    if lic is None:
        die(f"no LICENSE at {rev}")
    with open(os.path.join(out, "LICENSE"), "wb") as f:
        f.write(lic)
    # The module lists: evm/scripts/check-runtime.sh audits RUNTIME, the proofs' sweep PROOFS.
    with open(os.path.join(out, "RUNTIME"), "w", encoding="utf-8") as f:
        f.write("".join(m + "\n" for m in runtime))
    with open(os.path.join(out, "PROOFS"), "w", encoding="utf-8") as f:
        f.write("".join(m + "\n" for m in proofs))
    return runtime, proofs


def manifest(tree, names):
    """`sha256sum`'s format: the SHA-256 of each file, sorted by path."""
    lines = []
    for rel in sorted(names):
        with open(os.path.join(tree, rel), "rb") as f:
            lines.append(hashlib.sha256(f.read()).hexdigest() + "  " + rel.replace(os.sep, "/"))
    return "\n".join(lines) + "\n"


def files(tree, ours=OURS):
    out = set()
    if not os.path.isdir(tree):
        return out
    for d, _, fs in os.walk(tree):
        for f in fs:
            rel = os.path.relpath(os.path.join(d, f), tree)
            if rel not in ours:
                out.add(rel)
    return out


def check_sums():
    """Offline: every file of the tree but OURS is listed in SHA256SUMS with its hash, and every
    file listed is there."""
    path = os.path.join(TREE, "SHA256SUMS")
    want = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            digest, rel = line.rstrip("\n").split("  ", 1)
            want[rel] = digest
    have = {rel.replace(os.sep, "/") for rel in files(TREE)}
    diff = sorted(set(want) ^ have)
    for rel in sorted(set(want) & have):
        with open(os.path.join(TREE, rel), "rb") as f:
            if hashlib.sha256(f.read()).hexdigest() != want[rel]:
                diff.append(rel)
    if diff:
        die("evm/EthLib differs from its SHA256SUMS: " + ", ".join(diff))
    print(f"evm/EthLib: {len(want)} files match SHA256SUMS")


def main(argv):
    if argv == ["--sums"]:
        check_sums()
        return
    check = "--check" in argv
    args = [a for a in argv if a != "--check"]
    if len(args) != 1:
        die(__doc__.strip().splitlines()[2].strip())
    checkout = os.path.abspath(args[0])
    with open(os.path.join(TREE, "PIN"), encoding="utf-8") as f:
        pin = f.read().split()[0]
    if git(checkout, "cat-file", "-t", pin) != "commit":
        die(f"{checkout} does not hold commit {pin} (evm/EthLib/PIN)")
    with tempfile.TemporaryDirectory() as tmp:
        runtime, proofs = build(checkout, pin, tmp)
        want, have = files(tmp), files(TREE)
        sums = manifest(tmp, want)
        generated = ["RUNTIME", "PROOFS"]
        if check:
            diff = sorted(want ^ have) + sorted(
                f for f in want & have
                if not filecmp.cmp(os.path.join(tmp, f), os.path.join(TREE, f), shallow=False))
            for g in generated:
                p = os.path.join(TREE, g)
                if not os.path.isfile(p) or not filecmp.cmp(os.path.join(tmp, g), p, shallow=False):
                    diff.append(g)
            sums_path = os.path.join(TREE, "SHA256SUMS")
            if not os.path.isfile(sums_path) or open(sums_path, encoding="utf-8").read() != sums:
                diff.append("SHA256SUMS")
            if diff:
                die(f"evm/EthLib differs from EthLib {pin}: " + ", ".join(diff))
            print(f"evm/EthLib: {len(runtime)} runtime and {len(proofs)} proof modules of EthLib "
                  f"{pin[:8]}, byte for byte")
            return
        for f in have - want:
            os.remove(os.path.join(TREE, f))
        for f in list(want) + generated:
            dst = os.path.join(TREE, f)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(os.path.join(tmp, f), dst)
        with open(os.path.join(TREE, "SHA256SUMS"), "w", encoding="utf-8") as f:
            f.write(sums)
        for d, _, _ in sorted(os.walk(TREE), reverse=True):
            if not os.listdir(d):
                os.rmdir(d)
        print(f"evm/EthLib: wrote {len(runtime)} runtime and {len(proofs)} proof modules of "
              f"EthLib {pin[:8]}")


if __name__ == "__main__":
    main(sys.argv[1:])
