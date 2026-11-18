import LeanLightEvmTests.Proofs

/-!
`lake exe leanlight-evm-test [--quick] [--sweep-cap N] [FILE ...]`, run from `evm/`:
`LeanLightEvm.call` against the recorded calls of `tests/vectors` (each file checked against its
`SHA256SUMS` first), then the cases built by hand.

For each recorded case: the answer and gas recorded (the node's flag and output, EthLib's error
kind, gas used and logs, or the node's refusal), with the empty storage root assumed only for
deployment candidates whose root the recording did not keep (counted); EthLib's least passing gas
for an estimate (it passes at that gas and not one below); the discovery loop from no facts, with
the doubling width and the default budgets, to the same answer; and, unless `--quick`, the
sweeps: every required fact withheld in turn (none may give an answer), and up to `--sweep-cap`
unread facts a case (48), spread over them, each withheld and corrupted in turn (each must leave
the answer as it was); the counts swept are printed. Gas used, the error kind, logs and the
estimate's least gas are EthLib's recorded values (a regression check between two EthLib paths),
not a node's; the flag, the output and a refusal's class are the node's, and the node's own
estimate must pass. Then the proof-backed tier (`LeanLightEvmTests.Proofs`: every fact read by
`LeanLightEvm.Driver.inputAt` through leanLight's readers), the synthetic worlds
(`LeanLightEvmTests.Synthetic`: `call` against `reference` on the full state) and the cases built
by hand. Exits 1 on any failure.
-/

open LeanLightEvmTests LeanLightEvm

def defaultFiles : List String :=
  ["mainnet-calls24.txt.gz", "mainnet-corpus.txt.gz", "mainnet-proof-26435868.txt.gz",
   "sepolia-corpus.txt.gz", "mainnet-edge.txt.gz", "sepolia-edge.txt.gz", "sepolia-second.txt.gz"]

/-- The proof-backed tier (`LeanLightEvmTests.Proofs`): facts only through leanLight's readers. -/
def proofFiles : List String := ["mainnet-proofs-26435868.txt.gz", "sepolia-proofs-12155734.txt.gz"]

structure Opts where
  quick : Bool := false
  proofs : Bool := false
  trace : Option String := none
  cap : Nat := 48
  files : List String := []

def parseOpts : List String → Opts → Opts
  | "--quick" :: r, o => parseOpts r { o with quick := true }
  | "--proofs" :: r, o => parseOpts r { o with proofs := true }
  | "--sweep-cap" :: n :: r, o => parseOpts r { o with cap := n.toNat?.getD o.cap }
  | "--trace" :: n :: r, o => parseOpts r { o with trace := some n }
  | f :: r, o => parseOpts r { o with files := o.files ++ [f] }
  | [], o => o

def main (args : List String) : IO UInt32 := do
  let opts := parseOpts args {}
  let dir : System.FilePath := "tests/vectors"
  let names := if opts.files.isEmpty then defaultFiles else opts.files
  let mut t : Tally := {}
  -- per kind: cases, answered and matching, refused by design, matching with a root assumed
  let mut kinds : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  let mut cov : Coverage := {}
  let mut assumedCases := 0
  let mut assumedAccounts := 0
  let mut maxRounds := (0, "")
  let mut overRounds : Array String := #[]
  let mut maxWidest := 0
  let mut sweepRuns := 0
  let mut changed := 0
  let mut unchanged := 0
  let mut slowest := (0, "")
  let mut mainBase : Option (VFile × Case) := none
  let mut sepBase : Option (VFile × Case) := none
  let t0 ← IO.monoMsNow
  for name in names do
    let f ← load dir name
    let tf ← IO.monoMsNow
    let mut answered := 0
    for c in f.cases do
      let tc ← IO.monoMsNow
      if opts.trace == some c.name then
        let (_, orc, _) := baseline f c
        let mut fs : Facts := {}
        -- traced with the round budget lifted to 64, to see how many rounds the call needs
        for round in [0:64] do
          let o := runWith f c fs { rounds := 64 } round c.ancestors
          IO.println s!"trace {c.name}: round {round}: {o.show}"
          match o with
          | .needs n =>
            IO.println s!"  asks accounts {n.accounts.map vhex} slots {n.slots.map fun (a, k) => s!"{(vhex a).take 10}:{(vhex k).drop 60}"} code {n.code.length} roots {n.storageRoots.length}"
            fs := serve orc fs n
          | _ => break
      let (o, fs, assumed) := baseline f c
      if !assumed.isEmpty then
        assumedCases := assumedCases + 1; assumedAccounts := assumedAccounts + assumed.length
      let mut bad := mismatch c o
      if bad.isSome && matchesSecond c o then
        t := t.note s!"{name}: {c.name}: the two nodes disagreed; matches the second ({bad.getD ""})"
        bad := none
      let mut byDesign := false
      if let (some _, some why) := (bad, refusedByDesign c o) then
        t := t.note s!"{name}: {c.name}: refused by design: {why}"
        bad := none; byDesign := true
      t := t.check bad.isNone s!"{name}: {c.name}: {bad.getD ""}{if assumed.isEmpty then "" else s!" (empty root assumed for {assumed.length})"}"
      let (n, p, d, r) := kinds.getD s!"{c.kind}" (0, 0, 0, 0)
      let matched := bad.isNone && !byDesign
      kinds := kinds.insert s!"{c.kind}" (n + 1, p + (if matched then 1 else 0), d + (if byDesign then 1 else 0),
        r + (if matched && !assumed.isEmpty then 1 else 0))
      -- estimates: EthLib's least passing gas passes, one below does not
      if let (some (least, _), .answer _) := (c.estimate, o) then
        let at' (g : Nat) := runWith f { c with request := { c.request with gas := some g } } fs
        let okAt (g : Nat) := match at' g with | .answer a => a.result.ok | _ => false
        t := t.check (okAt least && !okAt (least - 1))
          s!"{name}: {c.name}: estimate: passes at {least} {okAt least}, at {least - 1} {okAt (least - 1)}"
      -- the node's own estimate must pass too (a node-side check of the estimate)
      if let (some (_, some node), .answer _) := (c.estimate, o) then
        let okNode := match runWith f { c with request := { c.request with gas := some node } } fs with
          | .answer a => a.result.ok | _ => false
        t := t.check okNode s!"{name}: {c.name}: the node's estimate {node} does not pass"
      if let .answer a := o then
        answered := answered + 1
        if mainBase.isNone && c.chainId == 1 && c.kind != "edge" then mainBase := some (f, c)
        if sepBase.isNone && c.chainId == 11155111 && c.kind != "edge" && c.request.to.isSome then
          sepBase := some (f, c)
        -- discovery from nothing, under the default budgets
        let d := discover f c fs (start := {})
        -- over the round budget: refused by design only if, with the rounds lifted, the same
        -- discovery reaches the same answer (so the answer is still checked)
        let mut dOk := d.stuck.isNone && sameOutcome d.outcome o
        if !dOk && isBudget .rounds d.outcome then
          let d' := discover f c fs { rounds := liftedRounds } (start := {})
          if d'.stuck.isNone && sameOutcome d'.outcome o then
            dOk := true
            overRounds := overRounds.push s!"{name}: {c.name}: {d'.rounds} rounds"
        t := t.check dOk
          s!"{name}: {c.name}: discovery: {d.outcome.show} after {d.rounds} rounds{d.stuck.map (s!", " ++ ·) |>.getD ""}"
        if d.rounds > maxRounds.1 then maxRounds := (d.rounds, s!"{name}: {c.name}")
        maxWidest := max maxWidest d.widest
        if !opts.quick then
          let (t', runs, ch, un, cv) := sweep t f c fs a opts.cap
          t := t'; sweepRuns := sweepRuns + runs; changed := changed + ch; unchanged := unchanged + un
          cov := { items := cov.items + cv.items, required := cov.required + cv.required
                   unread := cov.unread + cv.unread, unreadSwept := cov.unreadSwept + cv.unreadSwept }
        -- code under the wrong hash: refused before the EVM runs
        if let (h, b) :: _ := fs.code.toList then
          let flipped : ByteArray := ⟨b.data.modify (b.size / 2) (· ^^^ 0x80)⟩
          let o' := runWith f c { fs with code := fs.code.insert h flipped }
          t := t.check (isUnsupported o' fun | .malformed (.codeHash h') => h' == h | _ => false)
            s!"{name}: {c.name}: code not under its hash: {o'.show}"
      let te ← IO.monoMsNow
      if te - tc > slowest.1 then slowest := (te - tc, s!"{name}: {c.name}")
    let te ← IO.monoMsNow
    IO.println s!"{name}: {f.cases.size} cases, {answered} answered, {te - tf} ms"
  -- the EIP-7610 holes
  let hf ← load dir "holes-eip7610.txt.gz"
  t := holes t hf
  -- the proof-backed tier
  if opts.files.isEmpty || opts.proofs then
    for pf in proofFiles do
      let tp ← IO.monoMsNow
      t ← LeanLightEvmTests.Proofs.tier t dir pf
      IO.println s!"{pf}: proof tier, {(← IO.monoMsNow) - tp} ms"
  -- the synthetic worlds
  t := LeanLightEvmTests.Synthetic.checks t
  -- the cases built by hand
  match mainBase, sepBase with
  | some (mf, mc), some (sf, sc) =>
    IO.println s!"adversarial bases: {mf.name}: {mc.name}; {sf.name}: {sc.name}"
    t := adversarial t mf mc sf sc
    -- a wrong-fork control: Sepolia's cases one second before its Glamsterdam run as BPO2
    let sepFile ← load dir "sepolia-edge.txt.gz"
    let mut differ := 0
    for c in sepFile.cases do
      let (o, fs, _) := baseline sepFile c
      let c' := { c with header := { c.header with timestamp := 1791294815 } }
      if !sameOutcome o (runWith sepFile c' fs) then differ := differ + 1
    t := t.check (0 < differ) s!"wrong-fork control: {differ} Sepolia edge cases change under BPO2"
    t := t.note s!"wrong-fork control: {differ} of {sepFile.cases.size} Sepolia edge cases change when run under BPO2's rules"
  | _, _ => t := t.check false "no base case for the adversarial checks"
  let t1 ← IO.monoMsNow
  for (k, (n, p, d, r)) in kinds.toList do
    IO.println s!"  kind {k}: {n} cases: {p} answered or refused as recorded ({r} of them with an empty root assumed), {d} refused by design"
  IO.println s!"empty storage root assumed (not recorded) in {assumedCases} cases, for {assumedAccounts} accounts"
  IO.println s!"discovery: most rounds within the budget {maxRounds.1} ({maxRounds.2}); widest round {maxWidest} keys"
  for x in overRounds do
    IO.println s!"over the round budget (refused by design at {({} : Budgets).rounds}; the answer checked with {liftedRounds}): {x}"
  IO.println s!"sweeps: {sweepRuns} runs; items {cov.items}: required {cov.required}, all withheld; unread {cov.unread}, {cov.unreadSwept} withheld and corrupted (cap {opts.cap} a case); required facts corrupted (sampled): {changed} changed the outcome, {unchanged} did not"
  IO.println s!"slowest case: {slowest.1} ms ({slowest.2}); total {t1 - t0} ms"
  for n in t.notes do IO.println s!"note: {n}"
  for x in t.failures do IO.println s!"FAIL {x}"
  IO.println s!"{t.passed} checks passed, {t.failures.size} failed"
  return if t.failures.isEmpty then 0 else 1
