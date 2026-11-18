import LeanLightEvmTests.Vectors

/-!
# `leanlight-evm-test`'s checks

Everything here drives `LeanLightEvm.call`, the checked entry, and nothing else of
EthLib: the recorded answers and gas (`recorded`), the discovery loop with the doubling budget
(`discover`), the withheld and corrupted sweeps (`sweep`), and the cases built by hand that must
end in a refusal or in `needs` (`adversarial`).
-/

namespace LeanLightEvmTests

open EthLib.Base
open EthLib.Execution.Evm (EvmError)
open EthLib.Execution.State (EMPTY_CODE_HASH)
open LeanLightEvm

structure Tally where
  passed : Nat := 0
  failures : Array String := #[]
  notes : Array String := #[]

def Tally.check (t : Tally) (ok : Bool) (what : String) : Tally :=
  if ok then { t with passed := t.passed + 1 } else { t with failures := t.failures.push what }

def Tally.note (t : Tally) (what : String) : Tally := { t with notes := t.notes.push what }

/-! ## Showing outcomes -/

def errKind : Option EvmError → String
  | none => "-"
  | some .revert => "revert"
  | some .outOfGas => "outOfGas"
  | some (.invalidOpcode _) => "invalidOpcode"
  | some _ => "halt"

def _root_.LeanLightEvm.Outcome.show : Outcome → String
  | .answer a => s!"answer ok={a.result.ok} {errKind a.result.error} gas {a.result.gasUsed} {(toHex a.result.output).take 74}"
  | .refused r => s!"refused {repr r}"
  | .needs n => s!"needs {n.accounts.length} accounts, {n.slots.length} slots, {n.code.length} code, {n.storageRoots.length} roots, ancestors {n.ancestors}"
  | .unsupported u => s!"unsupported {repr u}"

def _root_.LeanLightEvm.Outcome.isAnswer : Outcome → Bool
  | .answer _ => true
  | _ => false

def sameLog (x y : EthLib.Execution.Blocks.Log) : Bool :=
  x.address == y.address && x.topics == y.topics && x.data.data == y.data.data

def sameResult (x y : Result) : Bool :=
  x.ok == y.ok && x.output.data == y.output.data && x.error == y.error && x.gasUsed == y.gasUsed &&
    x.refund == y.refund && x.logs.size == y.logs.size &&
    (x.logs.zip y.logs).all fun (a, b) => sameLog a b

/-- Two outcomes that are the same answer, the same refusal, or both not answers. -/
def sameOutcome : Outcome → Outcome → Bool
  | .answer a, .answer b => sameResult a.result b.result
  | .refused a, .refused b => a == b
  | .answer _, _ => false
  | _, .answer _ => false
  | .refused _, _ => false
  | _, .refused _ => false
  | _, _ => true

/-! ## Running a case -/

def runWith (f : VFile) (c : Case) (fs : Facts) (b : Budgets := {}) (round : Nat := 0)
    (ancestors : Option (List Hash32) := c.ancestors) : Outcome :=
  call b { c.input f fs round with ancestors }

/-- The accounts a needs names as storage roots whose root the vector did not record. -/
def unrecordedRoots (c : Case) (n : Needs) : Bool :=
  !n.storageRoots.isEmpty && n.accounts.isEmpty && n.slots.isEmpty && n.code.isEmpty &&
    !n.ancestors && n.storageRoots.all fun a =>
      (c.accounts.find? (·.1 == a)).any fun (_, l) => !l.absent && l.root.isNone

/-- The case on its facts. When the only thing missing is the storage root of deployment
candidates (nonce 0, no code) whose root the fixture did not record, it runs again with the empty
root assumed for them: the fixtures recorded with plain getters, or before roots were kept,
lack them. The accounts assumed are returned, and every report names them. -/
def baseline (f : VFile) (c : Case) : Outcome × Facts × List Address := Id.run do
  let mut assumed : List Address := []
  let mut fs := c.facts f
  let mut o := runWith f c fs
  for _ in [0:64] do
    match o with
    | .needs n =>
      if unrecordedRoots c n then
        assumed := assumed ++ n.storageRoots
        fs := c.facts f assumed
        o := runWith f c fs
      else break
    | _ => break
  return (o, fs, assumed)

/-! ## Recorded answers -/

def refusalName : Refusal → String
  | .insufficientFunds => "funds"
  | .intrinsicGasTooLow => "intrinsic"
  | .initCodeTooLarge _ => "initcode"
  | r => s!"{repr r}"

/-- The outcome against what was recorded: the node's flag and output, EthLib's error kind, gas
and logs, or the node's refusal. -/
def mismatch (c : Case) (o : Outcome) : Option String :=
  match c.expect, o with
  | .ran ok out err, .answer a =>
    let r := a.result
    -- a capped run that halts otherwise than by a revert consumes the capped gas, not the
    -- recorded run's (the header's): its gas is not compared (`allGasCapped`)
    let gasComparable := !(a.capped && r.error.isSome && r.error != some .revert)
    if r.ok != ok then some s!"ok {r.ok}, node {ok}"
    else if (out.map fun b => b.data != r.output.data).getD false then
      some s!"output {(toHex r.output).take 74}, node {(out.map toHex).getD "-"}"
    else if errKind r.error != err.getD "-" then some s!"error {errKind r.error}, recorded {err.getD "-"}"
    else if gasComparable && (c.gas.map (· != r.gasUsed)).getD false then
      some s!"gas {r.gasUsed}, recorded {c.gas.getD 0}"
    else if c.checkLogs && (c.logs.size != r.logs.size ||
        !(c.logs.zip r.logs).all fun ((a, t, d), l) =>
          a == l.address && t == l.topics && d.data == l.data.data) then
      some s!"logs {r.logs.size}, recorded {c.logs.size}"
    else none
  | .refused why, .refused r => if refusalName r == why then none else some s!"refused {refusalName r}, node {why}"
  | .ran .., o => some s!"{o.show}, recorded an answer"
  | .refused why, o => some s!"{o.show}, node refused ({why})"
  | _, _ => some "not a recorded case"

/-- Whether a case's recorded answer differs from the first node's only, and the outcome is the
second node's answer (two nodes disagreed when it was recorded). -/
def matchesSecond (c : Case) (o : Outcome) : Bool :=
  match c.second, c.expect, o with
  | some (ok, out), .ran _ _ err, .answer _ =>
    mismatch { c with expect := .ran ok out err, gas := none, logs := #[], checkLogs := false } o |>.isNone
  | _, _, _ => false

/-- A refusal by design, not a wrong answer, of a recorded call:

- the call accesses a deployment candidate (nonce 0, no code) whose storage root is proved not
  empty: EIP-7610 reads its whole storage, which `call` does not hold (R3), so it refuses;
- the request names more gas than the cap leaves before Glamsterdam: its answer could depend on
  that gas, so `call` refuses it as over budget. -/
def refusedByDesign (c : Case) (o : Outcome) : Option String :=
  match o with
  | .unsupported (.collisionUndecidable a) =>
    if (c.accounts.find? (·.1 == a)).any fun (_, l) =>
        !l.absent && l.nonce == 0 && (match l.code with | .none => true | _ => false) &&
          l.root.any (· != EMPTY_STORAGE_ROOT) then
      some s!"collision undecidable at {vhex a} (R3), recorded {match c.expect with | .ran ok .. => s!"ok={ok}" | _ => "-"}"
    else none
  | .unsupported (.budget .executionGas) =>
    if c.request.gas.any (· > 16777216) then some s!"named gas {c.request.gas.getD 0} over the cap" else none
  | _ => none

/-! ## The discovery loop -/

/-- The facts after serving `n` from the oracle `orc`: the case's own facts play the node, and a
key they lack is served as an absent account (a key only a run on defaults reads; the final
complete run never reads one, or its answer would not match). A slot comes with its account,
as `eth_getProof` gives both. -/
def serve (orc fs : Facts) (n : Needs) : Facts := Id.run do
  let mut fs := fs
  let addAccount (fs : Facts) (a : Address) : Facts :=
    if fs.accounts.contains a then fs
    else { fs with accounts := fs.accounts.insert a ((orc.accounts[a]?).getD .absent) }
  -- the planner fetches the code of an account it fetches (by its hash, `ElCode`), as the
  -- client's loop does, rather than spend a run to learn that the code is missing
  let addCode (fs : Facts) (a : Address) : Facts :=
    match fs.accounts[a]? with
    | some (.present _ _ h _) =>
      match orc.code[h]? with
      | some b => { fs with code := fs.code.insert h b }
      | none => fs
    | _ => fs
  for a in n.accounts do fs := addCode (addAccount fs a) a
  for a in n.storageRoots do fs := { fs with accounts := fs.accounts.insert a ((orc.accounts[a]?).getD .absent) }
  for (a, k) in n.slots do
    fs := addCode (addAccount fs a) a
    if let some (.present ..) := fs.accounts[a]? then
      let v := ((orc.slots.getD a ∅)[k]?).getD 0
      fs := { fs with slots := fs.slots.insert a ((fs.slots.getD a ∅).insert k v) }
  for h in n.code do
    if let some b := orc.code[h]? then fs := { fs with code := fs.code.insert h b }
  return fs

structure Discovery where
  outcome : Outcome
  rounds : Nat
  keys : Nat
  widest : Nat
  stuck : Option String := none

/-- The call from no facts at all, each round fetching what `needs` names from the oracle, under
budgets `b` (by default the defaults, so `rounds` is bounded by 32). -/
def discover (f : VFile) (c : Case) (orc : Facts) (b : Budgets := {}) (start : Facts := {}) :
    Discovery := Id.run do
  let mut fs := start
  let mut ancestors : Option (List Hash32) := none
  let mut widest := 0
  for round in [0:b.rounds + 1] do
    let o := runWith f c fs b round ancestors
    match o with
    | .needs n =>
      widest := max widest (n.keys + n.code.length + n.storageRoots.length)
      if n.ancestors then
        if c.ancestors.isNone then
          return { outcome := o, rounds := round + 1, keys := fs.stateKeys, widest, stuck := "ancestors not recorded" }
        ancestors := c.ancestors
      let before := fs.stateKeys + fs.code.size
      fs := serve orc fs n
      if fs.stateKeys + fs.code.size == before && !n.ancestors then
        return { outcome := o, rounds := round + 1, keys := fs.stateKeys, widest, stuck := s!"oracle cannot serve {o.show}" }
    | _ => return { outcome := o, rounds := round + 1, keys := fs.stateKeys, widest }
  return { outcome := .unsupported (.budget .rounds), rounds := b.rounds, keys := fs.stateKeys, widest }

/-- Whether the outcome is R0's refusal of facts that are no state's. -/
def isMalformed : Outcome → Bool
  | .unsupported (.malformed _) => true
  | _ => false

/-- The round budget a call that needs more rounds than `Budgets.rounds` is run under, to check
its answer anyway: a refusal at the round budget is by design only when the same discovery
with this many rounds gives the recorded answer. -/
def liftedRounds : Nat := 64

/-! ## Sweeps -/

/-- Whether the answer `a` on facts `fs` needs the item: withholding it must then not give an
answer, and corrupting it may change the answer. Otherwise withholding or corrupting it must
leave the answer as it was (the tracker shows it irrelevant). -/
def required (fs : Facts) (c : Case) (a : Answer) (accounts : Std.ExtTreeSet Address)
    (slots : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) : Item → Bool
  | .account x => accounts.contains x || slots.contains x
  | .slot x k => (slots.getD x ∅).contains k && !fs.storageEmpty x
  | .code h => accounts.toList.any fun x => match fs.accounts[x]? with
    | some (.present _ _ ch _) => ch == h
    | _ => false
  | .root x => accounts.contains x && match fs.accounts[x]? with
    | some (.present n _ ch (some _)) =>
      (n == 0 && ch == EMPTY_CODE_HASH) ||
        ((slots.getD x ∅).toList.any fun k => !(fs.slots.getD x ∅).contains k)
    | _ => false
  | .ancestors => a.reads.blockNumbers.any fun b => c.header.number - b > 1

/-- At most `cap` items, spread evenly over the list. -/
def spread {α : Type} (xs : Array α) (cap : Nat) : Array α :=
  if xs.size ≤ cap then xs
  else (Array.range cap).filterMap fun i => xs[i * xs.size / cap]?

/-- What a sweep covered: items of the case, required items withheld (all of them), unread
items withheld and corrupted (at most the cap, spread). -/
structure Coverage where
  items : Nat := 0
  required : Nat := 0
  unread : Nat := 0
  unreadSwept : Nat := 0

/-- Withhold every required item (each must stop the answer), then withhold and corrupt at most
`cap` of the others, spread over them (each must leave the answer as it was); the required
items among the `cap` spread over all are corrupted too, counted only. -/
def sweep (t : Tally) (f : VFile) (c : Case) (fs : Facts) (a : Answer) (cap : Nat) :
    Tally × Nat × Nat × Nat × Coverage := Id.run do
  let mut t := t
  let accounts := a.reads.accounts.foldl (fun s x => s.insert x) (∅ : Std.ExtTreeSet Address)
  let slots := a.reads.slots.foldl (fun m (x, k) => m.insert x ((m.getD x ∅).insert k))
    (∅ : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
  let base : Outcome := .answer a
  let mut changed := 0
  let mut unchanged := 0
  let mut runs := 0
  let all := items fs c.ancestors.isSome
  let req := all.filter (required fs c a accounts slots)
  let unread := all.filter fun it => !required fs c a accounts slots it
  let sampled := spread all cap
  let cov : Coverage := { items := all.size, required := req.size, unread := unread.size
                          unreadSwept := (spread unread cap).size }
  let withheldRun (it : Item) : Outcome := match it with
    | .ancestors => runWith f c fs (ancestors := none)
    | _ => runWith f c (withhold fs it)
  for it in req do
    let o := withheldRun it
    runs := runs + 1
    t := t.check (!o.isAnswer) s!"{c.file}: {c.name}: withheld {it.show}, required, still answered: {o.show}"
  for it in spread unread cap do
    let o := withheldRun it
    runs := runs + 1
    t := t.check (sameOutcome o base) s!"{c.file}: {c.name}: withheld {it.show}, unread, changed: {o.show}"
    for (what, fs') in corruptions fs it do
      let o := runWith f c fs'
      runs := runs + 1
      -- a corruption that makes the facts no state's (a nonzero slot under the empty root) is
      -- refused before anything runs (R0): not an answer, so not a changed one
      let refusedR0 := isMalformed o
      t := t.check (sameOutcome o base || refusedR0) s!"{c.file}: {c.name}: corrupted {it.show} ({what}), unread, changed: {o.show}"
  for it in sampled do
    let isReq := required fs c a accounts slots it
    unless isReq do continue
    for (what, fs') in corruptions fs it do
      let o := runWith f c fs'
      runs := runs + 1
      let _ := what
      if sameOutcome o base then unchanged := unchanged + 1 else changed := changed + 1
  return (t, runs, changed, unchanged, cov)

end LeanLightEvmTests
