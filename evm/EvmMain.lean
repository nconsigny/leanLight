import LeanLightEvmCli

/-!
# `leanlight-evm`

```
leanlight-evm [--network mainnet|sepolia] --consensus-rpc URL[,URL...] --execution-rpc URL[,URL...]
              (--checkpoint 0xROOT | --unsafe-untrusted-checkpoint) [--json] [-v]
              [--from ADDR] [--value WEI] [--gas N] [--compare] COMMAND

COMMAND:
  call TO [DATA]       eth_call of TO with DATA (hex) at the anchored block
  create INITCODE      eth_call of a creation with INITCODE (hex): the deployed code it returns
  estimate TO [DATA]   the least gas, as named in the request, at which the checked call
                       succeeds: it succeeded at that gas and failed one below
```

It syncs as `leanlight` does, binds the anchored execution block, then runs the call in rounds
(`LeanLightEvmCli.Call`): each round fetches the proofs and code the previous run of
`LeanLightEvm.call` asked for, at the anchored block. Every value printed comes out of
`LeanLightEvm.Driver.run`, never out of the endpoint's JSON, but the endpoint's own answer that
`--compare` prints beside it, marked unchecked.

`--from` defaults to the zero address, as nodes do; `--gas` names a gas limit (otherwise the
header's limit sizes the intrinsic gas and execution gas is capped at 2^24, `LeanLightEvm.Budgets`).
-/

open LeanLight.Cli
open LeanLight.Lc
open LeanLightEvm
open LeanLightEvm.Cli
open LeanLightEvm.Driver

structure Args where
  network : String := "mainnet"
  consensus : Option String := none
  execution : Option String := none
  checkpoint : Option String := none
  unsafeUntrustedCheckpoint : Bool := false
  json : Bool := false
  verbose : Bool := false
  compare : Bool := false
  sender : Option String := none
  value : Option String := none
  gas : Option String := none
  rest : List String := []

def valued : List String :=
  ["--network", "--consensus-rpc", "--execution-rpc", "--checkpoint", "--from", "--value", "--gas"]

def flag (o : String) (a : Args) : Option Args :=
  match o with
  | "--unsafe-untrusted-checkpoint" => some { a with unsafeUntrustedCheckpoint := true }
  | "--json" => some { a with json := true }
  | "-v" => some { a with verbose := true }
  | "--compare" => some { a with compare := true }
  | _ => none

partial def parseArgs : List String → Args → Except String Args
  | [], a => pure { a with rest := a.rest.reverse }
  | o :: r, a =>
    if valued.contains o then
      match r with
      | v :: r =>
        if v.startsWith "--" then throw s!"{o} needs a value, got {v}"
        else
          let a := match o with
            | "--network" => { a with network := v }
            | "--consensus-rpc" => { a with consensus := some v }
            | "--execution-rpc" => { a with execution := some v }
            | "--checkpoint" => { a with checkpoint := some v }
            | "--from" => { a with sender := some v }
            | "--value" => { a with value := some v }
            | _ => { a with gas := some v }
          parseArgs r a
      | [] => throw s!"{o} needs a value"
    else match flag o a with
      | some a => parseArgs r a
      | none =>
        if o.startsWith "-" && o.length > 1 && !(o.startsWith "0x") then throw s!"unknown option {o}"
        else parseArgs r { a with rest := o :: a.rest }

def usage : String :=
  "usage: leanlight-evm [--network mainnet|sepolia] --consensus-rpc URL --execution-rpc URL " ++
  "(--checkpoint 0xROOT | --unsafe-untrusted-checkpoint) [--json] [-v] [--from ADDR] [--value WEI] " ++
  "[--gas N] [--compare] (call TO [DATA] | create INITCODE | estimate TO [DATA])"

def hexArg (what s : String) : Except String ByteArray :=
  match hexBytes s with
  | some b => pure b
  | none => throw s!"{what}: not hex: {s}"

def addrArg (s : String) : Except String EthLib.Base.Address := do
  let b ← hexArg "address" s
  match toVector 20 b.data.toList with
  | some a => pure a
  | none => throw s!"address: not 20 bytes: {s}"

/-- A decimal or `0x` number. -/
def natArg (what s : String) : Except String Nat :=
  if s.startsWith "0x" then
    match hexNat s with
    | some n => pure n
    | none => throw s!"{what}: not a number: {s}"
  else match s.toNat? with
    | some n => pure n
    | none => throw s!"{what}: not a number: {s}"

inductive Command where
  | call (r : Request)
  | estimate (r : Request)

def parseCommand (a : Args) : Except String Command := do
  let sender ← match a.sender with
    | some s => addrArg s
    | none => pure (Vector.replicate 20 0)
  let value ← match a.value with
    | some v => natArg "value" v
    | none => pure 0
  let gas ← a.gas.mapM (natArg "gas")
  let req (to : Option EthLib.Base.Address) (data : ByteArray) : Request :=
    { sender, to, data, value, gas }
  match a.rest with
  | ["call", to] => return .call (req (some (← addrArg to)) .empty)
  | ["call", to, data] => return .call (req (some (← addrArg to)) (← hexArg "data" data))
  | ["create", code] => return .call (req none (← hexArg "init code" code))
  | ["estimate", to] => return .estimate (req (some (← addrArg to)) .empty)
  | ["estimate", to, data] => return .estimate (req (some (← addrArg to)) (← hexArg "data" data))
  | [] => throw "no command"
  | c => throw s!"unknown command: {" ".intercalate c}"

/-! ## Output -/

def jn (n : Nat) : Json := .num (toString n)

def timed {α} (act : IO α) : IO (α × Nat × Timing) := do
  timing.set {}
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0, ← timing.get)

def timingFields (ms : Nat) (t : Timing) : List (String × Json) :=
  [("ms", (jn ms)), ("net_ms", (jn t.netMs)), ("verify_ms", (jn t.verifyMs)),
   ("requests", (jn t.requests)), ("bytes", (jn t.bytes))]

def timingText (ms : Nat) (t : Timing) : String :=
  s!"{ms} ms (network {t.netMs} ms in {t.requests} requests, {t.bytes} bytes; verify {t.verifyMs} ms)"

def emit (json : Bool) (fields : List (String × Json)) (text : String) : IO Unit := do
  if json then IO.println (Json.mkObj fields).compress else IO.println text

def forkText (f : EthLib.Base.Fork) : String := (reprStr f).replace "EthLib.Base.Fork." ""

def outcomeFields : Outcome → List (String × Json) × String
  | .answer a =>
    let r := a.result
    ([("outcome", .str "answer"), ("ok", if r.ok then .bool true else .bool false),
      ("output", .str (toHex r.output)),
      ("error", match r.error with | some e => .str (reprStr e) | none => .null),
      ("gas_used", jn r.gasUsed), ("refund", jn r.refund), ("logs", jn r.logs.size),
      ("fork", .str (forkText a.fork)), ("capped", .bool a.capped),
      ("accounts_read", jn a.reads.accounts.length), ("slots_read", jn a.reads.slots.length),
      ("block_hashes_read", jn a.reads.blockNumbers.length)],
     s!"{if r.ok then "ok" else s!"failed ({match r.error with | some e => reprStr e | none => "?"})"}: {toHex r.output}\n" ++
     s!"gas used {r.gasUsed} (refund counter {r.refund}), {r.logs.size} logs, fork {forkText a.fork}" ++
     s!"{if a.capped then ", execution gas capped at the budget" else ""}; read {a.reads.accounts.length} accounts, " ++
     s!"{a.reads.slots.length} slots, {a.reads.blockNumbers.length} block hashes")
  | .refused r => ([("outcome", .str "refused"), ("why", .str (reprStr r))], s!"refused, as a node refuses it: {reprStr r}")
  | .needs _ => ([("outcome", .str "needs")], "needs more facts (the budget of rounds is spent)")
  | .unsupported u => ([("outcome", .str "unsupported"), ("why", .str (reprStr u))], s!"not answered: {reprStr u}")

def provedFields (d : Done) : List (String × Json) × String :=
  let f := d.ran.input.facts
  let el := d.ran.el
  ([("anchor_slot", jn d.ran.beacon.beacon.slot), ("block", jn el.number),
    ("block_hash", .str (toHex d.ran.beacon.elHash)), ("state_root", .str (toHexL el.stateRoot)),
    ("rounds", jn d.rounds), ("proved_accounts", jn f.accounts.size),
    ("proved_slots", jn f.stateKeys), ("proved_code_bytes", jn f.codeBytes),
    ("ancestors", .bool d.ran.input.ancestors.isSome)],
   s!"at block {el.number} {toHex d.ran.beacon.elHash} (anchor slot {d.ran.beacon.beacon.slot}, state root {toHexL el.stateRoot}):\n" ++
   s!"proved {f.accounts.size} accounts, {f.stateKeys - f.accounts.size} slots, {f.codeBytes} bytes of code" ++
   s!"{if d.ran.input.ancestors.isSome then ", 256 block hashes" else ""}, in {d.rounds} rounds")

/-- The endpoint's own `eth_call` at the anchored block, unchecked, for `--compare`. -/
def nodeCall (cfg : Config) (b : Anchored) (r : Request) : IO String := do
  let mut obj : List (String × Json) := [("from", .str (toHex (bytesOf r.sender)))]
  if let some to := r.to then obj := obj ++ [("to", .str (toHex (bytesOf to)))]
  obj := obj ++ [("data", .str (toHex r.data))]
  if r.value > 0 then obj := obj ++ [("value", .str (natHex r.value))]
  if let some g := r.gas then obj := obj ++ [("gas", .str (natHex g))]
  match ← rpcC cfg "eth_call" (.arr #[Json.mkObj obj, .str (toHex b.hash)]) with
  | .ok (.str s) => return s
  | .ok j => return j.compress
  | .error e => return s!"error: {e}"

/-- The least gas at which the checked call succeeds, between `lo` (failed, or below the
intrinsic gas) and `hi` (succeeded), by bisection; each probe is a checked run. -/
partial def bisect (cfg : Config) (b : Anchored) (budgets : Budgets) (r : Request) (fx : Fetched)
    (lo hi : Nat) : IO (Nat × Fetched) := do
  if hi ≤ lo + 1 then return (hi, fx)
  let mid := (lo + hi) / 2
  let d ← loop cfg b budgets { r with gas := some mid } fx 0
  match d.ran.outcome with
  | .answer a =>
    if a.result.ok then bisect cfg b budgets r d.fetched lo mid
    else bisect cfg b budgets r d.fetched mid hi
  | .refused .intrinsicGasTooLow => bisect cfg b budgets r d.fetched mid hi
  | o => die s!"estimate: a probe at gas {mid} was not answered: {(outcomeFields o).2}"

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"error: {msg}"
  IO.eprintln usage
  return 2

def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => return ← fail e
  verbose.set args.verbose
  let some chain := (match args.network with
      | "mainnet" => some Forks.mainnet
      | "sepolia" => some Forks.sepolia
      | _ => none)
    | fail s!"unknown network {args.network}"
  let urls (v : String) := ((v.splitOn ",").map (·.trimAscii.toString)).filter (· ≠ "") |>.toArray
  let some consensusAll := args.consensus.map urls | fail "--consensus-rpc is required"
  let some consensus := consensusAll[0]? | fail "--consensus-rpc is required"
  let executionAll := (args.execution.map urls).getD #[]
  let some execution := executionAll[0]? | fail "--execution-rpc is required"
  let checkpoint ← match args.checkpoint.mapM (hexArg "checkpoint") with
    | .ok (some c) => if c.size == 32 then pure (some c) else return ← fail "checkpoint: not 32 bytes"
    | .ok none =>
      if args.unsafeUntrustedCheckpoint then pure none
      else return ← fail "no checkpoint: pass --checkpoint 0xROOT, or --unsafe-untrusted-checkpoint to trust the beacon node's finalized root"
    | .error e => return ← fail e
  let command ← match parseCommand args with
    | .ok c => pure c
    | .error e => return ← fail e
  let cfg : Config := {
    chain, consensus, execution, checkpoint
    unsafeUntrustedCheckpoint := args.unsafeUntrustedCheckpoint
    consensusMore := consensusAll.extract 1
    executionMore := executionAll.extract 1
  }
  let r := match command with | .call r | .estimate r => r
  let budgets : Budgets := {}
  try
    let ((d, b), ms, t) ← timed do
      let sy ← sync cfg (some fun hash => blockCall hash :: firstCalls r hash)
      let s := sy.store
      let hash ← anchorHash cfg s
      prefetch cfg (blockCall hash :: firstCalls r hash)
      let b ← anchoredBlock cfg s
      let fx ← start cfg b r
      let d ← loop cfg b budgets r fx 0
      pure (d, b)
    let (pf, ptext) := provedFields d
    match command with
    | .call _ =>
      let (of, otext) := outcomeFields d.ran.outcome
      let node ← if args.compare then some <$> nodeCall cfg b r else pure none
      let nf := match node with | some n => [("endpoint_unchecked", Json.str n)] | none => []
      emit args.json (of ++ pf ++ nf ++ timingFields ms t) s!"{otext}\n{ptext}"
      if let some n := node then
        unless args.json do
          let same := match d.ran.outcome with
            | .answer a => if toHex a.result.output == n then " (equal)" else " (DIFFERENT)"
            | _ => ""
          IO.println s!"the endpoint's own eth_call (unchecked): {n}{same}"
    | .estimate _ =>
      match d.ran.outcome with
      | .answer a =>
        if !a.result.ok then
          let (of, otext) := outcomeFields d.ran.outcome
          emit args.json (of ++ pf) s!"estimate: the call fails without a gas limit named: {otext}"
        else
          -- succeeded with the gas it was given: bisect between the gas used and that limit
          let hi := r.gas.getD (b.el.gasLimit)
          let hi := min hi (a.result.gasUsed + budgets.executionGas)
          let lo := if a.result.gasUsed = 0 then 0 else a.result.gasUsed - 1
          let (g, _) ← bisect cfg b budgets r d.fetched lo hi
          emit args.json ([("estimate", jn g)] ++ pf)
            s!"{g}: the checked call succeeds with gas {g} and fails, or is refused, with {g - 1}\n{ptext}"
      | o =>
        let (of, otext) := outcomeFields o
        emit args.json (of ++ pf) s!"estimate: {otext}"
    unless args.json do IO.eprintln s!"done in {timingText ms t}"
    cleanup
    IO.Process.exit 0
  catch e =>
    cleanup
    IO.eprintln s!"error: {e}"
    IO.Process.exit 1
