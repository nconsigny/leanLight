import LeanLightCli.Record

/-!
# `leanlight`

```
leanlight [--network mainnet|sepolia] --consensus-rpc URL [--execution-rpc URL]
          (--checkpoint 0xROOT | --unsafe-untrusted-checkpoint) [--json] [-v] COMMAND

--execution-rpc is required by every command but `sync`.
COMMAND:
  sync                    sync and print the finalized and anchored heads
  block-number            the anchored execution block's number
  balance ADDR            the account's balance (wei), proved
  nonce ADDR              the account's nonce, proved
  code ADDR               the code's hash and size, the code checked against the proved hash
  storage ADDR SLOT...    storage words, proved
  record DIR [FILE]       record a run (and FILE's reads) for the offline tests and benchmark
  queries FILE            one sync, then each line of FILE ("balance 0x..", "nonce 0x..",
                          "code 0x..", "storage 0x.. 0xSLOT..", "block-number")
```

Every value printed comes out of `LeanLight`'s checked readers. Timings go to standard error
(or into the JSON lines with `--json`): wall time, time waiting on the network, time verifying.

The arguments are checked before anything is fetched: options, the checkpoint's length, and
every read (a file's lines included). In `queries` mode a line that does not parse is reported,
and the other lines are read.
-/

open LeanLight.Cli
open LeanLight.Lc

structure Args where
  network : String := "mainnet"
  consensus : Option String := none
  execution : Option String := none
  checkpoint : Option String := none
  unsafeUntrustedCheckpoint : Bool := false
  json : Bool := false
  verbose : Bool := false
  rest : List String := []

/-- The options that take a value. -/
def valued : List String := ["--network", "--consensus-rpc", "--execution-rpc", "--checkpoint"]

partial def parseArgs : List String → Args → Except String Args
  | [], a => pure { a with rest := a.rest.reverse }
  | [o], a =>
    if valued.contains o then throw s!"{o} needs a value"
    else if o == "--unsafe-untrusted-checkpoint" then
      pure { a with unsafeUntrustedCheckpoint := true, rest := a.rest.reverse }
    else if o == "--json" then pure { a with json := true, rest := a.rest.reverse }
    else if o == "-v" then pure { a with verbose := true, rest := a.rest.reverse }
    else if o.startsWith "-" then throw s!"unknown option {o}"
    else pure { a with rest := (o :: a.rest).reverse }
  | o :: v :: r, a =>
    if valued.contains o then
      if v.startsWith "--" then throw s!"{o} needs a value, got {v}"
      else match o with
        | "--network" => parseArgs r { a with network := v }
        | "--consensus-rpc" => parseArgs r { a with consensus := some v }
        | "--execution-rpc" => parseArgs r { a with execution := some v }
        | _ => parseArgs r { a with checkpoint := some v }
    else if o == "--unsafe-untrusted-checkpoint" then
      parseArgs (v :: r) { a with unsafeUntrustedCheckpoint := true }
    else if o == "--json" then parseArgs (v :: r) { a with json := true }
    else if o == "-v" then parseArgs (v :: r) { a with verbose := true }
    else if o.startsWith "-" then throw s!"unknown option {o}"
    else parseArgs (v :: r) { a with rest := o :: a.rest }

def usage : String :=
  "usage: leanlight [--network mainnet|sepolia] --consensus-rpc URL [--execution-rpc URL] " ++
  "(--checkpoint 0xROOT | --unsafe-untrusted-checkpoint) [--json] [-v] (sync | block-number | balance ADDR | nonce ADDR | " ++
  "code ADDR | storage ADDR SLOT... | queries FILE | record DIR [FILE]); --execution-rpc is required but for sync"

/-! ## Reads, checked before anything is fetched -/

/-- A read, its arguments parsed. -/
inductive Query where
  | blockNumber
  | balance (text : String) (addr : ByteArray)
  | nonce (text : String) (addr : ByteArray)
  | code (text : String) (addr : ByteArray)
  | storage (text : String) (addr : ByteArray) (slots : List String) (keys : List ByteArray)

def hexArg (what s : String) : Except String ByteArray :=
  match hexBytes s with
  | some b => pure b
  | none => throw s!"{what}: not hex: {s}"

def addrArg (s : String) : Except String ByteArray := do
  let b ← hexArg "address" s
  if b.size != 20 then throw s!"address: not 20 bytes: {s}"
  pure b

def slotArg (s : String) : Except String ByteArray := do
  let b ← hexArg "slot" s
  if b.size > 32 then throw s!"slot: more than 32 bytes: {s}"
  pure (ByteArray.mk (List.replicate (32 - b.size) (0 : UInt8)).toArray ++ b)

/-- A read from its words, or why not. -/
def parseQuery : List String → Except String Query
  | ["block-number"] => pure .blockNumber
  | ["balance", a] => return .balance a (← addrArg a)
  | ["nonce", a] => return .nonce a (← addrArg a)
  | ["code", a] => return .code a (← addrArg a)
  | "storage" :: a :: slots@(_ :: _) => return .storage a (← addrArg a) slots (← slots.mapM slotArg)
  | ["storage", _] => throw "storage: no slot"
  | q => throw s!"unknown read: {" ".intercalate q}"

/-- The calls a read makes at the block `hash` (`runQuery`'s, so the batch answers them). -/
def callsOf (hash : ByteArray) : Query → List (String × Json)
  | .blockNumber => []
  | .balance _ a | .nonce _ a => [proofCall a [] hash]
  | .code _ a => [proofCall a [] hash, codeCall a hash]
  | .storage _ a _ ks => [proofCall a ks hash]

/-! ## Output -/

/-- A number as JSON. -/
def jn (n : Nat) : Json := .num (toString n)

def emit (json : Bool) (fields : List (String × Json)) (text : String) : IO Unit := do
  if json then IO.println (Json.mkObj fields).compress else IO.println text

/-- One read at the anchored block: its JSON fields and its text line. -/
def runQuery (cfg : Config) (b : Anchored) : Query → IO (List (String × Json) × String)
  | .blockNumber =>
    pure ([("q", Json.str "block-number"), ("value", (jn b.el.number))], s!"{b.el.number}")
  | .balance a addr => do
    let r ← readAccount cfg b addr []
    pure ([("q", Json.str "balance"), ("addr", Json.str a), ("block", (jn b.el.number)),
      ("value", Json.str (natHex r.account.balance))], s!"{r.account.balance}")
  | .nonce a addr => do
    let r ← readAccount cfg b addr []
    pure ([("q", Json.str "nonce"), ("addr", Json.str a), ("block", (jn b.el.number)),
      ("value", Json.str (natHex r.account.nonce))], s!"{r.account.nonce}")
  | .code a addr => do
    let r ← readAccount cfg b addr []
    let code ← readCode cfg b addr r.account
    pure ([("q", Json.str "code"), ("addr", Json.str a), ("block", (jn b.el.number)),
      ("value", Json.str (toHexL r.account.codeHash)), ("size", (jn code.size))],
      s!"{toHexL r.account.codeHash} ({code.size} bytes)")
  | .storage a addr slots ks => do
    let r ← readAccount cfg b addr ks
    let words := r.slots.map fun v => toHexL (beN 32 v)
    pure ([("q", Json.str "storage"), ("addr", Json.str a), ("block", (jn b.el.number)),
      ("slots", Json.arr (slots.toArray.map Json.str)),
      ("value", Json.arr (words.toArray.map Json.str))], " ".intercalate words)

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

/-- What the command asks for: nothing more than the sync, one read, or a file's reads (each
line's, or why it does not parse). -/
inductive Command where
  | sync
  | one (q : Query)
  | many (lines : List (String × Except String Query))

def parseCommand : List String → IO (Except String Command)
  | [] | ["sync"] => pure (.ok .sync)
  | ["queries", file] => do
    let lines ← try (pure (Except.ok (← IO.FS.lines file))) catch e => pure (.error s!"{file}: {e}")
    return lines.map fun ls =>
      let ls := ls.toList.map (·.trimAscii.toString) |>.filter fun l => !l.isEmpty && !l.startsWith "#"
      .many (ls.map fun l => (l, parseQuery ((l.splitOn " ").filter (· ≠ ""))))
  | q => pure ((parseQuery q).map .one)

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
  let some consensus := args.consensus | fail "--consensus-rpc is required"
  let checkpoint ← match args.checkpoint.mapM (hexArg "checkpoint") with
    | .ok (some c) => if c.size == 32 then pure (some c) else return ← fail "checkpoint: not 32 bytes"
    | .ok none =>
      if args.unsafeUntrustedCheckpoint then pure none
      else return ← fail "no checkpoint: pass --checkpoint 0xROOT, or --unsafe-untrusted-checkpoint to trust the beacon node's finalized root"
    | .error e => return ← fail e
  if let "record" :: dir :: rest := args.rest then
    let some exec := args.execution | return ← fail "--execution-rpc is required to record"
    let lines ← match rest with
      | [file] => do
        let ls ← IO.FS.lines file
        pure (ls.toList.map (·.trimAscii.toString) |>.filter fun l => !l.isEmpty && !l.startsWith "#")
      | [] => pure []
      | _ => return ← fail "record DIR [FILE]"
    let mut qs := []
    for l in lines do
      match parseQuery ((l.splitOn " ").filter (· ≠ "")) with
      | .ok q => qs := qs ++ [(l, q)]
      | .error e => return ← fail s!"{l}: {e}"
    let cfg : Config := {
      chain := chain
      consensus := consensus
      execution := exec
      checkpoint := checkpoint
      unsafeUntrustedCheckpoint := args.unsafeUntrustedCheckpoint
    }
    try
      -- each read's calls at the block `record` anchors
      Record.record cfg dir (qs.map fun (l, q) => (l, fun hash => callsOf hash q))
      cleanup
      return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 1
  let command ← match ← parseCommand args.rest with
    | .ok c => pure c
    | .error e => return ← fail e
  let execution := args.execution.getD ""
  if execution.isEmpty && !(command matches .sync) then
    return ← fail "--execution-rpc is required to read"
  let cfg : Config := {
    chain := chain
    consensus := consensus
    execution := execution
    checkpoint := checkpoint
    unsafeUntrustedCheckpoint := args.unsafeUntrustedCheckpoint
  }
  try
    let (sy, ms, t) ← timed (sync cfg)
    let s := sy.store
    let anchor := s.anchor.map (·.header.beacon.slot)
    emit args.json ([("phase", Json.str "sync"), ("finalized_slot", (jn s.finalized.beacon.slot)),
        ("anchor_slot", (jn (anchor.getD 0))), ("updates", (jn sy.updates)),
        ("accepted", (jn sy.accepted)),
        ("refused", Json.arr (sy.refused.reverse.toArray.map Json.str))] ++ timingFields ms t)
      s!"synced: finalized slot {s.finalized.beacon.slot}, anchor slot {anchor.getD 0}, {sy.updates} updates ({sy.accepted} accepted{if sy.refused.isEmpty then "" else s!", refused: {sy.refused.reverse}"}) in {timingText ms t}"
    match command with
    | .sync => pure ()
    | .many lines =>
      let qs := lines.filterMap fun (_, q) => q.toOption
      -- the block's header and every read's proofs and code, in one JSON-RPC batch
      let (b, ms, t) ← timed do
        let hash ← anchorHash cfg s
        prefetch cfg.execution (blockCall hash :: qs.flatMap (callsOf hash))
        anchoredBlock cfg s
      emit args.json ([("phase", Json.str "anchor"), ("block", (jn b.el.number)),
          ("hash", Json.str (toHex b.hash)), ("reads", (jn qs.length))] ++ timingFields ms t)
        s!"anchored block {b.el.number} {toHex b.hash}, {qs.length} reads fetched in {timingText ms t}"
      for (l, q) in lines do
        match q with
        | .error e =>
          emit args.json [("q", Json.str l), ("error", Json.str e)] s!"{l}: error: {e}"
        | .ok q =>
          try
            let ((fs, text), ms, t) ← timed (runQuery cfg b q)
            emit args.json (fs ++ timingFields ms t) s!"{l}: {text}   [{timingText ms t}]"
          catch e =>
            emit args.json [("q", Json.str l), ("error", Json.str (toString e))] s!"{l}: error: {e}"
    | .one q =>
      let ((fs, text), ms, t) ← timed do
        let hash ← anchorHash cfg s
        prefetch cfg.execution (blockCall hash :: callsOf hash q)
        let b ← anchoredBlock cfg s
        runQuery cfg b q
      emit args.json (fs ++ timingFields ms t) text
      unless args.json do IO.eprintln s!"read in {timingText ms t}"
    cleanup
    return 0
  catch e =>
    cleanup
    IO.eprintln s!"error: {e}"
    return 1
