import LeanLightCli.Json
import Std.Data.HashMap

/-!
# Hex, JSON and `curl`

The command-line client's plumbing. Nothing here is trusted: every byte it fetches is checked
by `LeanLight` before it is believed, and a bug here can only make a read fail, never make a
wrong value pass (the values come out of `LeanLight`'s checked readers, never out of the JSON).
-/

namespace LeanLight.Cli

/-! ## Hex -/

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def strip0x (s : String) : String :=
  if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 |>.toString else s

/-- The bytes a `0x` hex string spells (an odd length gets a leading zero nibble). -/
def hexBytes (s : String) : Option ByteArray := Id.run do
  let cs := (strip0x s).toList
  let cs := if cs.length % 2 == 1 then '0' :: cs else cs
  let mut out := ByteArray.emptyWithCapacity (cs.length / 2)
  let mut rest := cs
  while true do
    match rest with
    | a :: b :: r =>
      match hexVal a, hexVal b with
      | some x, some y => out := out.push (x * 16 + y).toUInt8; rest := r
      | _, _ => return none
    | [] => break
    | _ => return none
  return some out

/-- A `0x` quantity. -/
def hexNat (s : String) : Option Nat :=
  (strip0x s).toList.foldlM (fun acc c => (hexVal c).map (acc * 16 + ·)) 0

def hexDigit (n : Nat) : Char := Json.hexNib n

def toHex (bs : ByteArray) : String :=
  bs.foldl (fun s b => (s.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) "0x"

def toHexL (bs : List UInt8) : String := toHex ⟨bs.toArray⟩

def natHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- `n` as `w` big-endian bytes. -/
def beN (w n : Nat) : List UInt8 := (List.range w).reverse.map fun i => (n / 256 ^ i % 256).toUInt8

/-! ## Time -/

/-- Milliseconds since the Unix epoch, read once from `date` and carried by the monotonic
clock after that. -/
initialize wallBase : IO.Ref (Option (Nat × Nat)) ← IO.mkRef none

def nowMs : IO Nat := do
  match ← wallBase.get with
  | some (wall, mono) => return wall + (← IO.monoMsNow) - mono
  | none =>
    let out ← IO.Process.output { cmd := "date", args := #["+%s%3N"] }
    if out.exitCode != 0 then throw (IO.userError s!"date: {out.stderr.trimAscii}")
    let some wall := out.stdout.trimAscii.toString.toNat?
      | throw (IO.userError s!"date: unexpected output: {out.stdout.trimAscii}")
    wallBase.set (some (wall, ← IO.monoMsNow))
    return wall

/-! ## Timing -/

initialize verbose : IO.Ref Bool ← IO.mkRef false

def log (s : String) : IO Unit := do
  if ← verbose.get then IO.eprintln s


/-- Time spent fetching and time spent verifying, in milliseconds (wall clock, monotonic). -/
structure Timing where
  netMs : Nat := 0
  verifyMs : Nat := 0
  requests : Nat := 0
  bytes : Nat := 0
  deriving Inhabited

initialize timing : IO.Ref Timing ← IO.mkRef {}

def timeNet {α} (act : IO (α × Nat)) : IO α := do
  let t0 ← IO.monoMsNow
  let (a, size) ← act
  let t1 ← IO.monoMsNow
  timing.modify fun t =>
    { t with netMs := t.netMs + (t1 - t0), requests := t.requests + 1, bytes := t.bytes + size }
  return a

def timeVerify {α} (act : IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  if ← verbose.get then IO.eprintln s!"  verified in {t1 - t0} ms"
  timing.modify fun t => { t with verifyMs := t.verifyMs + (t1 - t0) }
  return a

/-! ## HTTP through `curl` -/

/-- A scratch directory for binary answers. -/
initialize scratch : IO.Ref (Option System.FilePath) ← IO.mkRef none

def scratchDir : IO System.FilePath := do
  match ← scratch.get with
  | some d => return d
  | none =>
    let out ← IO.Process.output { cmd := "mktemp", args := #["-d", "/tmp/leanlight.XXXXXX"] }
    let d : System.FilePath := out.stdout.trimAscii.toString
    scratch.set (some d)
    return d

def cleanup : IO Unit := do
  if let some d := ← scratch.get then
    try IO.FS.removeDirAll d catch _ => pure ()

/-- A GET asking for SSZ: the body's bytes and the `Eth-Consensus-Version` header, or an error
with the status. -/
def getSsz (url : String) : IO (Except String (ByteArray × Option String)) := do
  let d ← scratchDir
  let body := d / "body"
  let hdrs := d / "headers"
  log s!"GET {url} (ssz)"
  timeNet do
    let out ← IO.Process.output { cmd := "curl", args := #["-sS", "--max-time", "60",
      "-H", "Accept: application/octet-stream", "-o", body.toString, "-D", hdrs.toString,
      "-w", "%{http_code}", url] }
    if out.exitCode != 0 then return (.error s!"curl: {out.stderr.trimAscii}", 0)
    let code := out.stdout.trimAscii.toString
    if code != "200" then
      let b ← (try IO.FS.readFile body catch _ => pure "")
      return (.error s!"HTTP {code}: {(b.take 200).toString}", 0)
    let bs ← IO.FS.readBinFile body
    let hs ← IO.FS.readFile hdrs
    let version := hs.splitOn "\n" |>.findSome? fun l =>
      let l := l.trimAscii.toString
      if l.toLower.startsWith "eth-consensus-version:" then
        some ((l.drop "eth-consensus-version:".length).trimAscii.toString.toLower)
      else none
    return (.ok (bs, version), bs.size)

/-- A GET of JSON. -/
def getJson (url : String) : IO (Except String Json) := do
  log s!"GET {url}"
  timeNet do
    let out ← IO.Process.output { cmd := "curl", args := #["-sS", "--max-time", "60",
      "-H", "Accept: application/json", url] }
    if out.exitCode != 0 then return (.error s!"curl: {out.stderr.trimAscii}", 0)
    return (Json.parse out.stdout, out.stdout.utf8ByteSize)

/-- One JSON-RPC call: its `result`, or the error. -/
def rpcOnce (url method : String) (params : Json) : IO (Except String Json) := do
  let req := Json.mkObj [("jsonrpc", "2.0"), ("id", (1 : Nat)), ("method", method),
    ("params", params)]
  log s!"POST {url} {method}"
  timeNet do
    let reqFile := (← scratchDir) / "request.json"
    IO.FS.writeFile reqFile req.compress
    let out ← IO.Process.output { cmd := "curl", args := #["-sS", "--max-time", "60", "-X", "POST",
      "-H", "Content-Type: application/json", "--data-binary", "@" ++ reqFile.toString, url] }
    if out.exitCode != 0 then return (.error s!"curl: {out.stderr.trimAscii}", 0)
    let size := out.stdout.utf8ByteSize
    match Json.parse out.stdout with
    | .error e => return (.error s!"{method}: not JSON: {e}: {(out.stdout.take 200).toString}", size)
    | .ok j =>
      match j.getObjVal? "result" with
      | .ok r => return (.ok r, size)
      | .error _ => return (.error s!"{method}: {(j.getObjValD "error").compress}", size)

/-- A JSON-RPC call, asked again up to twice after an error, 250 ms apart: a public endpoint is
a pool of nodes, and one behind the others refuses a block it does not hold yet. -/
def rpc (url method : String) (params : Json) : IO (Except String Json) := do
  let mut last := Except.error "no attempt"
  for i in [0:3] do
    if i > 0 then IO.sleep 250
    last ← rpcOnce url method params
    if last matches .ok _ then return last
    log s!"  {method}: attempt {i + 1} failed"
  return last

/-- The `Eth-Consensus-Version` of a response's headers, lower case. -/
def consensusVersion (hs : String) : Option String :=
  hs.splitOn "\n" |>.findSome? fun l =>
    let l := l.trimAscii.toString
    if l.toLower.startsWith "eth-consensus-version:" then
      some ((l.drop "eth-consensus-version:".length).trimAscii.toString.toLower)
    else none

/-- Several SSZ GETs in one `curl`, transferred in parallel over shared connections: each body
and its `Eth-Consensus-Version`, in the order asked. -/
def getSszMany (urls : Array String) : IO (Array (Except String (ByteArray × Option String))) := do
  let d ← scratchDir
  let mut args : Array String := #["-sS", "--max-time", "60", "--parallel", "--parallel-immediate",
    "-H", "Accept: application/octet-stream",
    "-w", "%{urlnum} %{http_code} %header{eth-consensus-version}\n"]
  for h : i in [0:urls.size] do
    log s!"GET {urls[i]} (ssz, batch {i})"
    args := args ++ #["-o", (d / s!"body{i}").toString, urls[i]]
  timeNet do
    let out ← IO.Process.output { cmd := "curl", args }
    let codes : Std.HashMap Nat (String × Option String) :=
      out.stdout.splitOn "\n" |>.foldl (init := {}) fun m l =>
        match l.trimAscii.toString.splitOn " " with
        | [n, c] => match n.toNat? with
          | some k => m.insert k (c, none)
          | none => m
        | [n, c, v] => match n.toNat? with
          | some k => m.insert k (c, some v.toLower)
          | none => m
        | _ => m
    let mut res := #[]
    let mut size := 0
    for i in [0:urls.size] do
      match codes[i]? with
      | some ("200", v) =>
        let bs ← IO.FS.readBinFile (d / s!"body{i}")
        size := size + bs.size
        res := res.push (.ok (bs, v))
      | some (c, _) =>
        let b ← (try IO.FS.readFile (d / s!"body{i}") catch _ => pure "")
        res := res.push (.error s!"HTTP {c}: {(b.take 200).toString}")
      | none => res := res.push (.error s!"curl: {out.stderr.trimAscii}")
    return (res, size)

/-- A JSON-RPC batch: each call's `result` or error, in the order asked. One HTTP request. -/
def rpcBatchOnce (url : String) (calls : Array (String × Json)) :
    IO (Except String (Array (Except String Json))) := do
  let req := Json.arr <| calls.mapIdx fun i (m, ps) => Json.mkObj
    [("jsonrpc", "2.0"), ("id", (i : Nat)), ("method", m), ("params", ps)]
  log s!"POST {url} batch of {calls.size}: {calls.map (·.1)}"
  timeNet do
    let reqFile := (← scratchDir) / "batch.json"
    IO.FS.writeFile reqFile req.compress
    let out ← IO.Process.output { cmd := "curl", args := #["-sS", "--max-time", "60", "-X", "POST",
      "-H", "Content-Type: application/json", "--data-binary", "@" ++ reqFile.toString, url] }
    if out.exitCode != 0 then return (.error s!"curl: {out.stderr.trimAscii}", 0)
    let size := out.stdout.utf8ByteSize
    match Json.parse out.stdout with
    | .error e => return (.error s!"batch: not JSON: {e}", size)
    | .ok (.arr items) =>
      let mut res : Array (Except String Json) := Array.replicate calls.size (.error "no answer")
      for it in items do
        match (it.getObjVal? "id" >>= Json.getNat?) with
        | .ok i =>
          if h : i < calls.size then
            let ans := match it.getObjVal? "result" with
              | .ok r => .ok r
              | .error _ => .error s!"{calls[i].1}: {(it.getObjValD "error").compress}"
            if hr : i < res.size then res := res.set i ans
        | .error _ => pure ()
      return (.ok res, size)
    | .ok j => return (.error s!"batch: not an array: {(j.compress.take 200).toString}", size)

/-- A JSON-RPC batch, asked again up to twice for the calls that failed (a public endpoint is a
pool of nodes, one of which may not hold the block yet). -/
def rpcBatch (url : String) (calls : Array (String × Json)) :
    IO (Array (Except String Json)) := do
  let mut res : Array (Except String Json) := Array.replicate calls.size (.error "no attempt")
  for attempt in [0:3] do
    let todo := (List.range calls.size).filterMap fun i =>
      match res[i]?, calls[i]? with
      | some (.ok _), _ => none
      | _, some c => some (i, c)
      | _, none => none
    if todo.isEmpty then break
    if attempt > 0 then IO.sleep 250
    match ← rpcBatchOnce url (todo.toArray.map (·.2)) with
    | .error e =>
      for (i, _) in todo do
        if hr : i < res.size then res := res.set i (.error e)
    | .ok rs =>
      for ((i, _), r) in todo.zip rs.toList do
        if hr : i < res.size then res := res.set i r
  return res

/-- A string field. -/
def str (j : Json) (k : String) : Except String String := do
  (← j.getObjVal? k).getStr?

end LeanLight.Cli
