import LeanLightEvm.Call
import LeanLight.Base.Sha256

/-!
# `leanlight-evm-test`'s vectors

The line format of `tests/vectors` (`tests/vectors/README.md`), read with no JSON library, each
file checked against `vectors/evm/SHA256SUMS` before it is parsed. A case becomes an
`LeanLightEvm.Input` through `Case.facts`, which the sweeps edit item by item (`Item`).
-/

namespace LeanLightEvmTests

open EthLib.Base
open EthLib.Execution.State (EMPTY_CODE_HASH)
open LeanLightEvm

/-! ## Hex -/

def nib (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def digits (s : String) : List Char :=
  match s.toList with
  | '0' :: 'x' :: r => r
  | r => r

def hexNat (s : String) : Option Nat :=
  (digits s).foldlM (fun acc c => (nib c).map (acc * 16 + ·)) 0

def unhexGo : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | a :: b :: r, acc =>
    match nib a, nib b with
    | some x, some y => unhexGo r (acc.push (UInt8.ofNat (x * 16 + y)))
    | _, _ => none
  | _, _ => none

def unhex (s : String) : Option ByteArray :=
  let cs := digits s
  unhexGo (if cs.length % 2 = 1 then '0' :: cs else cs) .empty

/-- Exactly `n` bytes, padded on the left. -/
def fixed (n : Nat) (s : String) : Option (Vector UInt8 n) := do
  let b ← unhex s
  if b.size > n then none else exactBytes? n (ByteArray.mk (Array.replicate (n - b.size) 0) ++ b)

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (b : ByteArray) : String :=
  "0x" ++ String.ofList (b.data.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

def vhex {n : Nat} (v : Vector UInt8 n) : String := toHex ⟨v.toArray⟩

def keccak (b : ByteArray) : Hash32 := EthLib.Cryptography.Hash.Keccak.keccak256 b

/-! ## Cases -/

/-- An account line: absent, or present with its code (none, held, or hash only) and root. -/
inductive Code where
  | none
  | held (idx : Nat)
  | hashOnly (h : Hash32)
  deriving Inhabited

structure AccountLine where
  absent : Bool := false
  nonce : Nat := 0
  balance : U256 := 0
  code : Code := .none
  root : Option Hash32 := none
  deriving Inhabited

inductive Expect where
  | ran (ok : Bool) (output : Option ByteArray) (err : Option String)
  | refused (reason : String)
  | hole (full : Bool) (candidate : Address)
  | none

structure Case where
  file : String := ""
  name : String := ""
  kind : String := ""
  chainId : Nat := 1
  header : Header := ⟨0, 0, 0, Vector.replicate 20 0, Vector.replicate 32 0, 0,
    Vector.replicate 32 0, 0, Vector.replicate 32 0⟩
  ancestors : Option (List Hash32) := none
  request : Request :=
    ({ sender := Vector.replicate 20 0, to := none, data := .empty, value := 0, gas := none })
  accounts : Array (Address × AccountLine) := #[]
  slots : Array (Address × Bytes32 × U256) := #[]
  overrides : Array (Address × ByteArray) := #[]
  expect : Expect := .none
  gas : Option Nat := none
  logs : Array (Address × List Hash32 × ByteArray) := #[]
  /-- EthLib's least passing gas and the node's estimate, when recorded. -/
  estimate : Option (Nat × Option Nat) := none
  /-- A second node's flag and output, when they differ from the first node's. -/
  second : Option (Bool × Option ByteArray) := none
  /-- Whether the recorded logs are compared (always, a recorded run with no log line having
  emitted none), except against a second node's answer, whose logs were not recorded. -/
  checkLogs : Bool := true

structure VFile where
  name : String
  /-- The code held, and its Keccak-256. -/
  codes : Array (ByteArray × Hash32) := #[]
  cases : Array Case := #[]

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def rest (l : String) (n : Nat) : String := " ".intercalate ((l.splitOn " ").drop n)

def addr (s : String) : Except String Address :=
  match fixed 20 s with | some a => .ok a | none => .error s!"bad address {s}"

def b32 (s : String) : Except String Bytes32 :=
  match fixed 32 s with | some a => .ok a | none => .error s!"bad word {s}"

def nat (s : String) : Except String Nat :=
  match hexNat s with | some n => .ok n | none => .error s!"bad number {s}"

def dec (s : String) : Except String Nat :=
  match s.toNat? with | some n => .ok n | none => .error s!"bad decimal {s}"

def bytes (s : String) : Except String ByteArray :=
  match unhex s with | some b => .ok b | none => .error s!"bad bytes {s.take 20}"

def u256 (s : String) : Except String U256 := do
  let n ← nat s
  if n < 2 ^ 256 then .ok (BitVec.ofNat 256 n) else .error "word too large"

def parseHeader (ws : List String) : Except String Header := do
  let g (i : Nat) : String := ws[i]?.getD ""
  return { number := ← nat (g 1), timestamp := ← nat (g 2), gasLimit := ← nat (g 3),
           coinbase := ← addr (g 4), prevRandao := ← b32 (g 5), excessBlobGas := ← nat (g 6),
           parentBeaconBlockRoot := ← b32 (g 7), slotNumber := ← nat (g 8),
           parentHash := ← b32 (g 9) }

def parseLine (f : VFile) (c : Case) (l : String) : Except String Case := do
  let ws := words l
  let g (i : Nat) : String := ws[i]?.getD ""
  match ws.head? with
  | some "kind" => return { c with kind := g 1 }
  | some "chain" => return { c with chainId := ← dec (g 1) }
  | some "header" => return { c with header := ← parseHeader ws }
  | some "ancestors" => return { c with ancestors := some (← (ws.drop 1).mapM b32) }
  | some "tx" =>
    let sender ← addr (g 1)
    let to ← if g 2 == "-" then pure none else some <$> addr (g 2)
    let value ← nat (g 3)
    let gas ← if g 4 == "-" then pure none else some <$> nat (g 4)
    let data ← bytes (g 5)
    return { c with request := { sender, to, value, gas, data } }
  | some "account" =>
    let a ← addr (g 1)
    if g 2 == "absent" then return { c with accounts := c.accounts.push (a, { absent := true }) }
    let code : Code ← match (g 4).toList with
      | ['-'] => pure .none
      | 'c' :: n => do
        let i ← dec (String.ofList n)
        unless i < f.codes.size do throw s!"code {i} not held"
        pure (.held i)
      | 'h' :: hs => .hashOnly <$> b32 (String.ofList hs)
      | _ => throw "bad code field"
    let root ← if g 5 == "-" then pure none else some <$> b32 (g 5)
    return { c with accounts := c.accounts.push (a,
      { nonce := ← nat (g 2), balance := ← u256 (g 3), code, root }) }
  | some "slot" => return { c with slots := c.slots.push (← addr (g 1), ← b32 (g 2), ← u256 (g 3)) }
  | some "override" => return { c with overrides := c.overrides.push (← addr (g 1), ← bytes (g 2)) }
  | some "expect" =>
    match g 1 with
    | "ran" =>
      let out ← if g 3 == "-" then pure none else some <$> bytes (g 3)
      let e : Expect := .ran (g 2 == "1") out (if g 4 == "-" then none else some (g 4))
      return { c with expect := e }
    | "refused" => return { c with expect := .refused (g 2) }
    | "hole" => return { c with expect := .hole (g 2 == "full") (← addr (g 3)) }
    | _ => throw "bad expect"
  | some "gas" => return { c with gas := some (← dec (g 1)) }
  | some "logs" =>
    unless g 1 == "unrecorded" do throw "bad logs line"
    return { c with checkLogs := false }
  | some "log" =>
    let topics ← if g 2 == "-" then pure [] else ((g 2).splitOn ",").mapM b32
    return { c with logs := c.logs.push (← addr (g 1), topics, ← bytes (g 3)) }
  | some "second" =>
    let out ← if g 2 == "-" then pure none else some <$> bytes (g 2)
    return { c with second := some (g 1 == "1", out) }
  | some "estimate" =>
    return { c with estimate := some (← dec (g 1), if g 2 == "-" then none else (g 2).toNat?) }
  | _ => throw s!"unknown line {l.take 40}"

def parse (name text : String) : Except String VFile := do
  let mut f : VFile := { name }
  let mut cur : Option Case := none
  let mut first := true
  for l in text.splitOn "\n" do
    if first then
      unless l == "leanlight-evm-vectors 1" do throw "not leanlight-evm-vectors 1"
      first := false
      continue
    if l.isEmpty || l.startsWith "#" then continue
    let ws := words l
    match ws.head?, cur with
    | some "code", _ =>
      let b ← bytes (ws[2]?.getD "")
      f := { f with codes := f.codes.push (b, keccak b) }
    | some "case", none => cur := some { file := name, name := rest l 1 }
    | some "end", some c => f := { f with cases := f.cases.push c }; cur := none
    | _, some c => cur := some (← (parseLine f c l).mapError fun e => s!"{c.name}: {e}")
    | _, none => throw s!"line outside a case: {l.take 40}"
  return f

/-! ## Reading, with the checksum -/

def readGz (path : System.FilePath) : IO ByteArray := do
  let out ← IO.Process.output { cmd := "gzip", args := #["-dc", path.toString] }
  if out.exitCode != 0 then throw (IO.userError s!"gzip -dc {path}: {out.stderr}")
  return out.stdout.toUTF8

/-- Read `dir/name`, refusing it unless its SHA-256 is the one `dir/SHA256SUMS` lists. -/
def load (dir : System.FilePath) (name : String) : IO VFile := do
  let sums ← IO.FS.readFile (dir / "SHA256SUMS")
  let raw ← IO.FS.readBinFile (dir / name)
  let digest := toHex (Ssz.Sha256.hash raw)
  let listed := (sums.splitOn "\n").any fun l => l == s!"{digest.drop 2}  {name}"
  unless listed do throw (IO.userError s!"{name}: SHA-256 {digest} is not in SHA256SUMS")
  let text ← readGz (dir / name)
  match parse name (String.fromUTF8! text) with
  | .ok f => return f
  | .error e => throw (IO.userError s!"{name}: {e}")

/-! ## Facts -/

/-- One fact of a case, as the sweeps withhold and corrupt them. -/
inductive Item where
  | account (a : Address)
  | slot (a : Address) (k : Bytes32)
  | code (h : Hash32)
  | root (a : Address)
  | ancestors
  deriving BEq

def Item.show : Item → String
  | .account a => s!"account {vhex a}"
  | .slot a k => s!"slot {vhex a} {vhex k}"
  | .code h => s!"code {vhex h}"
  | .root a => s!"root {vhex a}"
  | .ancestors => "ancestors"

/-- The facts of a case: its accounts with their code held under its Keccak-256 (the code a
proved code hash names), its slots, and its overrides (an override replaces the account's code
and code hash). `assumeEmpty` gives the listed accounts the empty storage root, which the
fixture did not record (stated in every report line that uses it). -/
def Case.facts (f : VFile) (c : Case) (assumeEmpty : List Address := []) : Facts := Id.run do
  let mut fs : Facts := {}
  for (a, l) in c.accounts do
    if l.absent then fs := { fs with accounts := fs.accounts.insert a .absent }
    else
      let root := if l.root.isNone && assumeEmpty.contains a then some EMPTY_STORAGE_ROOT else l.root
      let (codeHash, held) : Hash32 × Option ByteArray := match l.code with
        | .none => (EMPTY_CODE_HASH, none)
        | .held i => match f.codes[i]? with
          | some (b, h) => (h, some b)
          | none => (EMPTY_CODE_HASH, none)
        | .hashOnly h => (h, none)
      let (codeHash, held) := match c.overrides.find? (·.1 == a) with
        | some (_, b) => (keccak b, some b)
        | none => (codeHash, held)
      fs := { fs with accounts := fs.accounts.insert a (.present l.nonce l.balance codeHash root) }
      if let some b := held then
        if b.size > 0 then fs := { fs with code := fs.code.insert codeHash b }
  for (a, k, v) in c.slots do
    fs := { fs with slots := fs.slots.insert a ((fs.slots.getD a ∅).insert k v) }
  return fs

def Case.input (_ : VFile) (c : Case) (facts : Facts) (round : Nat := 0) : Input :=
  { chainId := c.chainId, header := c.header, ancestors := c.ancestors, facts, request := c.request,
    round }

/-- Every item of a set of facts (and the ancestors when given). -/
def items (fs : Facts) (ancestors : Bool) : Array Item := Id.run do
  let mut out : Array Item := #[]
  for (a, fact) in fs.accounts.toList do
    out := out.push (.account a)
    if let .present _ _ _ (some _) := fact then out := out.push (.root a)
  for (a, ks) in fs.slots.toList do
    for (k, _) in ks.toList do out := out.push (.slot a k)
  for (h, _) in fs.code.toList do out := out.push (.code h)
  if ancestors then out := out.push .ancestors
  return out

/-- The facts with one item withheld. Withholding an account withholds its slots: a proof of a
slot comes with its account's proof. -/
def withhold (fs : Facts) : Item → Facts
  | .account a => { fs with accounts := fs.accounts.erase a, slots := fs.slots.erase a }
  | .slot a k => { fs with slots := fs.slots.insert a ((fs.slots.getD a ∅).erase k) }
  | .code h => { fs with code := fs.code.erase h }
  | .root a => match fs.accounts[a]? with
    | some (.present n b c _) => { fs with accounts := fs.accounts.insert a (.present n b c none) }
    | _ => fs
  | .ancestors => fs

/-- The ways to corrupt one item (the code is corrupted apart: `Facts.check` refuses it). -/
def corruptions (fs : Facts) : Item → List (String × Facts)
  | .account a => match fs.accounts[a]? with
    | some (.present n b c r) =>
      let set (x : AccountFact) := { fs with accounts := fs.accounts.insert a x }
      [("balance", set (.present n (b + 1) c r)), ("nonce", set (.present (n + 1) b c r))] ++
        (if (fs.slots.getD a ∅).isEmpty then [("absent", set .absent)] else [])
    | some .absent =>
      let fact : AccountFact := .present 0 1 EMPTY_CODE_HASH (some EMPTY_STORAGE_ROOT)
      [("present", { fs with accounts := fs.accounts.insert a fact })]
    | none => []
  | .slot a k =>
    let v := ((fs.slots.getD a ∅)[k]?).getD 0
    [("value", { fs with slots := fs.slots.insert a ((fs.slots.getD a ∅).insert k (v + 1)) })]
  | .root a => match fs.accounts[a]? with
    | some (.present n b c (some r)) =>
      let other : Hash32 := if r == EMPTY_STORAGE_ROOT then keccak (ByteArray.mk #[1]) else EMPTY_STORAGE_ROOT
      if other == EMPTY_STORAGE_ROOT && !(fs.slots.getD a ∅).toList.all (·.2 == 0) then []
      else [("root", { fs with accounts := fs.accounts.insert a (.present n b c (some other)) })]
    | _ => []
  | _ => []

end LeanLightEvmTests
