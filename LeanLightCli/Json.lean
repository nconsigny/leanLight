/-!
# JSON

The little of JSON the command-line client needs: parsing the beacon API's and JSON-RPC's
answers, and writing requests. Lean core only: `Lean.Data.Json` would link the Lean compiler's
library into `leanlight` (a 119 MB binary using 66 MB before doing anything). Untrusted
plumbing, as `LeanLightCli.Util` is: a value is believed only once `LeanLight` checks it.
-/

namespace LeanLight.Cli

inductive Json where
  | null
  | bool (b : Bool)
  /-- A number, kept as its text: the client reads none of them as numbers but ids. -/
  | num (s : String)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving Inhabited

namespace Json

instance : Coe String Json := ⟨str⟩
instance : Coe Bool Json := ⟨bool⟩
instance {n : Nat} : OfNat Json n := ⟨num (toString n)⟩
instance : Coe Nat Json := ⟨fun n => num (toString n)⟩

def mkObj (kvs : List (String × Json)) : Json := obj kvs.toArray

def hexNib (n : Nat) : Char :=
  let d := n % 16
  Char.ofNat (if d < 10 then '0'.toNat + d else 'a'.toNat + (d - 10))

def escape (s : String) : String :=
  s.foldl (init := "\"") (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c => if c.toNat < 0x20 then acc ++ "\\u00" ++ (if c.toNat < 16 then "0" else "1") ++
        String.singleton (hexNib c.toNat) else acc.push c) ++ "\""

partial def compress : Json → String
  | null => "null"
  | bool b => toString b
  | num s => s
  | str s => escape s
  | arr xs => "[" ++ ",".intercalate (xs.toList.map compress) ++ "]"
  | obj kvs => "{" ++ ",".intercalate (kvs.toList.map fun (k, v) => escape k ++ ":" ++ compress v) ++ "}"

def getObjVal? (j : Json) (k : String) : Except String Json :=
  match j with
  | obj kvs => match kvs.find? (·.1 == k) with
    | some (_, v) => .ok v
    | none => .error s!"no field {k}"
  | _ => .error s!"not an object, looking for {k}"

def getObjValD (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD null

def getStr? : Json → Except String String
  | str s => .ok s
  | _ => .error "not a string"

def getArr? : Json → Except String (Array Json)
  | arr xs => .ok xs
  | _ => .error "not an array"

def getNat? : Json → Except String Nat
  | num s => match s.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: {s}"
  | _ => .error "not a number"

/-! ## Parsing -/

structure Parser where
  s : String
  i : String.Pos.Raw

abbrev P := StateT Parser (Except String)

def peek? : P (Option Char) := do
  let p ← get
  return if p.i < p.s.rawEndPos then some (p.i.get p.s) else none

def next : P Char := do
  let p ← get
  if p.i < p.s.rawEndPos then
    set { p with i := p.i.next p.s }
    return p.i.get p.s
  else throw "unexpected end"

partial def ws : P Unit := do
  match ← peek? with
  | some c => if c == ' ' || c == '\n' || c == '\r' || c == '\t' then let _ ← next; ws else pure ()
  | none => pure ()

def expect (c : Char) : P Unit := do
  let d ← next
  if d != c then throw s!"expected {c}, got {d}"

def word (w : String) : P Unit := w.toList.forM expect

def hexDig (c : Char) : P Nat :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
  else throw "bad \\u escape"

partial def strBody (acc : String) : P String := do
  match ← next with
  | '"' => return acc
  | '\\' =>
    match ← next with
    | '"' => strBody (acc.push '"')
    | '\\' => strBody (acc.push '\\')
    | '/' => strBody (acc.push '/')
    | 'b' => strBody (acc.push (Char.ofNat 8))
    | 'f' => strBody (acc.push (Char.ofNat 12))
    | 'n' => strBody (acc.push '\n')
    | 'r' => strBody (acc.push '\r')
    | 't' => strBody (acc.push '\t')
    | 'u' =>
      let a ← hexDig (← next); let b ← hexDig (← next)
      let c ← hexDig (← next); let d ← hexDig (← next)
      strBody (acc.push (Char.ofNat (((a * 16 + b) * 16 + c) * 16 + d)))
    | c => throw s!"bad escape {c}"
  | c => strBody (acc.push c)

partial def numBody (acc : String) : P String := do
  match ← peek? with
  | some c =>
    if c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' then
      let _ ← next; numBody (acc.push c)
    else return acc
  | none => return acc

mutual
partial def value : P Json := do
  ws
  match ← peek? with
  | some '{' => do
    let _ ← next
    ws
    if (← peek?) == some '}' then
      let _ ← next
      return obj #[]
    members #[]
  | some '[' => do
    let _ ← next
    ws
    if (← peek?) == some ']' then
      let _ ← next
      return arr #[]
    elements #[]
  | some '"' => do
    let _ ← next
    return str (← strBody "")
  | some 't' => word "true"; return bool true
  | some 'f' => word "false"; return bool false
  | some 'n' => word "null"; return null
  | some _ => return num (← numBody "")
  | none => throw "unexpected end"

partial def members (acc : Array (String × Json)) : P Json := do
  ws; expect '"'
  let k ← strBody ""
  ws; expect ':'
  let v ← value
  ws
  match ← next with
  | ',' => members (acc.push (k, v))
  | '}' => return obj (acc.push (k, v))
  | c => throw s!"expected , or }}, got {c}"

partial def elements (acc : Array Json) : P Json := do
  let v ← value
  ws
  match ← next with
  | ',' => elements (acc.push v)
  | ']' => return arr (acc.push v)
  | c => throw s!"expected , or ], got {c}"
end

def parse (s : String) : Except String Json :=
  match (do let v ← value; ws; pure v : P Json).run ⟨s, 0⟩ with
  | .ok (v, p) => if p.i < s.rawEndPos then .error "trailing characters" else .ok v
  | .error e => .error e

end Json

end LeanLight.Cli
