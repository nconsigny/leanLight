import LeanLightEvmTests.Synthetic
import LeanLightEvm.Driver

/-!
# The proof-backed tier: facts read by leanLight's readers, then the call

A file of `tests/vectors/*-proofs-*.txt.gz` holds one block's header RLP and hash, a node's
`eth_getProof` answers and code, and the cases. Nothing in it is a fact until leanLight's readers
say so, through the same functions `LeanLightEvm.Driver.run` calls once the header is bound:

- the header: `LeanLight.Spec.Header.verifyB` (its RLP must hash to the block hash), then
  `LeanLightEvm.Driver.headerOf` on the field list `LeanLight.Lc.Anchor.fieldsB` reads;
- the accounts, slots and code: `LeanLightEvm.Driver.factsAt` under the header's state root
  (`LeanLight.Lc.Facts.storageAt` for each account and its slots, code kept only under the proved
  code hash it hashes to).

Then each case runs `LeanLightEvm.call` from no facts, each round served from the proved facts; a
key the proofs lack is served as an absent account (a key only a run on defaults reads), and an
answer counts only when every account and slot it read was proved (`provedReads`): a declared
code override is the only input that is not, and the report names it. The block hash is the
node's: there is no beacon store here to bind it (`Anchor.bind` is leanLight's, tested by its
own client tests), and the fork comes from `LeanLightEvm.Chain` by the header's timestamp.

Forged inputs, each on both files: a flipped byte in an account proof node, a truncated account
proof, two slots' proofs swapped, and a changed header byte; each must be refused by the
readers, and a case that reads the forged account must not give a proved answer.
-/

namespace LeanLightEvmTests.Proofs

open EthLib.Base
open EthLib.Execution.State (EMPTY_CODE_HASH)
open LeanLightEvm
open LeanLightEvmTests

/-- A proof-tier file as read, before any proof is checked. -/
structure PFile where
  name : String
  chainId : Nat := 0
  blockHash : ByteArray := .empty
  headerRlp : ByteArray := .empty
  codes : Array ByteArray := #[]
  /-- Account proofs in file order, each with its slot proofs. -/
  proofs : Array (Address × ByteArray × Array (Bytes32 × ByteArray)) := #[]
  cases : Array Case := #[]

def PFile.addSlot (f : PFile) (a : Address) (k : Bytes32) (nodes : ByteArray) : PFile :=
  match f.proofs.findIdx? (·.1 == a) with
  | some i => { f with proofs := f.proofs.modify i fun (a, n, ss) => (a, n, ss.push (k, nodes)) }
  | none => f

def parseP (name text : String) : Except String PFile := do
  let mut f : PFile := { name }
  let mut cur : Option Case := none
  let mut first := true
  let empty : VFile := { name }
  for l in text.splitOn "\n" do
    if first then
      unless l == "leanlight-evm-proofs 1" do throw "not leanlight-evm-proofs 1"
      first := false
      continue
    if l.isEmpty || l.startsWith "#" then continue
    let ws := words l
    let g (i : Nat) : String := ws[i]?.getD ""
    match ws.head?, cur with
    | some "chain", none => f := { f with chainId := ← dec (g 1) }
    | some "block", none => f := { f with blockHash := ← bytes (g 1) }
    | some "headerrlp", none => f := { f with headerRlp := ← bytes (g 1) }
    | some "code", none => f := { f with codes := f.codes.push (← bytes (g 1)) }
    | some "account", none =>
      let a ← addr (g 1)
      f := { f with proofs := f.proofs.push (a, ← bytes (g 2), #[]) }
    | some "slot", none => f := f.addSlot (← addr (g 1)) (← b32 (g 2)) (← bytes (g 3))
    | some "case", none => cur := some { file := name, name := rest l 1, chainId := f.chainId }
    | some "end", some c => f := { f with cases := f.cases.push c }; cur := none
    | _, some c => cur := some (← (parseLine empty c l).mapError fun e => s!"{c.name}: {e}")
    | _, none => throw s!"line outside a case: {l.take 40}"
  return f

def loadP (dir : System.FilePath) (name : String) : IO PFile := do
  let sums ← IO.FS.readFile (dir / "SHA256SUMS")
  let raw ← IO.FS.readBinFile (dir / name)
  let digest := toHex (Ssz.Sha256.hash raw)
  unless (sums.splitOn "\n").any (· == s!"{digest.drop 2}  {name}") do
    throw (IO.userError s!"{name}: SHA-256 {digest} is not in SHA256SUMS")
  let text ← readGz (dir / name)
  match parseP name (String.fromUTF8! text) with
  | .ok f => return f
  | .error e => throw (IO.userError s!"{name}: {e}")

/-- The call's header, from RLP that `verifyB` accepts under the block hash: the fields the EVM
reads, by `LeanLightEvm.Driver.headerOf` from the field list `Anchor.fieldsB` reads (what
`Driver.run` does once `Anchor.bind` has bound the RLP to the anchor); with the state root. -/
def headerAt (rlp blockHash : ByteArray) : Except String (Header × List UInt8) := do
  let some h := LeanLight.Spec.Header.verifyB rlp blockHash.data.toList
    | throw "the header's RLP does not hash to the block hash, or is not a header"
  let some fs := LeanLight.Lc.Anchor.fieldsB rlp | throw "header: no field list"
  let some hdr := LeanLightEvm.Driver.headerOf fs | throw "header: before Cancun"
  return (hdr, h.stateRoot)

/-- What the readers proved. -/
structure Proved where
  facts : Facts := {}
  accounts : Nat := 0
  absent : Nat := 0
  slots : Nat := 0
  code : Nat := 0
  failed : Array Address := #[]

/-- Every account proof of the file read under `root` by `LeanLightEvm.Driver.factsAt` (each
alone first, to count the ones the readers refuse), then all those it accepts together, with
the file's code given to each account whose proved code hash it hashes to. -/
def prove (f : PFile) (root : List UInt8) : Proved := Id.run do
  let mut p : Proved := {}
  let mut good : List LeanLightEvm.Driver.AccountProof := []
  for (a, nodes, ss) in f.proofs do
    let one : LeanLightEvm.Driver.AccountProof := { address := a, nodes, slots := ss.toList }
    match LeanLightEvm.Driver.factsAt root { accounts := [one] } with
    | .error _ => p := { p with failed := p.failed.push a }
    | .ok _ => good := good ++ [one]
  let some proved := (LeanLightEvm.Driver.factsAt root { accounts := good }).toOption
    | return { p with failed := p.failed.push (Vector.replicate 20 0) }
  let code := f.codes.toList.filterMap fun c =>
    let h := keccak c
    (proved.accounts.toList.find? fun (_, fact) => match fact with
      | .present _ _ ch _ => ch == h
      | .absent => false).map fun (a, _) => (a, c)
  let some facts := (LeanLightEvm.Driver.factsAt root { accounts := good, code }).toOption
    | return { p with failed := p.failed.push (Vector.replicate 20 0) }
  let absent := facts.accounts.toList.countP fun (_, fact) => fact matches .absent
  return { p with facts, accounts := facts.accounts.size - absent, absent
                  slots := facts.stateKeys - facts.accounts.size, code := facts.code.size }

/-- The facts of a case: the proved ones, with the case's declared code overrides (inputs of the
case, not facts of the chain). -/
def withOverrides (fs : Facts) (c : Case) : Facts := Id.run do
  let mut fs := fs
  for (a, b) in c.overrides do
    let h := keccak b
    let (n, bal, root) := match fs.accounts[a]? with
      | some (.present n bal _ root) => (n, bal, root)
      | _ => (0, 0, some EMPTY_STORAGE_ROOT)
    fs := { fs with accounts := fs.accounts.insert a (.present n bal h root) }
    if b.size > 0 then fs := { fs with code := fs.code.insert h b }
  return fs

/-- Whether every account and slot the answer read is proved (an overridden account's code is a
declared input). -/
def provedReads (proved : Facts) (a : Answer) : Bool :=
  a.reads.accounts.all (proved.accounts.contains ·) &&
    a.reads.slots.all fun (x, k) => proved.slotKnown x k

/-- One case on proved facts: discovery from nothing under the default budgets. -/
def runCase (f : PFile) (hdr : Header) (proved : Facts) (c : Case) (b : Budgets := {}) :
    Outcome × Nat := Id.run do
  let orc := withOverrides proved c
  let c := { c with header := hdr, chainId := f.chainId }
  let vf : VFile := { name := f.name }
  let d := discover vf c orc b
  return (d.outcome, d.rounds)

/-- The tier on one file: the readers, the cases, and the forged inputs. -/
def tier (t : Tally) (dir : System.FilePath) (name : String) : IO Tally := do
  let mut t := t
  let f ← loadP dir name
  let (hdr, root) ← match headerAt f.headerRlp f.blockHash with
    | .ok x => pure x
    | .error e => do
      return t.check false s!"{name}: {e}"
  let p := prove f root
  t := t.check p.failed.isEmpty s!"{name}: {p.failed.size} account proofs refused by the readers: {p.failed.toList.map vhex}"
  t := t.note s!"{name}: the readers proved {p.accounts} accounts, {p.absent} absences, {p.slots} slots and {p.code} codes under state root {toHex ⟨root.toArray⟩}"
  let mut same := 0
  let mut firstRead : Option (Case × Answer) := none
  for c in f.cases do
    let (o, rounds) := runCase f hdr p.facts c
    let c' := { c with header := hdr, chainId := f.chainId }
    let mut bad := mismatch c' o
    if bad.isSome && matchesSecond c' o then
      t := t.note s!"{name}: {c.name}: the two nodes disagreed; matches the second ({bad.getD ""})"
      bad := none
    if let (some _, some why) := (bad, refusedByDesign c' o) then
      t := t.note s!"{name}: {c.name}: refused by design: {why}"
      bad := none
    -- EIP-7610: an accessed candidate whose proved storage root is not empty (R3)
    if let .unsupported (.collisionUndecidable x) := o then
      if let some (.present 0 _ ch (some r)) := p.facts.accounts[x]? then
        if bad.isSome && ch == EMPTY_CODE_HASH && r != EMPTY_STORAGE_ROOT then
          t := t.note s!"{name}: {c.name}: refused by design: collision undecidable at {vhex x}, whose proved storage root is {vhex r} (R3)"
          bad := none
    -- over the round budget: by design only if the lifted budget gives the recorded answer
    if bad.isSome && isBudget .rounds o then
      let (o', r') := runCase f hdr p.facts c { rounds := liftedRounds }
      let ok' := match o' with
        | .answer a' => provedReads p.facts a' && ((mismatch c' o').isNone || matchesSecond c' o')
        | _ => false
      if ok' then
        t := t.note s!"{name}: {c.name}: over the round budget (refused by design at {({} : Budgets).rounds}): answered as recorded with {r'} rounds"
        bad := none
    if let .answer a := o then
      if !provedReads p.facts a then
        bad := some s!"read an account or slot that no proof gave: {o.show}"
      else if firstRead.isNone && c.overrides.isEmpty && c.request.to.isSome then
        firstRead := some (c, a)
    if bad.isNone then same := same + 1
    t := t.check bad.isNone s!"{name}: {c.name}: {bad.getD ""} ({rounds} rounds{if c.overrides.isEmpty then "" else ", code override declared"})"
  t := t.note s!"{name}: {same} of {f.cases.size} cases answered on proved facts as recorded"
  -- forged inputs
  let flip (b : ByteArray) (i : Nat) : ByteArray := ⟨b.data.modify i (· ^^^ 0x01)⟩
  let hdrBad := flip f.headerRlp (f.headerRlp.size / 3)
  t := t.check (headerAt hdrBad f.blockHash |>.toOption |>.isNone)
    s!"{name}: forged: a header byte flipped is refused"
  match firstRead with
  | none => t := t.check false s!"{name}: forged: no answered case to forge under"
  | some (c, a) =>
    -- the recipient's account proof, forged three ways
    let some target := c.request.to | pure ()
    let some i := f.proofs.findIdx? (·.1 == target) | do
      t := t.check false s!"{name}: forged: the recipient {vhex target} has no proof"
    let (_, nodes, ss) := f.proofs[i]!
    let forgedFiles : List (String × PFile) :=
      [("a byte of the account proof flipped", { f with proofs := f.proofs.set! i (target, flip nodes (nodes.size - 40), ss) }),
       ("the account proof truncated", { f with proofs := f.proofs.set! i (target, nodes.extract 0 (nodes.size - 1), ss) })] ++
      (match ss.toList with
       | (k1, n1) :: (k2, n2) :: rest =>
         [("two slot proofs swapped", { f with proofs := f.proofs.set! i (target, nodes, ((k1, n2) :: (k2, n1) :: rest).toArray) })]
       | _ => [])
    for (what, ff) in forgedFiles do
      let pf := prove ff root
      t := t.check (pf.failed.contains target && !pf.facts.accounts.contains target)
        s!"{name}: forged ({what}): the readers refuse {vhex target}"
      let (o, _) := runCase ff hdr pf.facts c
      let provedAnswer := match o with | .answer a' => provedReads pf.facts a' | _ => false
      t := t.check (!provedAnswer) s!"{name}: forged ({what}): {c.name} gives no proved answer: {o.show}"
    let _ := a
  return t

end LeanLightEvmTests.Proofs
