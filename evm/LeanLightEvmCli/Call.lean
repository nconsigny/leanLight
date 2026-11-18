import LeanLightCli.Client
import LeanLightEvm

/-!
# The fetch-and-rerun loop of `leanlight-evm`

After `LeanLightCli`'s sync, a call runs at the anchored block in rounds: `LeanLightEvm.Driver.run`
reads what has been fetched through leanLight's readers and runs `LeanLightEvm.call`; when the
outcome is `needs`, this loop fetches what it names at the anchored block (an `eth_getProof` for
every needed account and slot, `eth_getCode` for every needed code, and the EIP-2935 history
contract's proofs when `BLOCKHASH` asks past the parent), and runs again. The entry's budgets
bound the rounds and the keys (`LeanLightEvm.Budgets`).

Like `LeanLightCli`, this loop is trusted and unproved: which calls it makes and in what order. It
cannot make a wrong answer pass: every fact reaches `call` only through `Driver.run`'s readers, and
`call` answers only when the run read nothing outside them. A bug here can make a call fail or
need more rounds.
-/

namespace LeanLightEvm.Cli

open LeanLight.Cli
open LeanLight.Lc
open LeanLightEvm
open LeanLightEvm.Driver
open EthLib.Base (Address Bytes32 Hash32)

/-- An address or a word as the bytes JSON-RPC takes. -/
def bytesOf {n : Nat} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

/-- 32 bytes of `b` as a word, if it has 32. -/
def word? (b : ByteArray) : Option Bytes32 := toVector 32 b.data.toList

/-- The history contract's address (EIP-2935). -/
def historyAddress : Address := (toVector 20 History.address).getD (Vector.replicate 20 0)

/-- The blocks whose hashes `BLOCKHASH` may ask at block `number`: the 256 before it (fewer near
genesis), oldest first. -/
def ancestorBlocks (number : Nat) : List Nat :=
  let k := min 256 number
  (List.range k).map (number - k + ·)

/-- An `eth_getProof` answer, its nodes joined as leanLight's readers take them, for `keys` in
the order asked. Untrusted: `Driver.run` reads it. -/
def proofOf (r : Json) (keys : List Bytes32) : Except String (ByteArray × List ByteArray) := do
  let nodes ← proofNodes (← r.getObjVal? "accountProof")
  let sp ← (← r.getObjVal? "storageProof").getArr?
  if sp.size != keys.length then throw "eth_getProof: wrong number of storage proofs"
  let slots ← sp.toList.mapM fun p => do proofNodes (← p.getObjVal? "proof")
  return (nodes, slots)

/-- The `eth_getProof` call of an account and slots at the anchored block. -/
def proofCallOf (b : Anchored) (a : Address) (keys : List Bytes32) : String × Json :=
  proofCall (bytesOf a) (keys.map bytesOf) b.hash

/-- What one round fetches: account proofs (with slots), code, and the history proofs. -/
structure Wants where
  proofs : List (Address × List Bytes32) := []
  code : List Address := []
  history : Bool := false

/-- Fetches `w` at the anchored block in one JSON-RPC batch, and adds it to `fx`. -/
def fetch (cfg : Config) (b : Anchored) (fx : Fetched) (w : Wants) : IO Fetched := do
  let blocks := ancestorBlocks b.el.number
  let historyKeys : List Bytes32 :=
    blocks.filterMap fun n => toVector 32 (History.slot n)
  let calls := w.proofs.map (fun (a, ks) => proofCallOf b a ks) ++
    w.code.map (fun a => codeCall (bytesOf a) b.hash) ++
    (if w.history then [proofCallOf b historyAddress historyKeys] else [])
  prefetch cfg calls
  let mut fx := fx
  for (a, ks) in w.proofs do
    let (m, ps) := proofCallOf b a ks
    let r ← orDie "eth_getProof" (← rpcC cfg m ps)
    let (nodes, slots) ← orDie "eth_getProof" (proofOf r ks)
    fx := { fx with accounts := fx.accounts ++ [{ address := a, nodes, slots := ks.zip slots }] }
  for a in w.code do
    let (m, ps) := codeCall (bytesOf a) b.hash
    let r ← orDie "eth_getCode" (← rpcC cfg m ps)
    let some code := hexBytes (← orDie "eth_getCode" r.getStr?) | die "eth_getCode: not hex"
    fx := { fx with code := fx.code ++ [(a, code)] }
  if w.history then
    let (m, ps) := proofCallOf b historyAddress historyKeys
    let r ← orDie "eth_getProof" (← rpcC cfg m ps)
    let (nodes, slots) ← orDie "eth_getProof (history)" (proofOf r historyKeys)
    fx := { fx with history := some (nodes, slots) }
  return fx

/-- The code to fetch with the accounts just proved: those whose proved code hash is not the
empty code's, so that the next run finds it. Read from `Driver.factsAt`, never from the
endpoint's account fields. -/
def codeWanted (cfg : Config) (b : Anchored) (fx : Fetched) (fresh : List Address) :
    IO (List Address) := do
  match factsAt b.el.stateRoot fx with
  | .error _ => return []
  | .ok f =>
    return fresh.filter fun a =>
      match f.accounts[a]? with
      | some (.present _ _ codeHash _) =>
        codeHash != EthLib.Execution.State.EMPTY_CODE_HASH && !f.code.contains codeHash
      | _ => false

/-- How a run of `loop` ended. -/
structure Done where
  ran : Ran
  rounds : Nat
  fetched : Fetched

/-- A `Stop` of the driver, as text. -/
def stopText : Stop → String
  | .noAnchor => "no anchor: the store is halted or too old"
  | .header => "the EL header does not bind to the anchor"
  | .proof a => s!"the proof of {toHex (bytesOf a)} does not verify under the anchored state root"
  | .code a => s!"the code of {toHex (bytesOf a)} does not hash to its proved code hash"
  | .history n => s!"the history contract's proof of block {n} does not verify"

/-- Runs `r` at the anchored block from the facts in `fx`, fetching what each run needs, until it
answers, refuses or is unsupported (the entry's budgets bound the rounds). -/
partial def loop (cfg : Config) (b : Anchored) (budgets : Budgets) (r : Request) (fx : Fetched)
    (round : Nat) : IO Done := do
  let now ← nowMs
  let res ← timeVerify do
    let now' ← nowMs
    pure (Driver.run cfg.chain b.store (max now now') b.rlp known budgets fx r round)
  let ran ← match res with
    | .ok ran => pure ran
    | .error s => die (stopText s)
  match ran.outcome with
  | .needs n =>
    log s!"  round {round}: needs {n.accounts.length} accounts, {n.slots.length} slots, {n.code.length} codes, {n.storageRoots.length} roots{if n.ancestors then ", ancestors" else ""}"
    let f := ran.input.facts
    -- slots grouped by account, with the accounts and storage roots asked
    let accts := (n.accounts ++ n.storageRoots).eraseDups
    let bySlot := n.slots.foldl (fun (acc : List (Address × List Bytes32)) (a, k) =>
      match acc.find? (·.1 == a) with
      | some _ => acc.map fun (a', ks) => if a' == a then (a', ks ++ [k]) else (a', ks)
      | none => acc ++ [(a, [k])]) []
    let proofs := accts.filter (fun a => !bySlot.any (·.1 == a)) |>.map (·, []) |> (· ++ bySlot)
    let code := f.accounts.toList.filterMap fun (a, fact) => match fact with
      | .present _ _ codeHash _ => if n.code.contains codeHash then some a else none
      | .absent => none
    let fx ← fetch cfg b fx { proofs, code, history := n.ancestors && fx.history.isNone }
    -- the code of accounts first proved now, fetched before the next run asks for it
    let more ← codeWanted cfg b fx accts
    let fx ← if more.isEmpty then pure fx else fetch cfg b fx { code := more }
    loop cfg b budgets r fx (round + 1)
  | _ => return { ran, rounds := round + 1, fetched := fx }

/-- The calls the first round makes, at the block `hash`: the sender's and the recipient's
proofs, and the recipient's code (checked against its proof when read). `sync` starts them while
it checks. -/
def firstCalls (r : Request) (hash : ByteArray) : List (String × Json) :=
  let accts := r.sender :: r.to.toList
  accts.map (fun a => proofCall (bytesOf a) [] hash) ++
    r.to.toList.map (fun a => codeCall (bytesOf a) hash)

/-- The first round's fetches: sender, recipient and the recipient's code. -/
def start (cfg : Config) (b : Anchored) (r : Request) : IO Fetched := do
  let accts := (r.sender :: r.to.toList).eraseDups
  let fx ← fetch cfg b {} { proofs := accts.map (·, []) }
  let more ← codeWanted cfg b fx accts
  if more.isEmpty then pure fx else fetch cfg b fx { code := more }

end LeanLightEvm.Cli
