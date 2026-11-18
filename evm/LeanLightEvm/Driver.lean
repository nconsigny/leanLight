import LeanLightEvm.Call
import LeanLight.Driver
import LeanLight.El.History

/-!
# A checked `eth_call` at the light client's anchor

`LeanLightEvm.Driver.run` is what a client calls with the bytes it fetched: leanLight's store,
the clock, the EL header's RLP, `eth_getProof` nodes for the accounts and slots a call needs,
code bytes, and optionally the history contract's proofs for `BLOCKHASH`. It turns them into the
input of `LeanLightEvm.call` only through leanLight's own readers, and runs it:

* **The header.** The store's anchor at the clock (`Store.anchored`), the EL header bound to it
  by `Anchor.bind` (Keccak-256 of the RLP is the anchored beacon header's execution block hash,
  and its fields agree with the beacon block). The EVM's header fields (`COINBASE`,
  `PREVRANDAO`, the excess blob gas, the parent beacon block root, the slot number, the parent
  hash) are read from the field list of the same RLP (`Anchor.fieldsB`, which `bind` reads too).
* **Accounts and slots.** Each account's proof is read by `Facts.storageAt` under that header's
  state root, with its slots under the account's storage root. An account the trie proves absent
  reads as the empty account, and becomes an absent fact: from Spurious Dragon on (EIP-161) a
  state holds no empty account, which EIP-7523 makes a rule on every chain past the Merge, so the
  empty account and no account are one state. Its slots are left out: an absent account's
  storage is empty, which `call` knows without them.
* **Code.** Code fetched for an account is kept only when it hashes to the code hash its proof
  proved (`LeanLight.Lc.Driver.codeOk`), and then under that hash.
* **Ancestors.** Without history proofs, `BLOCKHASH` knows only the parent's hash (the header's
  `parentHash`), and `call` asks for more when a run needs them. With them, each of the 256 (or
  fewer, near genesis) hashes before the anchored block is read by `History.blockHash` from the
  EIP-2935 history contract under the same state root, which the anchored block's state holds.

Any proof that does not verify stops the run (`Stop`): nothing the endpoint says is used unless a
reader accepted it. `LeanLightEvmProofs.Driver` states what an answer then means.
-/

namespace LeanLightEvm.Driver

open EthLib.Base
open LeanLight LeanLight.Lc
open LeanLight.Lc.Forks (Chain)

/-- An `eth_getProof` answer for one account, as fetched (untrusted). -/
structure AccountProof where
  /-- The account. -/
  address : Address
  /-- The account proof's nodes, joined in order. -/
  nodes : ByteArray
  /-- Each slot asked, with its proof's nodes joined. -/
  slots : List (Bytes32 × ByteArray) := []

/-- What a client fetched for one run (untrusted until read). -/
structure Fetched where
  /-- The accounts' proofs, with their slots'. -/
  accounts : List AccountProof := []
  /-- Code fetched for an account (`eth_getCode`). -/
  code : List (Address × ByteArray) := []
  /-- The history contract's account proof, and the slot proof of each block from the oldest of
  the (up to) 256 before the anchored block to its parent. -/
  history : Option (ByteArray × List ByteArray) := none

/-- Why the driver did not run the call. -/
inductive Stop where
  /-- The store has no anchor at this clock (halted, or older than `MAX_AGE`). -/
  | noAnchor
  /-- The EL header does not bind to the anchor, or lacks the fields from Cancun on. -/
  | header
  /-- An account's proof does not prove it, or its slots, under the anchored state root. -/
  | proof (a : Address)
  /-- Code that does not hash to its account's proved code hash, or for an account with no
  present fact. -/
  | code (a : Address)
  /-- The history contract's proofs do not prove a hash of block `n`. -/
  | history (n : Nat)
  deriving Repr

/-- The bytes `l` as a vector of `n`, if `l` has `n`. -/
def toVector (n : Nat) (l : List UInt8) : Option (Vector UInt8 n) :=
  if h : l.toArray.size = n then some ⟨l.toArray, h⟩ else none

/-- A 32-byte field, or 32 zero bytes when it has another length (none does: `Anchor.bind`
checks every field's shape). -/
def bytes32 (l : List UInt8) : Bytes32 := (toVector 32 l).getD (Vector.replicate 32 0)

/-- The EVM's header from an EL header's field list (Yellow Paper order, `Spec.Header.shapes`):
parent hash (0), coinbase (2), number (8), gas limit (9), timestamp (11), mixHash as
`PREVRANDAO` (13), excess blob gas (18), parent beacon block root (19), slot number (22, from
Amsterdam; 0 before). None for a header of fewer than 20 fields (before Cancun), whose blob and
beacon fields the EVM would otherwise read as zero. -/
def headerOf (fs : List (List UInt8)) : Option Header := do
  if fs.length < 20 then none
  let f (i : Nat) := Spec.Header.field fs i
  let coinbase ← toVector 20 (f 2)
  return { number := Spec.Rlp.beValue (f 8), timestamp := Spec.Rlp.beValue (f 11)
           gasLimit := Spec.Rlp.beValue (f 9), coinbase, prevRandao := bytes32 (f 13)
           excessBlobGas := Spec.Rlp.beValue (f 18), parentBeaconBlockRoot := bytes32 (f 19)
           slotNumber := if 23 ≤ fs.length then Spec.Rlp.beValue (f 22) else 0
           parentHash := bytes32 (f 0) }

/-- The fact an account read is: absent for the empty account (module doc), else present with
its nonce, balance, code hash and storage root. -/
def factOf (acct : Spec.Mpt.Account) : AccountFact :=
  if acct = Spec.Mpt.emptyAccount then .absent
  else .present acct.nonce (BitVec.ofNat 256 acct.balance) (bytes32 acct.codeHash)
    (some (bytes32 acct.storageRoot))

/-- The facts after one account's read: the account, and its slots when it is present. -/
def addRead (f : Facts) (a : Address) (acct : Spec.Mpt.Account) (keys : List Bytes32)
    (vs : List Nat) : Facts :=
  let fact := factOf acct
  match fact with
  | .absent => { f with accounts := f.accounts.insert a fact }
  | .present .. =>
    let slots := (keys.zip vs).foldl (fun m (k, v) => m.insert k (BitVec.ofNat 256 v))
      (f.slots.getD a ∅)
    { f with accounts := f.accounts.insert a fact
             slots := if keys.isEmpty then f.slots else f.slots.insert a slots }

/-- The accounts' proofs read one after the other under the state root `stateRoot` by
`LeanLight.Lc.Facts.storageAt` (the account under the state root, its slots under the account's
storage root), each added to `f` (`addRead`); the first that does not verify stops. -/
def readAccounts (stateRoot : List UInt8) : List AccountProof → Facts → Except Stop Facts
  | [], f => .ok f
  | p :: ps, f =>
    match LeanLight.Lc.Facts.storageAt stateRoot p.address.toList p.nodes
        (p.slots.map fun (k, nodes) => (k.toList, nodes)) with
    | none => .error (.proof p.address)
    | some (acct, vs) => readAccounts stateRoot ps (addRead f p.address acct (p.slots.map (·.1)) vs)

/-- Code fetched for accounts, each kept in `f` only under the code hash that `proved` holds for
its account, when it hashes to it (`LeanLight.Lc.Driver.codeOk`'s check); code for an account
with no present fact, or that hashes to something else, stops. Code under the empty code's hash
is never kept: the entry never asks for it, and EthLib's state reads it without a lookup. -/
def readCode (proved : Facts) : List (Address × ByteArray) → Facts → Except Stop Facts
  | [], f => .ok f
  | (a, code) :: rest, f =>
    match proved.accounts[a]? with
    | some (.present _ _ codeHash _) =>
      if Spec.Common.keccak code.data.toList == codeHash.toList then
        if codeHash == EthLib.Execution.State.EMPTY_CODE_HASH then readCode proved rest f
        else readCode proved rest { f with code := f.code.insert codeHash code }
      else .error (.code a)
    | _ => .error (.code a)

/-- The facts `fx` proves under the state root `stateRoot`: its accounts and slots
(`readAccounts`), then its code (`readCode`). -/
def factsAt (stateRoot : List UInt8) (fx : Fetched) : Except Stop Facts := do
  let proved ← readAccounts stateRoot fx.accounts {}
  readCode proved fx.code proved

/-- The hashes of blocks `n`, `n + 1`, ..., one a slot proof of `slotNodes`, each read by
`History.blockHash` under `stateRoot` with the history contract's account proof `accountNodes`. -/
def ancestorsFrom (stateRoot : List UInt8) (accountNodes : ByteArray) :
    Nat → List ByteArray → Except Stop (List Hash32)
  | _, [] => .ok []
  | n, sp :: sps =>
    match History.blockHash stateRoot accountNodes sp n with
    | some h => (bytes32 h :: ·) <$> ancestorsFrom stateRoot accountNodes (n + 1) sps
    | none => .error (.history n)

/-- The hashes of the blocks before block `number`, oldest first, the parent's last (at most
256), each read by `History.blockHash` under `stateRoot` from the history proofs. -/
def ancestorsOf (stateRoot : List UInt8) (number : Nat) (accountNodes : ByteArray)
    (slotNodes : List ByteArray) : Except Stop (List Hash32) :=
  let k := min 256 number
  if slotNodes.length = k then ancestorsFrom stateRoot accountNodes (number - k) slotNodes
  else .error (.history (number - k))

/-- A run of the driver: the outcome of `call`, with the anchored block it ran at. -/
structure Ran where
  /-- `call`'s outcome. -/
  outcome : Outcome
  /-- The anchored beacon header. -/
  beacon : Store.Header
  /-- The EL header bound to it. -/
  el : Spec.Header.Header
  /-- The input `call` ran on. -/
  input : Input

/-- The input of `call` at an EL header already bound (`el`, and `fs` its RLP's field list): the
EVM's header from the fields, the facts and ancestors read from `fx` under `el`'s state root. -/
def inputAt (c : Chain) (table : List ChainRules) (el : Spec.Header.Header)
    (fs : List (List UInt8)) (fx : Fetched) (r : Request) (round : Nat) : Except Stop Input := do
  let some header := headerOf fs | throw .header
  let facts ← factsAt el.stateRoot fx
  let ancestors ← match fx.history with
    | none => pure none
    | some (ap, sps) => some <$> ancestorsOf el.stateRoot el.number ap sps
  return { table, chainId := c.chainId, header, ancestors, facts, request := r, round }

/-- **The checked `eth_call` at the anchor** (module doc): the anchor of `s` at clock `now`, the
EL header `rlp` bound to it by `Anchor.bind`, the input read from `fx` under its state root
(`inputAt`), then `call` with the rules of `table`, the budgets `b`, the request `r` and the round
`round`. -/
def run (c : Chain) (s : Store.Store) (now : Nat) (rlp : ByteArray) (table : List ChainRules)
    (b : Budgets) (fx : Fetched) (r : Request) (round : Nat) : Except Stop Ran := do
  let some a := Store.anchored c s now | throw .noAnchor
  let some el := Anchor.bind c a.header rlp | throw .header
  let some fs := Anchor.fieldsB rlp | throw .header
  let input ← inputAt c table el fs fx r round
  return { outcome := call b input, beacon := a.header, el, input }

end LeanLightEvm.Driver
