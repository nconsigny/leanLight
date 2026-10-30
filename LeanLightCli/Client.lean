import LeanLight
import LeanLightCli.Util

/-!
# Sync and verified reads

The light client's loop, as Helios runs it, over `LeanLight`:

1. **Bootstrap** from a checkpoint root: `GET /eth/v1/beacon/light_client/bootstrap/{root}` (SSZ),
   decoded as the fork its `Eth-Consensus-Version` names (`Codec.decodeBootstrap`), then
   `Store.bootstrap` (the header's root is the checkpoint, the committee's branch, the age bound,
   every key validated).
2. **Updates**, period by period up to the clock's: `GET .../updates?start_period=p&count=n`
   (SSZ chunks tagged by fork digest, `Ssz.parseUpdates`), each through `Store.receive` (BLS
   signature of two thirds of the committee, branches, the sync protocol's rules).
3. **The finality and optimistic updates**, through `Store.receive` too.

The store's anchor is the newest attested header two thirds of the committee signed. A read is
answered at the execution block that header names: the block's header, rebuilt in RLP from
`eth_getBlockByHash`, must hash to the beacon header's execution block hash and match its fields
(`Anchor.bind`); an account and its storage are read from `eth_getProof`'s nodes under that
header's state root (`Facts.account`, `Facts.storage`), and code is accepted only when it hashes
to the proved code hash. The endpoint's own account fields are never read.
-/

namespace LeanLight.Cli

open LeanLight.Lc
open LeanLight.Lc.Forks (Chain ForkName)

def forkOfName : String → Option ForkName
  | "electra" => some .electra
  | "fulu" => some .fulu
  | "gloas" => some .gloas
  | _ => none

def verdictName : Store.Verdict → String
  | .halted => "halted"
  | .malformed => "malformed"
  | .unknownPeriod => "unknown period"
  | .tooOld => "too old"
  | .badSignature => "bad signature"
  | .conflict => "conflict"
  | .compared => "compared"
  | .irrelevant => "irrelevant"
  | .badKeys => "bad keys"
  | .accepted a l => s!"accepted (applied {a}, learned {l})"

structure Config where
  chain : Chain
  consensus : String
  execution : String
  checkpoint : Option ByteArray := none
  unsafeUntrustedCheckpoint : Bool := false

/-- What a sync did. -/
structure Synced where
  store : Store.Store
  updates : Nat := 0
  accepted : Nat := 0
  refused : List String := []

def die {α} (msg : String) : IO α := throw (IO.userError msg)

def orDie {α} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => die s!"{what}: {e}"

/-- Parse the finalized header response's root and check it is 32 bytes. -/
def finalizedRootOf (j : Json) : Except String ByteArray := do
  let root ← (← (← j.getObjVal? "data").getObjVal? "root").getStr?
  match hexBytes root with
  | some r =>
    if r.size != 32 then throw "root is not 32 bytes"
    pure r
  | none => throw "bad root"

/-- The checkpoint: the one given, else (with `--unsafe-untrusted-checkpoint`) the beacon node's
finalized root (trust on first use). -/
def checkpointOf (cfg : Config) : IO ByteArray := do
  if let some c := cfg.checkpoint then return c
  unless cfg.unsafeUntrustedCheckpoint do
    die "no checkpoint: pass --checkpoint 0xROOT, or --unsafe-untrusted-checkpoint to trust the beacon node's finalized root"
  let j ← orDie "finalized header" (← getJson s!"{cfg.consensus}/eth/v1/beacon/headers/finalized")
  let r ← orDie "finalized header" (finalizedRootOf j)
  IO.eprintln s!"checkpoint (the node's finalized root, unchecked): {toHex r}"
  return r

def bootstrapOf (cfg : Config) (root : ByteArray) (bs : ByteArray) (version : Option String) :
    IO Store.Store := do
  let some fork := version.bind forkOfName | die s!"bootstrap: fork {version} unknown"
  let now ← nowMs
  timeVerify do
    match Driver.start cfg.chain root now (.name fork) bs with
    | some s => pure s
    | none => die "bootstrap: refused (decoding, root, committee branch, age or keys)"

/-- One update through the store. -/
def receive (cfg : Config) (sy : Synced) (k : Codec.Kind) (tag : Codec.Tag) (bs : ByteArray) :
    IO Synced := do
  let now ← nowMs
  timeVerify do
    match Driver.feed cfg.chain sy.store now k tag bs with
    | (_, none) => pure { sy with updates := sy.updates + 1, refused := "undecodable" :: sy.refused }
    | (s, some v) =>
      log s!"  update: {verdictName v}"
      match v with
      | .accepted _ _ => pure { sy with store := s, updates := sy.updates + 1, accepted := sy.accepted + 1 }
      | .irrelevant | .compared => pure { sy with store := s, updates := sy.updates + 1 }
      | v => pure { sy with store := s, updates := sy.updates + 1, refused := verdictName v :: sy.refused }

def currentPeriod (c : Chain) : IO Nat := do
  return c.periodAt (c.slotOf (← nowMs))

/-- Updates from period `p` on, `count` of them, through the store. -/
def updatesFrom (cfg : Config) (sy : Synced) (bs : ByteArray) : IO Synced := do
  let some chunks := Ssz.parseUpdates bs | die "updates: bad framing"
  let mut sy := sy
  for ch in chunks do
    sy ← receive cfg sy .update (.digest ch.digest) ch.ssz
  return sy

/-- Bootstrap, then updates up to the clock's period, then the finality and optimistic updates.
The bootstrap, the clock period's update and the finality and optimistic updates are fetched
together, in one round trip (`getSszMany`); older periods' updates, when the checkpoint is older
than the clock's period, after the bootstrap. The store takes them in the specification's order. -/
def sync (cfg : Config) : IO Synced := do
  let root ← checkpointOf cfg
  let cur ← currentPeriod cfg.chain
  let lc := s!"{cfg.consensus}/eth/v1/beacon/light_client"
  let got ← getSszMany #[s!"{lc}/bootstrap/{toHex root}", s!"{lc}/updates?start_period={cur}&count=1",
    s!"{lc}/finality_update", s!"{lc}/optimistic_update"]
  let (bbs, bv) ← orDie "bootstrap" (got[0]?.getD (.error "missing answer"))
  let mut sy : Synced := { store := ← bootstrapOf cfg root bbs bv }
  -- periods before the clock's
  let mut guard := 0
  while Store.period cfg.chain sy.store < cur do
    guard := guard + 1
    if guard > 64 then break
    let p := Store.period cfg.chain sy.store
    let (bs, _) ← orDie "updates" (← getSsz
      s!"{lc}/updates?start_period={p}&count={min 128 (cur - p)}")
    let before := (Store.period cfg.chain sy.store, sy.store.next.isSome)
    sy ← updatesFrom cfg sy bs
    if (Store.period cfg.chain sy.store, sy.store.next.isSome) == before then break
  -- the clock's period, for its next committee
  if sy.store.next.isNone then
    match got[1]?.getD (.error "missing answer") with
    | .ok (bs, _) => sy ← updatesFrom cfg sy bs
    | .error e => log s!"updates for period {cur}: {e}"
  for (k, path, i) in [(Codec.Kind.finality, "finality_update", 2), (.optimistic, "optimistic_update", 3)] do
    let (bs, version) ← orDie path (got[i]?.getD (.error "missing answer"))
    let some fork := version.bind forkOfName | die s!"{path}: fork {version} unknown"
    sy ← receive cfg sy k (.name fork) bs
  return sy

/-! ## The RPC answers a batch prefetched -/

/-- Answers prefetched by one JSON-RPC batch (`prefetch`), by method and parameters. Only a cache
of the endpoint's words: each is checked where it is read, as a direct answer would be. -/
initialize rpcCache : IO.Ref (Std.HashMap String Json) ← IO.mkRef {}

def callKey (method : String) (params : Json) : String := method ++ params.compress

/-- A call, answered from the prefetched batch when it holds it. -/
def rpcC (url method : String) (params : Json) : IO (Except String Json) := do
  match (← rpcCache.get)[callKey method params]? with
  | some r => return .ok r
  | none => rpc url method params

/-- The calls, deduplicated, in one JSON-RPC batch; their answers kept for `rpcC`. -/
def prefetch (url : String) (calls : List (String × Json)) : IO Unit := do
  let calls := calls.foldl (fun acc c =>
    if acc.any (fun d => callKey d.1 d.2 == callKey c.1 c.2) then acc else acc.push c) #[]
  if calls.isEmpty then return
  let rs ← rpcBatch url calls
  for (c, r) in calls.toList.zip rs.toList do
    if let .ok j := r then rpcCache.modify (·.insert (callKey c.1 c.2) j)

/-- `eth_getBlockByHash` of the anchored block. -/
def blockCall (hash : ByteArray) : String × Json :=
  ("eth_getBlockByHash", .arr #[toHex hash, false])

/-- `eth_getProof` of an account and slots at a block. -/
def proofCall (addr : ByteArray) (slots : List ByteArray) (hash : ByteArray) : String × Json :=
  ("eth_getProof", .arr #[toHex addr, .arr (slots.toArray.map fun k => Json.str (toHex k)),
    toHex hash])

/-- `eth_getCode` of an account at a block. -/
def codeCall (addr : ByteArray) (hash : ByteArray) : String × Json :=
  ("eth_getCode", .arr #[toHex addr, toHex hash])

/-- The execution block hash the store's anchor names, if it anchors. -/
def anchorHash (cfg : Config) (s : Store.Store) : IO ByteArray := do
  let some a := Store.anchored cfg.chain s (← nowMs) | die "no anchor: the store is halted or too old"
  return a.header.elHash

/-! ## Reads at the anchor -/

/-- The header's fields in their RLP order (London to Amsterdam), and whether each is a quantity. -/
def headerFields : List (String × Bool) :=
  [("parentHash", false), ("sha3Uncles", false), ("miner", false), ("stateRoot", false),
   ("transactionsRoot", false), ("receiptsRoot", false), ("logsBloom", false),
   ("difficulty", true), ("number", true), ("gasLimit", true), ("gasUsed", true),
   ("timestamp", true), ("extraData", false), ("mixHash", false), ("nonce", false),
   ("baseFeePerGas", true), ("withdrawalsRoot", false), ("blobGasUsed", true),
   ("excessBlobGas", true), ("parentBeaconBlockRoot", false), ("requestsHash", false),
   ("blockAccessListHash", false), ("slotNumber", true)]

/-- The RLP of a block's header, rebuilt from `eth_getBlockByHash`'s fields via
`Spec.Header.encodeFieldsB` (`Spec.Header.decodeB_encodeFieldsB`). Untrusted: `Anchor.bind` checks
it hashes to the anchored block hash. -/
def headerRlp (block : Json) : Except String ByteArray := do
  let mut fields : List Spec.Rlp.Bytes := []
  for (name, quantity) in headerFields do
    match block.getObjVal? name with
    | .error _ => break
    | .ok v =>
      let s ← v.getStr?
      let field ← if quantity then
          match hexNat s with
          | some n => pure (Spec.Rlp.be n)
          | none => throw s!"{name}: not a quantity"
        else
          match hexBytes s with
          | some b => pure b.data.toList
          | none => throw s!"{name}: not hex"
      fields := fields ++ [field]
  match Spec.Header.encodeFieldsB fields with
  | some e => return e
  | none => throw "header: unknown fork or malformed field"

/-- An `eth_getProof` proof's nodes, joined in order as `Mpt.lookup` reads them. -/
def proofNodes (items : Json) : Except String ByteArray := do
  let arr ← items.getArr?
  let mut out := ByteArray.empty
  for it in arr do
    let some b := hexBytes (← it.getStr?) | throw "proof node: not hex"
    out := out ++ b
  return out

/-- The anchored block: its beacon header and the EL header's RLP, bound. -/
structure Anchored where
  /-- The store: each read checks freshness against a live clock (`nowMs`). -/
  store : Store.Store
  beacon : Store.Header
  rlp : ByteArray
  el : Spec.Header.Header
  hash : ByteArray

def anchoredBlock (cfg : Config) (s : Store.Store) : IO Anchored := do
  let now ← nowMs
  let some a := Store.anchored cfg.chain s now | die "no anchor: the store is halted or too old"
  let hash := a.header.elHash
  let (m, ps) := blockCall hash
  let block ← orDie "eth_getBlockByHash" (← rpcC cfg.execution m ps)
  let rlp ← orDie "header" (headerRlp block)
  let now ← nowMs
  timeVerify do
    match Driver.bindAnchor cfg.chain s now rlp with
    | some (b, h) => pure { store := s, beacon := b, rlp, el := h, hash }
    | none => die "header: the endpoint's block does not match the anchored execution block"

/-- What a verified read says. -/
structure AccountRead where
  account : Spec.Mpt.Account
  slots : List Nat

def readAccount (cfg : Config) (b : Anchored) (addr : ByteArray) (slots : List ByteArray) :
    IO AccountRead := do
  let (m, ps) := proofCall addr slots b.hash
  let r ← orDie "eth_getProof" (← rpcC cfg.execution m ps)
  let nodes ← orDie "accountProof" (proofNodes (← orDie "eth_getProof" (r.getObjVal? "accountProof")))
  let sp ← orDie "storageProof" do (← r.getObjVal? "storageProof").getArr?
  if sp.size != slots.length then die "eth_getProof: wrong number of storage proofs"
  let mut pairs : List (List UInt8 × ByteArray) := []
  for (k, p) in slots.zip sp.toList do
    let ns ← orDie "storage proof" do proofNodes (← p.getObjVal? "proof")
    pairs := pairs ++ [(k.data.toList, ns)]
  let now ← nowMs
  timeVerify do
    match Driver.read cfg.chain b.store now b.rlp addr.data.toList nodes pairs with
    | some (_, acct, vs) => pure { account := acct, slots := vs }
    | none => die "eth_getProof: the proof does not prove the account under the anchored state root"

/-- The code at `addr`, accepted only when it hashes to the proved code hash. -/
def readCode (cfg : Config) (b : Anchored) (addr : ByteArray) (acct : Spec.Mpt.Account) :
    IO ByteArray := do
  let (m, ps) := codeCall addr b.hash
  let r ← orDie "eth_getCode" (← rpcC cfg.execution m ps)
  let some code := hexBytes (← orDie "eth_getCode" r.getStr?) | die "eth_getCode: not hex"
  timeVerify do
    if Driver.codeOk acct code then pure code
    else die "eth_getCode: the code does not hash to the proved code hash"

end LeanLight.Cli
