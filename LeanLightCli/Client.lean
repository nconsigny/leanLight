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
  | .future => "signature slot after the clock's slot"
  | .unknownPeriod => "unknown period"
  | .tooOld => "too old"
  | .badSignature => "bad signature"
  | .conflict => "conflict"
  | .compared => "compared"
  | .irrelevant => "irrelevant"
  | .nextMismatch => "next committee differs from the store's"
  | .badKeys => "bad keys"
  | .accepted a l => s!"accepted (applied {a}, learned {l})"

structure Config where
  chain : Chain
  consensus : String
  execution : String
  checkpoint : Option ByteArray := none
  unsafeUntrustedCheckpoint : Bool := false
  /-- More beacon nodes, asked with `consensus` at once: the first answer that verifies is used. -/
  consensusMore : Array String := #[]
  /-- More execution endpoints, asked with `execution` at once, likewise. -/
  executionMore : Array String := #[]

/-- Every beacon node, `consensus` first. -/
def Config.beacons (cfg : Config) : Array String := #[cfg.consensus] ++ cfg.consensusMore

/-- Every execution endpoint, `execution` first. -/
def Config.endpoints (cfg : Config) : Array String := #[cfg.execution] ++ cfg.executionMore

/-- What a sync did. -/
structure Synced where
  store : Store.Store
  updates : Nat := 0
  accepted : Nat := 0
  refused : List String := []
  /-- Updates skipped because they repeat a signature the store checked (`sameSigned`). -/
  repeated : Nat := 0

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
    IO (Option Store.Store) := do
  let some fork := version.bind forkOfName
    | log s!"  bootstrap: fork {version} unknown"; return none
  timeVerify do
    let now ← nowMs
    let r := Driver.start cfg.chain root now (.name fork) bs
    if r.isNone then log "  bootstrap: refused (decoding, root, committee branch or age)"
    pure r

/-- Whether an update's verdict is a refusal (it did not decode, or the store refused it). -/
def Synced.lastRefused (before after : Synced) : Bool := after.refused.length > before.refused.length

/-- One update through the store. -/
def receive (cfg : Config) (sy : Synced) (k : Codec.Kind) (tag : Codec.Tag) (bs : ByteArray) :
    IO Synced := do
  timeVerify do
    let now ← nowMs
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

/-! ## The RPC answers a batch prefetched -/

/-- Answers prefetched by one JSON-RPC batch (`prefetch`), by method and parameters. Only a cache
of the endpoint's words: each is checked where it is read, as a direct answer would be. -/
initialize rpcCache : IO.Ref (Std.HashMap String Json) ← IO.mkRef {}

def callKey (method : String) (params : Json) : String := method ++ params.compress

/-- A call, answered from the prefetched batch when it holds it, else by the first execution
endpoint that answers. -/
def rpcC (cfg : Config) (method : String) (params : Json) : IO (Except String Json) := do
  match (← rpcCache.get)[callKey method params]? with
  | some r => return .ok r
  | none =>
    let mut last := Except.error "no execution endpoint"
    for url in cfg.endpoints do
      last ← rpc url method params
      if last matches .ok _ then return last
    return last

/-- Prefetches still running (the speculative one `sync` starts); `prefetch` waits for them. -/
initialize pending : IO.Ref (Array (Task (Except IO.Error Unit))) ← IO.mkRef #[]

/-- The calls not yet cached, deduplicated, in one JSON-RPC batch to every execution endpoint at
once; each answer kept for `rpcC`, until every call has one. -/
def prefetchNow (cfg : Config) (calls : List (String × Json)) : IO Unit := do
  let cache ← rpcCache.get
  let calls := calls.foldl (fun acc c =>
    if cache.contains (callKey c.1 c.2) || acc.any (fun d => callKey d.1 d.2 == callKey c.1 c.2)
    then acc else acc.push c) #[]
  if calls.isEmpty then return
  let tasks ← spawnEach cfg.endpoints (fun _ url => rpcBatch url calls)
    (Array.replicate calls.size (.error "the request failed"))
  discard <| firstOf tasks fun (ir : Nat × Array (Except String Json)) => do
    for (c, r) in calls.toList.zip ir.2.toList do
      if let .ok j := r then rpcCache.modify (·.insert (callKey c.1 c.2) j)
    let cache ← rpcCache.get
    return if calls.all fun c => cache.contains (callKey c.1 c.2) then some () else none

/-- `prefetchNow`, once the prefetches still running have finished. -/
def prefetch (cfg : Config) (calls : List (String × Json)) : IO Unit := do
  for t in ← pending.get do discard (IO.wait t)
  pending.set #[]
  prefetchNow cfg calls

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

/-! ## Sync -/

/-- An update's bytes decoded as the fork `version` names, as `Driver.feed` decodes them. -/
def decodeAs (cfg : Config) (k : Codec.Kind) (version : Option String) (bs : ByteArray) :
    Option Store.Update :=
  (version.bind forkOfName).bind fun f => Codec.decodeUpdate Codec.mainnet cfg.chain k (.name f) bs

/-- Whether two updates carry the same signature over the same header: attested header, aggregate
and signature slot. A beacon node's optimistic update usually repeats its finality update's; the
store has then checked that signature, and skipping the repeat leaves it reached from the
checkpoint all the same (`LeanLightProofs.Driver.feed_reaches`: a skipped update is a step not
taken). -/
def sameSigned (a b : Store.Update) : Bool :=
  a.attested.root.data == b.attested.root.data && a.aggregate.bits.data == b.aggregate.bits.data &&
    a.aggregate.signature.data == b.aggregate.signature.data && a.signatureSlot == b.signatureSlot

/-- Starts fetching, in the background, the block and `wanted`'s calls at the execution block an
optimistic update's attested header names, before the update is checked: when the checked
store anchors there, the reads find their answers cached. Unchecked answers are only a cache,
each checked where it is read (`rpcC`). -/
def speculate (cfg : Config) (wanted : ByteArray → List (String × Json))
    (optimistic : Except String (ByteArray × Option String)) : IO Unit := do
  let .ok (bs, v) := optimistic | return
  let some u := decodeAs cfg .optimistic v bs | return
  let h := u.attested.elHash
  log s!"  fetching the reads at {toHex h} while checking"
  let t ← IO.asTask (prio := .dedicated) (prefetchNow cfg (blockCall h :: wanted h))
  pending.modify (·.push t)

/-- One beacon node's answers: the bootstrap, the clock period's update, the finality update and
the optimistic update. -/
abbrev Bundle := Array (Except String (ByteArray × Option String))

/-- From a store: updates for the periods before the clock's `cur`, the clock period's when the
store lacks the next committee, then the finality and optimistic updates, each taken from node
`k`'s bundle first (`sync`'s, or `refresh`'s, whose bundles have no bootstrap). -/
def advance (cfg : Config) (sy : Synced) (cur : Nat) (bundles : Array (Task (Nat × Bundle)))
    (k : Nat) : IO Synced := do
  let lc (src : String) := s!"{src}/eth/v1/beacon/light_client"
  -- object `j` of the first bundle, after `k`'s, that `use` takes
  let order := k :: (List.range bundles.size).filter (· != k)
  let tryEach {β} (j : Nat) (use : ByteArray × Option String → IO (Option β)) : IO (Option β) := do
    for i in order do
      let some t := bundles[i]? | continue
      let answer : Option (Except String (ByteArray × Option String)) := (← IO.wait t).2[j]?
      match answer with
      | some (.ok x) => if let some b ← use x then return some b
      | some (.error e) => log s!"  {cfg.beacons[i]?.getD ""}: {e}"
      | none => pure ()
    return none
  let mut sy := sy
  -- periods before the clock's
  let mut guard := 0
  while Store.period cfg.chain sy.store < cur do
    guard := guard + 1
    if guard > 64 then break
    let p := Store.period cfg.chain sy.store
    let path := s!"updates?start_period={p}&count={min 128 (cur - p)}"
    let asks ← spawnEach cfg.beacons (fun _ src => getSsz s!"{lc src}/{path}") (.error "the request failed")
    let some bs ← firstOf asks fun (ir : Nat × Except String (ByteArray × Option String)) =>
        return match ir.2 with | .ok (bs, _) => some bs | _ => none
      | die s!"updates from period {p}: no beacon node answered"
    let before := (Store.period cfg.chain sy.store, sy.store.next.isSome)
    sy ← updatesFrom cfg sy bs
    if (Store.period cfg.chain sy.store, sy.store.next.isSome) == before then break
  -- the clock's period, for its next committee
  if sy.store.next.isNone then
    let sy0 := sy
    if let some sy' ← tryEach 1 fun (bs, _) => do
        let sy' ← try updatesFrom cfg sy0 bs catch _ => pure sy0
        return if sy0.lastRefused sy' then none else some sy'
    then sy := sy'
  -- The finality and optimistic updates: node `k`'s (or, when the store refuses it, the next
  -- node's), then every other node's that has arrived, so that a node fast but behind does not
  -- hold the anchor back: the store keeps the better. One signed header is checked once
  -- (`sameSigned`): a node's optimistic update usually repeats its finality update's.
  let mut seen : Array Store.Update := #[]
  for (j, kind, name) in [(2, Codec.Kind.finality, "finality update"), (3, .optimistic, "optimistic update")] do
    let mut taken := false
    for i in order do
      let some t := bundles[i]? | continue
      if taken && !(← IO.hasFinished t) then continue
      let answer : Option (Except String (ByteArray × Option String)) := (← IO.wait t).2[j]?
      let some (.ok (bs, v)) := answer | continue
      let some fork := v.bind forkOfName | continue
      if let some u := decodeAs cfg kind v bs then
        if seen.any (sameSigned u) then
          log s!"  {name} from {cfg.beacons[i]?.getD ""}: a signed header checked already"
          sy := { sy with repeated := sy.repeated + 1 }
          taken := true
          continue
        seen := seen.push u
      let sy0 := sy
      let sy' ← receive cfg sy0 kind (.name fork) bs
      if sy0.lastRefused sy' then
        sy := { sy' with refused := sy0.refused }
      else
        sy := sy'
        taken := true
    if !taken then sy := { sy with refused := name :: sy.refused }
  return sy

/-- Bootstrap, then updates up to the clock's period, then the finality and optimistic updates.

Every beacon node is asked at once for the bootstrap, the clock period's update and the
finality and optimistic updates, in one round trip each (`getSszMany`); the bootstrap is the
first that verifies, and each other object is taken from that node, or from the next when the
store refuses it. Older periods' updates, when the checkpoint is older than the clock's period,
come after the bootstrap, from the first node to answer. With `wanted` (the reads to make), the
reads at the block the optimistic update names are fetched while all this is checked
(`speculate`). The store takes the updates in the specification's order. -/
def sync (cfg : Config) (wanted : Option (ByteArray → List (String × Json)) := none) :
    IO Synced := do
  discard scratchDir
  let root ← checkpointOf cfg
  let cur ← currentPeriod cfg.chain
  let lc (src : String) := s!"{src}/eth/v1/beacon/light_client"
  let failed : Array (Except String (ByteArray × Option String)) :=
    Array.replicate 4 (.error "the request failed")
  let bundles ← spawnEach cfg.beacons (fun _ src => getSszMany #[s!"{lc src}/bootstrap/{toHex root}",
    s!"{lc src}/updates?start_period={cur}&count=1", s!"{lc src}/finality_update",
    s!"{lc src}/optimistic_update"]) failed
  let some (k, got, s0) ← firstOf bundles fun (ig : Nat × Array (Except String (ByteArray × Option String))) => do
      let (i, got) := ig
      let a0 : Option (Except String (ByteArray × Option String)) := got[0]?
      match a0 with
      | some (.ok (bs, v)) => return (← bootstrapOf cfg root bs v).map fun s => (i, got, s)
      | some (.error e) => log s!"  bootstrap from {cfg.beacons[i]?.getD ""}: {e}"; return none
      | none => return none
    | die "bootstrap: no beacon node gave one that verifies (decoding, root, committee branch or age)"
  if cfg.beacons.size > 1 then log s!"  bootstrap from {cfg.beacons[k]?.getD ""}"
  if let some w := wanted then speculate cfg w (got[3]?.getD (.error "missing"))
  advance cfg { store := s0 } cur bundles k

/-- The store kept after `sync`: every beacon node asked at once for the clock period's update
and the finality and optimistic updates, then one `advance`. -/
def refresh (cfg : Config) (sy : Synced) : IO Synced := do
  let cur ← currentPeriod cfg.chain
  let lc (src : String) := s!"{src}/eth/v1/beacon/light_client"
  let failed : Bundle := Array.replicate 4 (.error "the request failed")
  -- no bootstrap: index 0 left empty, so the bundles read as `sync`'s
  let bundles ← spawnEach cfg.beacons (fun _ src => do
    return #[.error "no bootstrap"] ++ (← getSszMany #[s!"{lc src}/updates?start_period={cur}&count=1",
      s!"{lc src}/finality_update", s!"{lc src}/optimistic_update"])) failed
  advance cfg sy cur bundles 0

/-- After `sync`, the store kept, as Helios runs: once a slot, 4 s in (when the beacon node has
the previous slot's signatures), `refresh`, and `onHead` each time the anchor moves to another
slot. A round that fails (the network, an answer that does not decode) is reported and the next
slot's tried; the store only ever changes through `Driver.feed`. Stops when the store halts. -/
partial def follow (cfg : Config) (sy : Synced) (last : Option Nat) (onHead : Synced → IO Unit) :
    IO Unit := do
  let now ← nowMs
  let wake := cfg.chain.slotTime (cfg.chain.slotOf now + 1) + 4000
  IO.sleep (wake - now).toUInt32
  timing.set {}
  let sy ← try refresh cfg sy catch e => do IO.eprintln s!"follow: {e}"; pure sy
  if sy.store.halted.isSome then die "the store halted: two conflicting updates were signed"
  let slot := (Store.anchored cfg.chain sy.store (← nowMs)).map (·.header.beacon.slot)
  if slot.isSome && slot != last then onHead sy
  follow cfg sy (slot.orElse fun _ => last) onHead

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
  let block ← orDie "eth_getBlockByHash" (← rpcC cfg m ps)
  let rlp ← orDie "header" (headerRlp block)
  timeVerify do
    let now ← nowMs
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
  let r ← orDie "eth_getProof" (← rpcC cfg m ps)
  let nodes ← orDie "accountProof" (proofNodes (← orDie "eth_getProof" (r.getObjVal? "accountProof")))
  let sp ← orDie "storageProof" do (← r.getObjVal? "storageProof").getArr?
  if sp.size != slots.length then die "eth_getProof: wrong number of storage proofs"
  let mut pairs : List (List UInt8 × ByteArray) := []
  for (k, p) in slots.zip sp.toList do
    let ns ← orDie "storage proof" do proofNodes (← p.getObjVal? "proof")
    pairs := pairs ++ [(k.data.toList, ns)]
  timeVerify do
    let now ← nowMs
    match Driver.read cfg.chain b.store now b.rlp addr.data.toList nodes pairs with
    | some (_, acct, vs) => pure { account := acct, slots := vs }
    | none => die "eth_getProof: the proof does not prove the account under the anchored state root"

/-- The code at `addr`, accepted only when it hashes to the proved code hash. -/
def readCode (cfg : Config) (b : Anchored) (addr : ByteArray) (acct : Spec.Mpt.Account) :
    IO ByteArray := do
  let (m, ps) := codeCall addr b.hash
  let r ← orDie "eth_getCode" (← rpcC cfg m ps)
  let some code := hexBytes (← orDie "eth_getCode" r.getStr?) | die "eth_getCode: not hex"
  timeVerify do
    if Driver.codeOk acct code then pure code
    else die "eth_getCode: the code does not hash to the proved code hash"

end LeanLight.Cli
