import LeanLight.Forks
import LeanLight.Ssz.Containers
import LeanLight.Bls.Fav

/-!
# The store: Altair's sync protocol, as amended through Gloas

The light client's store: consensus-specs v1.7.0-beta.5's `initialize_light_client_store`,
`validate_light_client_update`, `process_light_client_update`, `apply_light_client_update`,
`is_better_update` and `process_light_client_store_force_update`
(`altair/light-client/sync-protocol.md`, as Capella, Deneb, Electra and Gloas amend them). The
store holds the specification's `LightClientStore` (`finalized`, `current`, `next`, `best`,
`optimistic`, `previousMaxActive`, `currentMaxActive`) and keeps it as the specification does:
`LeanLightProofs.SyncProtocol` proves that every update `receive` accepts,
`process_light_client_update` (transcribed in `LeanLightProofs.Spec.SyncProtocol`) accepts at the
clock's slot with the same resulting store, and that every other update leaves that part as it
was (`receive_refines`, `reaches_spec`). leanLight refuses more than the specification, never
less, and never changes what an accepted update does:

* **Two thirds.** An update below two thirds of the committee (`3·signers ≥ 2·size`) is refused
  before BLS (the specification takes one participant); the anchor reads are answered from is
  the newest attested header two thirds signed, the first verified winning at one slot
  (`moveAnchor`).
* **No forced update in the client.** `forceUpdate` is the specification's
  `process_light_client_store_force_update`, which a client "MAY" call; leanLight's client never
  calls it (a finalized header moves only on two thirds' finality). The tests call it on the
  specification's vectors.
* **Conflicts halt** (G2): an update whose signature verifies under a committee the store holds
  for its signature period is compared, before the relevance check, with the finalized
  checkpoints and committee roots the store keeps; two checkpoints of one epoch with different
  roots, or two committees of one period, halt the store, and the pair is kept (`conflictOf`).
* **The age bound.** `MAX_AGE` holds on every update against `effNow`, the clock or the newest
  verified attested slot's time, whichever is later (G6), as well as the specification's
  `current_slot ≥ signature_slot` (`.future`).
* **Forks.** Headers from the chain table's first fork (Electra) on, an Electra or Fulu
  container only before Gloas; `signature_slot` a `uint64`.
* **Committee keys are not validated**, as in the specification and Helios: a committee enters
  the store as its keys' and aggregate key's 48-byte encodings (`Committee.ofSync`), proved by
  its root. A signature check decodes only what it needs (`signersKey?`): when more than half
  signed, the committee's aggregate key less the absent keys, else the participants' keys, with
  no subgroup check. On a committee as the chain holds one (every key passes KeyValidate, the
  aggregate their sum) that is the specification's `FastAggregateVerify` over the participants'
  keys (`LeanLightProofs.SyncProtocol.verifySignature_spec`); the theorems that need it take it
  as a hypothesis (`Committee.Consistent`, `Valid`).

The objects are normalized, preset- and fork-independent forms of the SSZ containers
(`LeanLight.Codec` builds them from the bytes): a `Header` keeps its beacon header, what its
execution branch proves (`Exec`) and the branch; an `Update` is a `LightClientUpdate`, a
finality or optimistic update entering with its missing fields empty, as the specification
does. A header's execution branch is checked at its own slot's fork (`isValidHeader`):
an Electra or Fulu container proves the payload header at gindex 25; a Gloas container proves
`execution_block_hash` at 2856 from `GLOAS_FORK_EPOCH` on, and at 812, its branch normalized to
11 roots, before it (an earlier header brought into a Gloas container,
`upgrade_lc_header_to_gloas`). The store keeps headers in the form they were validated in:
`get_lc_execution_root` and every check give the same answer for an Electra header and its
upgrade, so the specification's `upgrade_lc_store_to_gloas` changes nothing here.

What the store keeps is bounded: `maxCheckpoints` finalized checkpoints, `maxRoots` committee
roots and `maxPast` past committees, each list cut to its newest entries, and checkpoints older
than `MAX_AGE` dropped.
-/

namespace LeanLight.Lc.Store

open LeanLight.Lc.Ssz (BeaconBlockHeader SyncCommittee SyncAggregate ExecutionPayloadHeader
  isValidNormalizedBranch hash64 subtree zeroChunk)
open LeanLight.Lc.Forks (Chain Preset ForkName computeDomain signingRoot domainSyncCommittee)

/-! ## Bounds -/

/-- Finalized checkpoints kept at most: 14 days of mainnet epochs are 3,150. -/
def maxCheckpoints : Nat := 4096

/-- Committee roots kept at most, one per period. -/
def maxRoots : Nat := 32

/-- Past committees kept at most, with their keys, to verify an older period's update. -/
def maxPast : Nat := 16

/-! ## Objects -/

/-- Whether every byte of `b` is zero. -/
def isZero (b : ByteArray) : Bool := b.data.all (· == 0)

/-- Whether every root of a branch is zero. -/
def allZero (bs : Array ByteArray) : Bool := bs.all isZero

/-- What a header's execution branch proves. -/
inductive Exec where
  /-- An Electra or Fulu container: the payload header, whose root sits at gindex 25. -/
  | payload (e : ExecutionPayloadHeader)
  /-- A Gloas container: `execution_block_hash`, at 2856 from the Gloas fork on, at 812 before
  it. -/
  | blockHash (h : ByteArray)

/-- A `LightClientHeader`, normalized. -/
structure Header where
  beacon : BeaconBlockHeader
  exec : Exec
  branch : Array ByteArray

namespace Header

/-- `hash_tree_root(header.beacon)`: what a sync aggregate signs and a checkpoint names. -/
def root (h : Header) : ByteArray := h.beacon.root

/-- The EL block hash the header names: the payload's `block_hash`, or `execution_block_hash`. -/
def elHash (h : Header) : ByteArray :=
  match h.exec with
  | .payload e => e.blockHash
  | .blockHash b => b

/-- Whether an execution payload header is `ExecutionPayloadHeader.empty()`. -/
def payloadEmpty (e : ExecutionPayloadHeader) : Bool :=
  isZero e.parentHash && isZero e.feeRecipient && isZero e.stateRoot && isZero e.receiptsRoot &&
    isZero e.logsBloom && isZero e.prevRandao && e.blockNumber == 0 && e.gasLimit == 0 &&
    e.gasUsed == 0 && e.timestamp == 0 && e.extraData.size == 0 && e.baseFeePerGas == 0 &&
    isZero e.blockHash && isZero e.transactionsRoot && isZero e.withdrawalsRoot &&
    e.blobGasUsed == 0 && e.excessBlobGas == 0

/-- Whether the header is `LightClientHeader.empty()`: every field zero. -/
def isEmpty (h : Header) : Bool :=
  h.beacon.slot == 0 && h.beacon.proposerIndex == 0 && isZero h.beacon.parentRoot &&
    isZero h.beacon.stateRoot && isZero h.beacon.bodyRoot &&
    (match h.exec with
      | .payload e => payloadEmpty e
      | .blockHash b => isZero b) &&
    allZero h.branch

end Header

/-- `is_valid_light_client_header`, at the header's own slot's fork: none before the table's
first fork; an Electra or Fulu container, only before Gloas, proves its payload header's root
at gindex 25 under `body_root` by a branch of exactly 4 roots (`ExecutionBranch`, checked by
`is_valid_merkle_branch`, not normalized); a Gloas container proves `execution_block_hash` at 2856 from the
Gloas fork on, at 812 before it. Branches are normalized (`is_valid_normalized_merkle_branch`). -/
def isValidHeader (c : Chain) (h : Header) : Bool :=
  match c.forkOfSlot h.beacon.slot with
  | none => false
  | some f =>
    match h.exec with
    | .payload e =>
      f != .gloas && h.branch.size == Ssz.gindexExecutionPayload.log2 &&
        isValidNormalizedBranch e.root h.branch Ssz.gindexExecutionPayload h.beacon.bodyRoot
    | .blockHash b =>
      isValidNormalizedBranch b h.branch
        (if f == .gloas then Ssz.gindexExecutionBlockHashGloas else Ssz.gindexExecutionBlockHashDeneb)
        h.beacon.bodyRoot

/-- Whether `slot` is at or past `ELECTRA_FORK_EPOCH`. -/
def electraAt (c : Chain) (slot : Nat) : Bool := decide (c.epochOf .electra ≤ c.epochAt slot)

/-- `finalized_root_gindex_at_slot`: 735 from the Gloas fork on, 169 from Electra, else 105. -/
def finalizedGindex (c : Chain) (slot : Nat) : Nat :=
  if c.gloasAt slot then Ssz.gindexFinalizedRootGloas
  else if electraAt c slot then Ssz.gindexFinalizedRootElectra else Ssz.gindexFinalizedRootAltair

/-- `current_sync_committee_gindex_at_slot`: 2945 from the Gloas fork on, 86 from Electra, else
54. -/
def currentGindex (c : Chain) (slot : Nat) : Nat :=
  if c.gloasAt slot then Ssz.gindexCurrentSyncCommitteeGloas
  else if electraAt c slot then Ssz.gindexCurrentSyncCommitteeElectra
  else Ssz.gindexCurrentSyncCommitteeAltair

/-- `next_sync_committee_gindex_at_slot`: 2946 from the Gloas fork on, 87 from Electra, else 55. -/
def nextGindex (c : Chain) (slot : Nat) : Nat :=
  if c.gloasAt slot then Ssz.gindexNextSyncCommitteeGloas
  else if electraAt c slot then Ssz.gindexNextSyncCommitteeElectra
  else Ssz.gindexNextSyncCommitteeAltair

/-! ### Committees -/

/-- `hash_tree_root` of a sync committee of the preset's size: its keys' roots in a tree of the
preset's depth, beside the aggregate key's root. On the mainnet preset, `SyncCommittee.root`. -/
def committeeRoot (p : Preset) (sc : SyncCommittee) : ByteArray :=
  hash64 (subtree (sc.pubkeys.map SyncCommittee.pubkeyRoot) p.committeeDepth 0)
    (SyncCommittee.pubkeyRoot sc.aggregatePubkey)

/-- Whether a committee is `SyncCommittee.empty()`: every key zero. -/
def committeeEmpty (sc : SyncCommittee) : Bool := allZero sc.pubkeys && isZero sc.aggregatePubkey

/-- A committee the store holds: its root, its keys' 48-byte encodings and its aggregate key's,
as the state holds them. -/
structure Committee where
  root : ByteArray
  pubkeys : Array ByteArray
  aggregate : ByteArray

/-- A committee taken in: as many keys as the preset's committee; `none` otherwise. -/
def Committee.ofSync (p : Preset) (sc : SyncCommittee) : Option Committee :=
  if sc.pubkeys.size = p.committeeSize then
    some ⟨committeeRoot p sc, sc.pubkeys, sc.aggregatePubkey⟩
  else none

/-- Bit `i` of an SSZ `Bitvector`: bit `i % 8` of byte `i / 8`. -/
def bit (bits : ByteArray) (i : Nat) : Bool := (Bytes.byteAt bits (i / 8)).toNat.testBit (i % 8)

/-- How many of the first `n` bits are set: `get_set_bit_count`. -/
def popcount (n : Nat) (bits : ByteArray) : Nat := (List.range n).countP (bit bits)

/-- The keys whose bit is set, in order. -/
def participants {α : Type} (keys : Array α) (bits : ByteArray) : Array α :=
  ((List.range keys.size).filterMap fun i => if bit bits i then keys[i]? else none).toArray

/-- The keys whose bit is clear, in order. -/
def absent {α : Type} (keys : Array α) (bits : ByteArray) : List α :=
  (List.range keys.size).filterMap fun i => if bit bits i then none else keys[i]?

/-- The participants' keys decoded (`g1Decompress?`, no subgroup check) and summed, as
FastAggregateVerify aggregates them: `none` when one does not decode or the sum is the
identity. -/
def signersSum? (com : Committee) (bits : ByteArray) : Option Bls.G1A :=
  ((participants com.pubkeys bits).mapM Bls.g1Decompress?).bind Bls.aggregate?

/-- The key the participants signed under, as the store computes it: when more than half signed,
the committee's aggregate key less the absent keys, each decoded (Helios's
`get_participating_aggregate_pubkey`), so a few points are decoded rather than hundreds; else
`signersSum?`. The two agree on a committee whose aggregate key is its keys' sum
(`LeanLightProofs.Store.signersKey?_eq`). -/
def signersKey? (com : Committee) (bits : ByteArray) : Option Bls.G1A :=
  let out := absent com.pubkeys bits
  if 2 * out.length < com.pubkeys.size then
    match Bls.g1Decompress? com.aggregate, out.mapM Bls.g1Decompress? with
    | some a, some ks => (ks.foldl (fun acc k => acc.addA k.neg) (Bls.G1J.ofAffine a)).toAffine?
    | _, _ => none
  else signersSum? com bits

/-- Two thirds of the committee: `3·signers ≥ 2·SYNC_COMMITTEE_SIZE`. -/
def supermajority (p : Preset) (signers : Nat) : Bool := decide (2 * p.committeeSize ≤ 3 * signers)

/-- `UPDATE_TIMEOUT`: `SLOTS_PER_EPOCH * EPOCHS_PER_SYNC_COMMITTEE_PERIOD`. -/
def updateTimeout (p : Preset) : Nat := p.slotsPerEpoch * p.epochsPerPeriod

/-! ### Bootstraps and updates -/

/-- A `LightClientBootstrap`, normalized. -/
structure Bootstrap where
  header : Header
  committee : SyncCommittee
  branch : Array ByteArray

/-- A `LightClientUpdate`, normalized. A finality update has an empty next committee and an
all-zero branch; an optimistic update also an empty finalized header and finality branch. -/
structure Update where
  attested : Header
  next : SyncCommittee
  nextBranch : Array ByteArray
  finalized : Header
  finalityBranch : Array ByteArray
  aggregate : SyncAggregate
  signatureSlot : Nat

namespace Update

/-- `is_sync_committee_update`. -/
def isSyncCommitteeUpdate (u : Update) : Bool := !allZero u.nextBranch

/-- `is_finality_update`. -/
def isFinalityUpdate (u : Update) : Bool := !allZero u.finalityBranch

/-- How many members signed. -/
def signers (p : Preset) (u : Update) : Nat := popcount p.committeeSize u.aggregate.bits

/-- The attested slot. -/
def slot (u : Update) : Nat := u.attested.beacon.slot

/-- The root the finality branch proves: the finalized header's, or zero for the genesis
checkpoint. -/
def finalizedLeaf (u : Update) : ByteArray :=
  if u.finalized.beacon.slot = 0 then zeroChunk else u.finalized.root

end Update

/-! ## Validation before BLS -/

/-- Step 6 for the finalized header: with no finality branch, the finalized header is empty;
with one, at the genesis slot the header is empty and the branch proves the zero root, else the
header is valid at its own slot's fork and the branch proves its root, at the gindex of the
attested slot's fork, under the attested state root. -/
def finalityOk (c : Chain) (u : Update) : Bool :=
  if !u.isFinalityUpdate then u.finalized.isEmpty
  else
    (if u.finalized.beacon.slot = 0 then u.finalized.isEmpty else isValidHeader c u.finalized) &&
      isValidNormalizedBranch u.finalizedLeaf u.finalityBranch (finalizedGindex c u.slot)
        u.attested.beacon.stateRoot

/-- Step 7: with no next-committee branch, the committee is empty; with one, it has the preset's
number of keys (its SSZ type's, which the decoders already ensure) and the branch proves the
committee's root at the gindex of the attested slot's fork, under the attested state root. -/
def nextOk (c : Chain) (u : Update) : Bool :=
  if !u.isSyncCommitteeUpdate then committeeEmpty u.next
  else
    decide (u.next.pubkeys.size = c.preset.committeeSize) &&
    isValidNormalizedBranch (committeeRoot c.preset u.next) u.nextBranch (nextGindex c u.slot)
      u.attested.beacon.stateRoot

/-- The checks of `validate_light_client_update` that need neither the store nor BLS: two thirds
of the committee signed (step 2, this light client's threshold, which implies
`MIN_SYNC_COMMITTEE_PARTICIPANTS`); `signature_slot > attested slot ≥ finalized slot` (step 3,
without the clock); the attested header valid at its own slot's fork, and the finalized header
and the next committee proved under its state root (steps 6 and 7); `signature_slot` a
`uint64`, as the SSZ decoders give it, so every slot of the update is one. -/
def formOk (c : Chain) (u : Update) : Bool :=
  supermajority c.preset (u.signers c.preset) && decide (u.slot < u.signatureSlot) &&
    decide (u.finalized.beacon.slot ≤ u.slot) && isValidHeader c u.attested && finalityOk c u &&
    nextOk c u && decide (u.signatureSlot < 2 ^ 64)

/-- Step 9: the participants' aggregate key (`signersKey?`) under the committee, the fork version
at the epoch of `max(signature_slot, 1) − 1`, the domain `compute_domain(DOMAIN_SYNC_COMMITTEE,
version, genesis_validators_root)`, the signing root of the attested header's root, and
`FastAggregateVerify`'s check of that key (`Bls.verifyAggregate`). -/
def verifySignature (c : Chain) (com : Committee) (u : Update) : Bool :=
  match c.signatureVersion u.signatureSlot with
  | none => false
  | some v =>
    Bls.verifyAggregate (signersKey? com u.aggregate.bits)
      (signingRoot u.attested.root (computeDomain domainSyncCommittee v c.genesisValidatorsRoot))
      u.aggregate.signature

/-! ## The store -/

/-- What one side of a conflict holds: a header two thirds signed and a root its state proves,
a finalized checkpoint's (`finality`) or a next committee's. Enough to verify again: the
signature over `attested`, and the branch from `leaf` to its state root. -/
structure Witness where
  attested : BeaconBlockHeader
  aggregate : SyncAggregate
  signatureSlot : Nat
  finality : Bool
  leaf : ByteArray
  branch : Array ByteArray

/-- A finalized checkpoint seen in a verified update: its epoch (read from the finality branch),
root and slot, and the update's witness. -/
structure Checkpoint where
  epoch : Nat
  root : ByteArray
  slot : Nat
  witness : Witness

/-- A committee root seen for `period`: the bootstrap's (no witness) or a verified update's. -/
structure Held where
  period : Nat
  root : ByteArray
  witness : Option Witness

/-- The two kinds of conflict. -/
inductive ConflictKind where
  /-- Two finalized checkpoints of one epoch with different roots. -/
  | finality
  /-- Two committees for one period. -/
  | committee
  deriving DecidableEq

/-- A conflict: what the store held (`none`: the bootstrap's own committee) and the update that
disagrees with it. -/
structure Conflict where
  kind : ConflictKind
  held : Option Witness
  new : Witness

/-- The anchor: the newest attested header two thirds of the committee signed, how many signed,
and the signature slot. -/
structure Anchor where
  header : Header
  signers : Nat
  signatureSlot : Nat

/-- The light client's store. The specification's `LightClientStore` (`finalized`, `current`,
`next`, `best`, `optimistic`, `previousMaxActive`, `currentMaxActive`) and, beside it:
the anchor; the newest attested slot of a verified update (`newestSlot`), which moves `effNow`;
the finalized checkpoints and committee roots seen in verified updates (`checkpoints`, `roots`)
and past committees with their keys (`past`), for conflicts; the conflict that halted the store;
and whether a verified header at the anchor's slot named another root (the G9 warning). -/
structure Store where
  finalized : Header
  current : Committee
  next : Option Committee
  best : Option Update
  /-- `optimistic_header`. -/
  optimistic : Header
  /-- `previous_max_active_participants`. -/
  previousMaxActive : Nat
  /-- `current_max_active_participants`. -/
  currentMaxActive : Nat
  anchor : Option Anchor
  newestSlot : Option Nat
  checkpoints : List Checkpoint
  roots : List Held
  past : List (Nat × Committee)
  halted : Option Conflict
  forkWarning : Bool

/-- The store's period: its finalized header's. -/
def period (c : Chain) (s : Store) : Nat := c.periodAt s.finalized.beacon.slot

/-! ## The clock (G6) -/

/-- `effNow`: the clock, or the time of the newest attested slot two thirds verified, whichever
is later. Nothing unverified enters it. -/
def effNow (c : Chain) (s : Store) (now : Nat) : Nat :=
  match s.newestSlot with
  | some n => max now (c.slotTime n)
  | none => now

/-- The age bound: `effNow − slotTime(finalized slot) ≤ MAX_AGE`. -/
def fresh (c : Chain) (s : Store) (now : Nat) : Bool :=
  decide (effNow c s now - c.slotTime s.finalized.beacon.slot ≤ c.maxAge)

/-- "Clock behind": the clock's slot is before the newest verified attested slot. -/
def clockBehind (c : Chain) (s : Store) (now : Nat) : Bool :=
  match s.newestSlot with
  | some n => decide (c.slotOf now < n)
  | none => false

/-! ## Bootstrap -/

/-- `initialize_light_client_store`, with this light client's checks: the header is valid at its slot's fork,
its root is the configured checkpoint, the current committee is proved by its branch at the
fork's gindex under the header's state root, its slot is a `uint64`, the checkpoint is younger
than `MAX_AGE` at `now`,
and the committee has the preset's number of keys (kept as encodings, not validated). The store starts with that header finalized, that committee
current, its root kept for its period, and nothing else. -/
def bootstrap (c : Chain) (checkpoint : ByteArray) (now : Nat) (b : Bootstrap) : Option Store :=
  let slot := b.header.beacon.slot
  if isValidHeader c b.header && decide (b.header.root = checkpoint) &&
      decide (slot < 2 ^ 64) &&
      isValidNormalizedBranch (committeeRoot c.preset b.committee) b.branch (currentGindex c slot)
        b.header.beacon.stateRoot &&
      decide (now - c.slotTime slot ≤ c.maxAge) then
    (Committee.ofSync c.preset b.committee).map fun com =>
      { finalized := b.header, current := com, next := none, best := none,
        optimistic := b.header, previousMaxActive := 0, currentMaxActive := 0, anchor := none,
        newestSlot := none, checkpoints := [], roots := [⟨c.periodAt slot, com.root, none⟩],
        past := [], halted := none, forkWarning := false }
  else none

/-! ## `is_better_update` -/

/-- The key `is_better_update` compares, in its order, larger first: a supermajority (`1`) beats
none; below it, more participants (the count, `0` for a supermajority, where it does not
count yet); a relevant next committee (attested and signature in one period) beats none;
finality beats none; sync-committee finality (finalized and attested in one period) beats none;
then more participants; then the older attested slot (its negation); then the earlier
signature slot (its negation). -/
def rank (c : Chain) (u : Update) : List Int :=
  let p := c.preset
  let n := u.signers p
  let sm := supermajority p n
  let rel := u.isSyncCommitteeUpdate && c.periodAt u.slot == c.periodAt u.signatureSlot
  let fin := u.isFinalityUpdate
  let scf := fin && c.periodAt u.finalized.beacon.slot == c.periodAt u.slot
  [if sm then 1 else 0, if sm then 0 else n, if rel then 1 else 0, if fin then 1 else 0,
    if scf then 1 else 0, n, -u.slot, -u.signatureSlot]

/-- Lexicographic comparison, larger first: at the first key that differs. -/
def lexGtB : List Int → List Int → Bool
  | a :: as, b :: bs => if a = b then lexGtB as bs else decide (b < a)
  | _, _ => false

/-- `is_better_update(new, old)` (`altair/light-client/sync-protocol.md`), as spec/16 states it: a
lexicographic order on `rank`. `LeanLightProofs.Store` proves it a strict order; the tests compare it
with the specification's text (`LeanLightTests.Store`, on every pair of the `update_ranking` vectors'
updates) and run those vectors. -/
def isBetter (c : Chain) (new old : Update) : Bool := lexGtB (rank c new) (rank c old)

/-! ## Processing an update -/

/-- The committee the store holds for a signature period, and whether it is the current or next
one (an update signed under it may be accepted) rather than a past one (it is only compared). -/
def committeeFor (c : Chain) (s : Store) (sigPeriod : Nat) : Option (Committee × Bool) :=
  if sigPeriod = period c s then some (s.current, true)
  else if sigPeriod = period c s + 1 then s.next.map fun n => (n, true)
  else (s.past.find? (·.1 == sigPeriod)).map fun e => (e.2, false)

/-- The epoch of the finalized checkpoint an update's finality branch proves: the root's
sibling, `finality_branch[len − floorlog2(gindex)]`, read as a `uint64`. -/
def finalityEpoch (c : Chain) (u : Update) : Nat :=
  let i := u.finalityBranch.size - (finalizedGindex c u.slot).log2
  Ssz.u64 (u.finalityBranch[i]?.getD zeroChunk) 0

/-- The witness of an update's finalized checkpoint. -/
def Witness.ofFinality (u : Update) : Witness :=
  ⟨u.attested.beacon, u.aggregate, u.signatureSlot, true, u.finalizedLeaf, u.finalityBranch⟩

/-- The witness of an update's next committee. -/
def Witness.ofNext (c : Chain) (u : Update) : Witness :=
  ⟨u.attested.beacon, u.aggregate, u.signatureSlot, false, committeeRoot c.preset u.next,
    u.nextBranch⟩

/-- The period a committee an update brings is for: the one after its attested slot's. -/
def nextPeriod (c : Chain) (u : Update) : Nat := c.periodAt u.slot + 1

/-- The conflict a verified update makes with what the store keeps, if any: a finalized
checkpoint (not genesis) of an epoch the store holds with another root, or a next committee
for a period the store holds another root for. -/
def conflictOf (c : Chain) (s : Store) (u : Update) : Option Conflict :=
  let fin : Option Conflict :=
    if u.isFinalityUpdate && u.finalized.beacon.slot != 0 then
      let e := finalityEpoch c u
      match s.checkpoints.find? (·.epoch == e) with
      | some cp =>
        if cp.root = u.finalized.root then none
        else some ⟨.finality, some cp.witness, Witness.ofFinality u⟩
      | none => none
    else none
  let com : Option Conflict :=
    if u.isSyncCommitteeUpdate then
      match s.roots.find? (·.period == nextPeriod c u) with
      | some h =>
        if h.root = committeeRoot c.preset u.next then none
        else some ⟨.committee, h.witness, Witness.ofNext c u⟩
      | none => none
    else none
  match fin with
  | some k => some k
  | none => com

/-- What a verified update adds to what the store keeps: its finalized checkpoint, unless its
epoch is held; its next committee's root, unless its period is held. Checkpoints older than
`MAX_AGE` against `effNow` leave, and each list keeps its newest entries within its bound. -/
def retain (c : Chain) (s : Store) (now : Nat) (u : Update) : Store :=
  let e := finalityEpoch c u
  let cps :=
    if u.isFinalityUpdate && u.finalized.beacon.slot != 0 && !s.checkpoints.any (·.epoch == e) then
      ⟨e, u.finalized.root, u.finalized.beacon.slot, Witness.ofFinality u⟩ :: s.checkpoints
    else s.checkpoints
  let q := nextPeriod c u
  let roots :=
    if u.isSyncCommitteeUpdate && !s.roots.any (·.period == q) then
      ⟨q, committeeRoot c.preset u.next, some (Witness.ofNext c u)⟩ :: s.roots
    else s.roots
  let horizon := effNow c s now
  { s with
    checkpoints := (cps.filter fun cp => decide (horizon ≤ c.slotTime cp.slot + c.maxAge)).take
      maxCheckpoints
    roots := roots.take maxRoots }

/-- Step 5, relevance: the attested slot is past the store's finalized slot, or the update brings
the next committee the store lacks, for the store's period. -/
def relevant (c : Chain) (s : Store) (u : Update) : Bool :=
  decide (s.finalized.beacon.slot < u.slot) ||
    (s.next.isNone && u.isSyncCommitteeUpdate && c.periodAt u.slot == period c s)

/-- The anchor moves to a newer attested header; at the anchor's slot another root changes
nothing but raises the G9 warning. -/
def moveAnchor (c : Chain) (s : Store) (u : Update) : Store :=
  let new : Anchor := ⟨u.attested, u.signers c.preset, u.signatureSlot⟩
  match s.anchor with
  | none => { s with anchor := some new }
  | some a =>
    if a.header.beacon.slot < u.slot then { s with anchor := some new }
    else if a.header.beacon.slot = u.slot ∧ a.header.root ≠ u.attested.root then
      { s with forkWarning := true }
    else s

/-- What an update did. -/
inductive Verdict where
  /-- The store is halted: nothing is accepted. -/
  | halted
  /-- A check before BLS failed: participation, slots, headers or branches. -/
  | malformed
  /-- `signature_slot` is after the clock's slot (`current_slot >= signature_slot` fails). -/
  | future
  /-- The store holds no committee for the signature period (a skipped or unknown period). -/
  | unknownPeriod
  /-- The age bound failed: the store is too old. -/
  | tooOld
  /-- The signature does not verify. -/
  | badSignature
  /-- Verified, and conflicts with what the store keeps: the store is halted. -/
  | conflict
  /-- Verified under a past committee: compared, nothing else. -/
  | compared
  /-- Verified, and not relevant. -/
  | irrelevant
  /-- Verified, relevant, and brings for the store's period a next committee other than the one
  the store holds (`update.next_sync_committee == store.next_sync_committee` fails). -/
  | nextMismatch
  /-- The next committee it brings is refused by `Committee.ofSync`: not the preset's number of
  keys (which `nextOk` already refuses; no key is validated). -/
  | badKeys
  /-- Accepted: `applied` when the finalized header or the committees moved, `learned` when a
  committee entered the store. -/
  | accepted (applied learned : Bool)
  deriving DecidableEq

/-- The committee an update brings, when it becomes the store's next: none when empty, else
`Committee.ofSync` of it (`none` inside when that refuses it). -/
def learn (c : Chain) (u : Update) : Option (Option Committee) :=
  if committeeEmpty u.next then some none else (Committee.ofSync c.preset u.next).map some

/-- `apply_light_client_update`, then `best_valid_update = None` as both its callers do: with no
next committee, the update's becomes next (its finalized header in the store's period; the
specification's assertion, which fails only on an update `validate_light_client_update`
refuses); with one, when the finalized header enters the next period, next becomes current, the
old current goes to `past`, the update's becomes next and the participation counters move on;
the finalized header advances, and the optimistic header with it when it is older. -/
def apply (c : Chain) (s : Store) (u : Update) : Store × Verdict :=
  let sp := period c s
  let fp := c.periodAt u.finalized.beacon.slot
  let advance (s : Store) : Store :=
    if s.finalized.beacon.slot < u.finalized.beacon.slot then
      let o := if s.optimistic.beacon.slot < u.finalized.beacon.slot then u.finalized else s.optimistic
      { s with finalized := u.finalized, best := none, optimistic := o }
    else { s with best := none }
  match s.next with
  | none =>
    if fp = sp then
      match learn c u with
      | none => (s, .badKeys)
      | some nc => (advance { s with next := nc }, .accepted true nc.isSome)
    else (s, .irrelevant)
  | some n =>
    if fp = sp + 1 then
      match learn c u with
      | none => (s, .badKeys)
      | some nc =>
        let s' : Store :=
          { s with
            current := n, next := nc, past := ((sp, s.current) :: s.past).take maxPast
            previousMaxActive := s.currentMaxActive, currentMaxActive := 0 }
        (advance s', .accepted true nc.isSome)
    else (advance s, .accepted true false)

/-- `best` as `process_light_client_update` keeps it: the update when there is none or
`isBetter` prefers it. -/
def keepBest (c : Chain) (s : Store) (u : Update) : Store :=
  { s with best := if (s.best.map (isBetter c u)).getD true then some u else s.best }

/-- `get_safety_threshold`: half the larger of the two participation counters. -/
def safetyThreshold (s : Store) : Nat := max s.previousMaxActive s.currentMaxActive / 2

/-- What `process_light_client_update` does to every valid update before deciding whether to
apply it: `best` follows `isBetter`, the current participation counter takes the update's
count, and the optimistic header moves to the attested header when more than the safety
threshold signed and it is newer. -/
def track (c : Chain) (s : Store) (u : Update) : Store :=
  let n := u.signers c.preset
  let s := keepBest c s u
  let s := { s with currentMaxActive := max s.currentMaxActive n }
  if decide (safetyThreshold s < n) && decide (s.optimistic.beacon.slot < u.slot) then
    { s with optimistic := u.attested }
  else s

/-- Whether `process_light_client_update` applies an update, short of its two thirds: its
finalized header is newer than the store's, or it brings a finalized next committee the store
lacks. -/
def applies (c : Chain) (s : Store) (u : Update) : Bool :=
  decide (s.finalized.beacon.slot < u.finalized.beacon.slot) ||
    (s.next.isNone && u.isSyncCommitteeUpdate && u.isFinalityUpdate &&
      c.periodAt u.finalized.beacon.slot == c.periodAt u.slot)

/-- `process_light_client_update` after validation: `track`; the anchor moves; the update is
applied when two thirds signed (as every update reaching here did) and `applies`. -/
def process (c : Chain) (s : Store) (u : Update) : Store × Verdict :=
  let s := moveAnchor c (track c s u) u
  if supermajority c.preset (u.signers c.preset) && applies c s u then apply c s u
  else (s, .accepted false false)

/-- `validate_light_client_update`'s check of a next committee for the store's own period when
the store already knows its next committee: the update's must be the same committee. -/
def nextMatches (c : Chain) (s : Store) (u : Update) : Bool :=
  match s.next with
  | some n =>
    !(u.isSyncCommitteeUpdate && c.periodAt u.slot == period c s) ||
      (decide (u.next.pubkeys = n.pubkeys) && decide (u.next.aggregatePubkey = n.aggregate))
  | none => true

/-- What follows a verified signature: the attested slot counted in `newestSlot`; the comparison
with what the store keeps, a conflict halting the store; the update kept (`retain`); and, signed
by the current or next committee (`live`), the age bound again with its attested slot counted,
the relevance check, the next committee's check and `process`. -/
def afterBls (c : Chain) (s : Store) (now : Nat) (u : Update) (live : Bool) : Store × Verdict :=
  let s := { s with newestSlot := some (max u.slot (s.newestSlot.getD 0)) }
  match conflictOf c s u with
  | some k => ({ s with halted := some k }, .conflict)
  | none =>
    let s := retain c s now u
    if !live then (s, .compared)
    else if !fresh c s now then (s, .tooOld)
    else if !relevant c s u then (s, .irrelevant)
    else if !nextMatches c s u then (s, .nextMismatch)
    else process c s u

/-- One update, at clock `now` (ms): refused while halted; checked before BLS (`formOk`, the
clock's slot at or after `signature_slot`, a committee held for its signature period, the age
bound); its signature verified; then `afterBls`. -/
def receive (c : Chain) (s : Store) (now : Nat) (u : Update) : Store × Verdict :=
  if s.halted.isSome then (s, .halted)
  else if !formOk c u then (s, .malformed)
  else if c.slotOf now < u.signatureSlot then (s, .future)
  else
    match committeeFor c s (c.periodAt u.signatureSlot) with
    | none => (s, .unknownPeriod)
    | some (com, live) =>
      if !fresh c s now then (s, .tooOld)
      else if !verifySignature c com u then (s, .badSignature)
      else afterBls c s now u live

/-- `process_light_client_store_force_update`, which the specification lets a light client call
"based on use case dependent heuristics if light client sync appears stuck". leanLight's client
never calls it (no forced update: the finalized header moves only on two thirds' finality); it
is here so the specification's `sync` vectors run whole. After `UPDATE_TIMEOUT` slots past the
finalized header, the best update is applied, its attested header standing in for a finalized
header no newer than the store's; nothing changes when `apply` refuses it. -/
def forceUpdate (c : Chain) (s : Store) (now : Nat) : Store :=
  match s.best with
  | none => s
  | some b =>
    if s.halted.isNone && decide (s.finalized.beacon.slot + updateTimeout c.preset < c.slotOf now) then
      let b := if b.finalized.beacon.slot ≤ s.finalized.beacon.slot then { b with finalized := b.attested } else b
      match apply c s b with
      | (s', .accepted _ _) => { s' with best := none }
      | _ => s
    else s

/-- The anchor answered from: the store's, while it is not halted and within `MAX_AGE`. -/
def anchored (c : Chain) (s : Store) (now : Nat) : Option Anchor :=
  if s.halted.isNone && fresh c s now then s.anchor else none

/-! ## Historical updates -/

/-- Which EL block a header's hash names, by the header's own slot: its own payload's (`own`)
before `GLOAS_FORK_EPOCH`, its parent payload's (`parent`) from it on. -/
inductive ElTag where
  | own
  | parent
  deriving DecidableEq

/-- The tag of a header's EL hash, by its own slot. -/
def elTag (c : Chain) (h : Header) : ElTag := if c.gloasAt h.beacon.slot then .parent else .own

/-- A historical finality update (or update), verified without changing the store, under the
committee the store holds for its signature period, current, next or past (`committeeFor`):
`formOk` (two thirds signed, slots in order, headers valid at their slots' forks, branches), a
finality branch to a header other than genesis, and the signature. When it verifies: the
finalized header, its EL hash and that hash's tag. No age bound and no conflict check: the
caller (LC6's re-check of a stored snapshot) judges age itself. -/
def verifyHistorical (c : Chain) (s : Store) (u : Update) : Option (Header × ByteArray × ElTag) :=
  if formOk c u && u.isFinalityUpdate && u.finalized.beacon.slot != 0 then
    match committeeFor c s (c.periodAt u.signatureSlot) with
    | some (com, _) =>
      if verifySignature c com u then some (u.finalized, u.finalized.elHash, elTag c u.finalized)
      else none
    | none => none
  else none

/-! ## Conflicts, verified again -/

/-- A witness verified under a committee: two thirds signed, `signature_slot` after the attested
slot, the branch proves the leaf at the gindex of the attested slot's fork (a finalized root's or
a next committee's) under the attested state root, and the signature verifies. -/
def Witness.verify (c : Chain) (com : Committee) (w : Witness) : Bool :=
  supermajority c.preset (popcount c.preset.committeeSize w.aggregate.bits) &&
    decide (w.attested.slot < w.signatureSlot) &&
    isValidNormalizedBranch w.leaf w.branch
      (if w.finality then finalizedGindex c w.attested.slot else nextGindex c w.attested.slot)
      w.attested.stateRoot &&
    match c.signatureVersion w.signatureSlot with
    | none => false
    | some v =>
      Bls.verifyAggregate (signersKey? com w.aggregate.bits)
        (signingRoot w.attested.root (computeDomain domainSyncCommittee v c.genesisValidatorsRoot))
        w.aggregate.signature

/-- A witness verified under the committee the store holds for its signature period. -/
def Witness.verifiedBy (c : Chain) (s : Store) (w : Witness) : Bool :=
  match committeeFor c s (c.periodAt w.signatureSlot) with
  | some (com, _) => w.verify c com
  | none => false

/-- The checkpoint epoch a finality witness proves. -/
def Witness.epoch (c : Chain) (w : Witness) : Nat :=
  let i := w.branch.size - (finalizedGindex c w.attested.slot).log2
  Ssz.u64 (w.branch[i]?.getD zeroChunk) 0

/-- Whether a stored conflict still stands against a store: both sides verify under the
committees the store holds (the held side of a committee conflict may be the bootstrap's own
committee, whose root the store keeps), and they disagree in their kind (a finality conflict:
one epoch, two roots; a committee conflict: one period, two roots). -/
def Conflict.stands (c : Chain) (s : Store) (k : Conflict) : Bool :=
  k.new.verifiedBy c s && (k.new.finality == (k.kind == .finality)) &&
    match k.held with
    | some h =>
      h.verifiedBy c s && h.finality == k.new.finality && !(h.leaf = k.new.leaf) &&
        (if k.kind == .finality then h.epoch c == k.new.epoch c
         else c.periodAt h.attested.slot == c.periodAt k.new.attested.slot)
    | none =>
      k.kind == .committee &&
        s.roots.any fun r => r.witness.isNone && r.period == c.periodAt k.new.attested.slot + 1 &&
          !(r.root = k.new.leaf)

end LeanLight.Lc.Store
