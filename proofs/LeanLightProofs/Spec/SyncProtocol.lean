import LeanLight.Ssz.Containers
import LeanLight.Forks
import LeanLight.Bls.Fav

/-!
# The light client's sync protocol, as consensus-specs writes it

A transcription of consensus-specs v1.7.0-beta.5 (`204fb4a1`, unchanged in these files since
v1.7.0-beta.4), function by function and in the specification's order of checks:
`specs/altair/light-client/sync-protocol.md` as `capella`, `deneb`, `electra` and `gloas`
`light-client/sync-protocol.md` modify it, with `compute_fork_version` as `gloas/p2p-interface.md`
states it. Nothing here comes from leanLight's store (`LeanLight.Store`); the store is proved to
refine this (`LeanLightProofs.SyncProtocol`).

**Mutation.** The Python mutates `store`; here each function returns the new store. An `assert`
is `require`, a step of the `Option` monad: `none` is the exception the specification raises, and
a caller that sees it keeps its store, as a client that rejects an update does. (An `assert` in
`apply_light_client_update` cannot fail on an update `validate_light_client_update` accepted;
`process_sim` relies on that.)

**Representation.** An SSZ value is held as leanLight's containers hold it (`LeanLight.Ssz`):
`Bytes32`, `BLSPubkey` and friends as `ByteArray`, `uint64` as `Nat`, a `Vector` as `Array`, a
`Bitvector` as its bytes. Equality with a type's default value (`LightClientHeader.empty()`,
`SyncCommittee.empty()`, `FinalityBranch()`) is "every byte zero", which on a value of the type,
whose sizes are fixed, is that equality. `LightClientHeader` is the one sum of its two forms that
consensus-specs has today: Capella's container with Deneb's `ExecutionPayloadHeader`, which
Deneb, Electra and Fulu use (`electra`), and Gloas's (`gloas`). Each form is checked by its own
fork's `is_valid_light_client_header`; a store holds one fork's form, the other's being what
`upgrade_lc_header_to_gloas` changes, and no function below reads a header past its `beacon`
except `is_valid_light_client_header`.

**Primitives.** The SSZ, hashing and BLS functions the protocol calls are leanLight's, each
proved against its own specification elsewhere, so that this file is the protocol alone:

* `hash`: SHA-256 (`LeanLight.Ssz.hash64 a b` is `hash(a + b)`; `LeanLightProofs.Sha256`
  proves it FIPS 180-4's);
* `hash_tree_root` of `BeaconBlockHeader` and of the execution payload headers
  (`LeanLightProofs.SszRoot` proves them ssz-specs'); of `SyncCommittee` written here over
  `SYNC_COMMITTEE_SIZE`;
* `compute_domain` and `compute_signing_root` (`LeanLight.Forks`, phase0's);
* `bls.FastAggregateVerify`: `LeanLight.Bls.fastAggregateVerifyBytes`, KeyValidate on every key
  then the aggregate check, which `LeanLightProofs.Bls.FavEth` proves EthLib's.

`is_valid_merkle_branch` and `is_valid_normalized_merkle_branch` are transcribed here (phase0 and
Altair), an index past a branch's end (Python's `IndexError`) refusing.

`process_light_client_finality_update` and `process_light_client_optimistic_update` build the
missing fields from the defaults of the attested header's fork (`defaultsOf`). The tests run this
file on consensus-specs' `sync` and `update_ranking` vectors (`leanlight-store-test`).
-/

namespace LeanLight.Spec.LightClient

open LeanLight.Lc
open LeanLight.Lc.Ssz (BeaconBlockHeader SyncCommittee SyncAggregate ExecutionPayloadHeader
  hash64 subtree bytesRoot u64Root u256Root mixInLength zeroChunk)

/-! ## Configuration -/

/-- The preset and configuration values the protocol reads: `SLOTS_PER_EPOCH`,
`EPOCHS_PER_SYNC_COMMITTEE_PERIOD`, `SYNC_COMMITTEE_SIZE`, `MIN_SYNC_COMMITTEE_PARTICIPANTS`, and
every fork's version and epoch (`FAR_FUTURE_EPOCH` for a fork not scheduled). -/
structure Config where
  SLOTS_PER_EPOCH : Nat
  EPOCHS_PER_SYNC_COMMITTEE_PERIOD : Nat
  SYNC_COMMITTEE_SIZE : Nat
  MIN_SYNC_COMMITTEE_PARTICIPANTS : Nat
  GENESIS_FORK_VERSION : ByteArray
  ALTAIR_FORK_VERSION : ByteArray
  ALTAIR_FORK_EPOCH : Nat
  BELLATRIX_FORK_VERSION : ByteArray
  BELLATRIX_FORK_EPOCH : Nat
  CAPELLA_FORK_VERSION : ByteArray
  CAPELLA_FORK_EPOCH : Nat
  DENEB_FORK_VERSION : ByteArray
  DENEB_FORK_EPOCH : Nat
  ELECTRA_FORK_VERSION : ByteArray
  ELECTRA_FORK_EPOCH : Nat
  FULU_FORK_VERSION : ByteArray
  FULU_FORK_EPOCH : Nat
  GLOAS_FORK_VERSION : ByteArray
  GLOAS_FORK_EPOCH : Nat

/-- `FAR_FUTURE_EPOCH`. -/
def FAR_FUTURE_EPOCH : Nat := 2 ^ 64 - 1

/-- `GENESIS_SLOT`. -/
def GENESIS_SLOT : Nat := 0

/-- `DOMAIN_SYNC_COMMITTEE`. -/
def DOMAIN_SYNC_COMMITTEE : ByteArray := ⟨#[0x07, 0, 0, 0]⟩

/-- The mainnet preset and the mainnet configuration (eth-clients/mainnet `config.yaml`): no
Gloas epoch is scheduled, Gloas's version the preset's default. -/
def mainnet : Config :=
  { SLOTS_PER_EPOCH := 32, EPOCHS_PER_SYNC_COMMITTEE_PERIOD := 256, SYNC_COMMITTEE_SIZE := 512,
    MIN_SYNC_COMMITTEE_PARTICIPANTS := 1,
    GENESIS_FORK_VERSION := ⟨#[0x00, 0, 0, 0]⟩,
    ALTAIR_FORK_VERSION := ⟨#[0x01, 0, 0, 0]⟩, ALTAIR_FORK_EPOCH := 74240,
    BELLATRIX_FORK_VERSION := ⟨#[0x02, 0, 0, 0]⟩, BELLATRIX_FORK_EPOCH := 144896,
    CAPELLA_FORK_VERSION := ⟨#[0x03, 0, 0, 0]⟩, CAPELLA_FORK_EPOCH := 194048,
    DENEB_FORK_VERSION := ⟨#[0x04, 0, 0, 0]⟩, DENEB_FORK_EPOCH := 269568,
    ELECTRA_FORK_VERSION := ⟨#[0x05, 0, 0, 0]⟩, ELECTRA_FORK_EPOCH := 364032,
    FULU_FORK_VERSION := ⟨#[0x06, 0, 0, 0]⟩, FULU_FORK_EPOCH := 411392,
    GLOAS_FORK_VERSION := ⟨#[0x07, 0, 0, 0]⟩, GLOAS_FORK_EPOCH := FAR_FUTURE_EPOCH }

/-- The mainnet preset and Sepolia's configuration (eth-clients/sepolia `config.yaml`). -/
def sepolia : Config :=
  { SLOTS_PER_EPOCH := 32, EPOCHS_PER_SYNC_COMMITTEE_PERIOD := 256, SYNC_COMMITTEE_SIZE := 512,
    MIN_SYNC_COMMITTEE_PARTICIPANTS := 1,
    GENESIS_FORK_VERSION := ⟨#[0x90, 0, 0, 0x69]⟩,
    ALTAIR_FORK_VERSION := ⟨#[0x90, 0, 0, 0x70]⟩, ALTAIR_FORK_EPOCH := 50,
    BELLATRIX_FORK_VERSION := ⟨#[0x90, 0, 0, 0x71]⟩, BELLATRIX_FORK_EPOCH := 100,
    CAPELLA_FORK_VERSION := ⟨#[0x90, 0, 0, 0x72]⟩, CAPELLA_FORK_EPOCH := 56832,
    DENEB_FORK_VERSION := ⟨#[0x90, 0, 0, 0x73]⟩, DENEB_FORK_EPOCH := 132608,
    ELECTRA_FORK_VERSION := ⟨#[0x90, 0, 0, 0x74]⟩, ELECTRA_FORK_EPOCH := 222464,
    FULU_FORK_VERSION := ⟨#[0x90, 0, 0, 0x75]⟩, FULU_FORK_EPOCH := 272640,
    GLOAS_FORK_VERSION := ⟨#[0x90, 0, 0, 0x76]⟩, GLOAS_FORK_EPOCH := 353024 }

variable (cfg : Config)

/-- `UPDATE_TIMEOUT`: `SLOTS_PER_EPOCH * EPOCHS_PER_SYNC_COMMITTEE_PERIOD`. -/
def UPDATE_TIMEOUT : Nat := cfg.SLOTS_PER_EPOCH * cfg.EPOCHS_PER_SYNC_COMMITTEE_PERIOD

/-! ## Constants -/

/-- `FINALIZED_ROOT_GINDEX` (Altair, frozen). -/
def FINALIZED_ROOT_GINDEX : Nat := 105
/-- `CURRENT_SYNC_COMMITTEE_GINDEX` (Altair, frozen). -/
def CURRENT_SYNC_COMMITTEE_GINDEX : Nat := 54
/-- `NEXT_SYNC_COMMITTEE_GINDEX` (Altair, frozen). -/
def NEXT_SYNC_COMMITTEE_GINDEX : Nat := 55
/-- `FINALIZED_ROOT_GINDEX_ELECTRA`. -/
def FINALIZED_ROOT_GINDEX_ELECTRA : Nat := 169
/-- `CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA`. -/
def CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA : Nat := 86
/-- `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA`. -/
def NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA : Nat := 87
/-- `FINALIZED_ROOT_GINDEX_GLOAS`. -/
def FINALIZED_ROOT_GINDEX_GLOAS : Nat := 735
/-- `CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS`. -/
def CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS : Nat := 2945
/-- `NEXT_SYNC_COMMITTEE_GINDEX_GLOAS`. -/
def NEXT_SYNC_COMMITTEE_GINDEX_GLOAS : Nat := 2946
/-- `EXECUTION_PAYLOAD_GINDEX` (Capella). -/
def EXECUTION_PAYLOAD_GINDEX : Nat := 25
/-- `EXECUTION_BLOCK_HASH_GINDEX` (Gloas: Capella's body). -/
def EXECUTION_BLOCK_HASH_GINDEX : Nat := 412
/-- `EXECUTION_BLOCK_HASH_GINDEX_DENEB` (Gloas: Deneb's body). -/
def EXECUTION_BLOCK_HASH_GINDEX_DENEB : Nat := 812
/-- `EXECUTION_BLOCK_HASH_GINDEX_GLOAS`. -/
def EXECUTION_BLOCK_HASH_GINDEX_GLOAS : Nat := 2856

/-! ## Helpers from phase0 -/

/-- `floorlog2`. -/
def floorlog2 (x : Nat) : Nat := Nat.log2 x

/-- `compute_epoch_at_slot`. -/
def compute_epoch_at_slot (slot : Nat) : Nat := slot / cfg.SLOTS_PER_EPOCH

/-- `compute_sync_committee_period`. -/
def compute_sync_committee_period (epoch : Nat) : Nat := epoch / cfg.EPOCHS_PER_SYNC_COMMITTEE_PERIOD

/-- `compute_sync_committee_period_at_slot`. -/
def compute_sync_committee_period_at_slot (slot : Nat) : Nat :=
  compute_sync_committee_period cfg (compute_epoch_at_slot cfg slot)

/-- `compute_fork_version` (Gloas, `gloas/p2p-interface.md`). -/
def compute_fork_version (epoch : Nat) : ByteArray :=
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then cfg.GLOAS_FORK_VERSION
  else if epoch ≥ cfg.FULU_FORK_EPOCH then cfg.FULU_FORK_VERSION
  else if epoch ≥ cfg.ELECTRA_FORK_EPOCH then cfg.ELECTRA_FORK_VERSION
  else if epoch ≥ cfg.DENEB_FORK_EPOCH then cfg.DENEB_FORK_VERSION
  else if epoch ≥ cfg.CAPELLA_FORK_EPOCH then cfg.CAPELLA_FORK_VERSION
  else if epoch ≥ cfg.BELLATRIX_FORK_EPOCH then cfg.BELLATRIX_FORK_VERSION
  else if epoch ≥ cfg.ALTAIR_FORK_EPOCH then cfg.ALTAIR_FORK_VERSION
  else cfg.GENESIS_FORK_VERSION

/-- `saturating_sub`. -/
def saturating_sub (a b : Nat) : Nat := a - b

/-- `is_valid_merkle_branch` (phase0): `hash(branch[i] + value)` when bit `i` of `index` is set,
else `hash(value + branch[i])`, for `i` below `depth`; an index past the branch refuses. -/
def is_valid_merkle_branch (leaf : ByteArray) (branch : Array ByteArray) (depth index : Nat)
    (root : ByteArray) : Bool :=
  match (List.range depth).foldlM (fun value i => do
      let b ← branch[i]?
      pure (if index / 2 ^ i % 2 == 1 then hash64 b value else hash64 value b)) leaf with
  | some value => decide (value = root)
  | none => false

/-- `get_subtree_index`. -/
def get_subtree_index (generalized_index : Nat) : Nat :=
  generalized_index % 2 ^ floorlog2 generalized_index

/-- Whether every byte is zero: equality with the type's default (`Bytes32()`, `BLSPubkey()`). -/
def isZero (b : ByteArray) : Bool := b.data.all (· == 0)

/-- `is_valid_normalized_merkle_branch`: the leading `len(branch) - depth` roots zero, then
`is_valid_merkle_branch` on the rest. -/
def is_valid_normalized_merkle_branch (leaf : ByteArray) (branch : Array ByteArray)
    (gindex : Nat) (root : ByteArray) : Bool :=
  let depth := floorlog2 gindex
  let index := get_subtree_index gindex
  let num_extra := branch.size - depth
  ((List.range num_extra).all fun i => isZero (branch[i]?.getD ⟨#[]⟩)) &&
    is_valid_merkle_branch leaf (branch.extract num_extra branch.size) depth index root

/-! ## Containers -/

/-- `hash_tree_root` of a `SyncCommittee`: its keys (`Vector[BLSPubkey, SYNC_COMMITTEE_SIZE]`)
merkleized beside its aggregate key. -/
def hash_tree_root_sync_committee (sc : SyncCommittee) : ByteArray :=
  hash64 (subtree (sc.pubkeys.map SyncCommittee.pubkeyRoot) (floorlog2 cfg.SYNC_COMMITTEE_SIZE) 0)
    (SyncCommittee.pubkeyRoot sc.aggregatePubkey)

/-- `SyncCommittee.empty()`: every key and the aggregate key zero. -/
def SyncCommittee.isEmpty (sc : SyncCommittee) : Bool :=
  sc.pubkeys.all isZero && isZero sc.aggregatePubkey

/-- `SyncCommittee.empty()`, a value. -/
def SyncCommittee.empty : SyncCommittee :=
  ⟨Array.replicate cfg.SYNC_COMMITTEE_SIZE zeroChunk, ⟨Array.replicate 48 0⟩⟩

/-- `SyncCommittee` equality. -/
def SyncCommittee.eq (a b : SyncCommittee) : Bool :=
  decide (a.pubkeys = b.pubkeys) && decide (a.aggregatePubkey = b.aggregatePubkey)

/-- `hash_tree_root` of Capella's `ExecutionPayloadHeader` built from Deneb's fields
(`deneb/light-client/sync-protocol.md`, `get_lc_execution_root`): fifteen fields, depth 4. -/
def hash_tree_root_capella_payload (e : ExecutionPayloadHeader) : ByteArray :=
  subtree #[e.parentHash, bytesRoot e.feeRecipient 0, e.stateRoot, e.receiptsRoot,
    bytesRoot e.logsBloom 3, e.prevRandao, u64Root e.blockNumber, u64Root e.gasLimit,
    u64Root e.gasUsed, u64Root e.timestamp,
    mixInLength (bytesRoot e.extraData 0) e.extraData.size, u256Root e.baseFeePerGas,
    e.blockHash, e.transactionsRoot, e.withdrawalsRoot] 4 0

/-- `ExecutionPayloadHeader.empty()`. -/
def payloadIsEmpty (e : ExecutionPayloadHeader) : Bool :=
  isZero e.parentHash && isZero e.feeRecipient && isZero e.stateRoot && isZero e.receiptsRoot &&
    isZero e.logsBloom && isZero e.prevRandao && e.blockNumber == 0 && e.gasLimit == 0 &&
    e.gasUsed == 0 && e.timestamp == 0 && e.extraData.size == 0 && e.baseFeePerGas == 0 &&
    isZero e.blockHash && isZero e.transactionsRoot && isZero e.withdrawalsRoot &&
    e.blobGasUsed == 0 && e.excessBlobGas == 0

/-- A `LightClientHeader`, in the form of the fork whose container carries it. -/
inductive LightClientHeader where
  /-- Capella's container with Deneb's payload header, as Deneb, Electra and Fulu use it. -/
  | electra (beacon : BeaconBlockHeader) (execution : ExecutionPayloadHeader)
      (execution_branch : Array ByteArray)
  /-- Gloas's container. -/
  | gloas (beacon : BeaconBlockHeader) (execution_block_hash : ByteArray)
      (execution_branch : Array ByteArray)

namespace LightClientHeader

/-- `header.beacon`. -/
def beacon : LightClientHeader → BeaconBlockHeader
  | .electra b _ _ => b
  | .gloas b _ _ => b

/-- `header == LightClientHeader.empty()`. -/
def isEmpty : LightClientHeader → Bool
  | .electra b e br =>
    b.slot == 0 && b.proposerIndex == 0 && isZero b.parentRoot && isZero b.stateRoot &&
      isZero b.bodyRoot && payloadIsEmpty e && br.all isZero
  | .gloas b h br =>
    b.slot == 0 && b.proposerIndex == 0 && isZero b.parentRoot && isZero b.stateRoot &&
      isZero b.bodyRoot && isZero h && br.all isZero

end LightClientHeader

/-- `LightClientBootstrap`. -/
structure LightClientBootstrap where
  header : LightClientHeader
  current_sync_committee : SyncCommittee
  current_sync_committee_branch : Array ByteArray

/-- `LightClientUpdate`. -/
structure LightClientUpdate where
  attested_header : LightClientHeader
  next_sync_committee : SyncCommittee
  next_sync_committee_branch : Array ByteArray
  finalized_header : LightClientHeader
  finality_branch : Array ByteArray
  sync_aggregate : SyncAggregate
  signature_slot : Nat

/-- `LightClientFinalityUpdate`. -/
structure LightClientFinalityUpdate where
  attested_header : LightClientHeader
  finalized_header : LightClientHeader
  finality_branch : Array ByteArray
  sync_aggregate : SyncAggregate
  signature_slot : Nat

/-- `LightClientOptimisticUpdate`. -/
structure LightClientOptimisticUpdate where
  attested_header : LightClientHeader
  sync_aggregate : SyncAggregate
  signature_slot : Nat

/-- `LightClientStore`. -/
structure LightClientStore where
  finalized_header : LightClientHeader
  current_sync_committee : SyncCommittee
  next_sync_committee : SyncCommittee
  best_valid_update : Option LightClientUpdate
  optimistic_header : LightClientHeader
  previous_max_active_participants : Nat
  current_max_active_participants : Nat

/-! ## Helpers -/

/-- `finalized_root_gindex_at_slot` (Gloas). -/
def finalized_root_gindex_at_slot (slot : Nat) : Nat :=
  let epoch := compute_epoch_at_slot cfg slot
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then FINALIZED_ROOT_GINDEX_GLOAS
  else if epoch ≥ cfg.ELECTRA_FORK_EPOCH then FINALIZED_ROOT_GINDEX_ELECTRA
  else FINALIZED_ROOT_GINDEX

/-- `current_sync_committee_gindex_at_slot` (Gloas). -/
def current_sync_committee_gindex_at_slot (slot : Nat) : Nat :=
  let epoch := compute_epoch_at_slot cfg slot
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS
  else if epoch ≥ cfg.ELECTRA_FORK_EPOCH then CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA
  else CURRENT_SYNC_COMMITTEE_GINDEX

/-- `next_sync_committee_gindex_at_slot` (Gloas). -/
def next_sync_committee_gindex_at_slot (slot : Nat) : Nat :=
  let epoch := compute_epoch_at_slot cfg slot
  if epoch ≥ cfg.GLOAS_FORK_EPOCH then NEXT_SYNC_COMMITTEE_GINDEX_GLOAS
  else if epoch ≥ cfg.ELECTRA_FORK_EPOCH then NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA
  else NEXT_SYNC_COMMITTEE_GINDEX

/-- `get_lc_execution_root` (Deneb), for the Deneb-to-Fulu container. -/
def get_lc_execution_root_electra (beacon : BeaconBlockHeader) (execution : ExecutionPayloadHeader) :
    ByteArray :=
  let epoch := compute_epoch_at_slot cfg beacon.slot
  if epoch ≥ cfg.DENEB_FORK_EPOCH then execution.root
  else if epoch ≥ cfg.CAPELLA_FORK_EPOCH then hash_tree_root_capella_payload execution
  else zeroChunk

/-- `is_valid_light_client_header`: Deneb's (which Electra and Fulu keep) for the Deneb-to-Fulu
container, Gloas's for Gloas's. -/
def is_valid_light_client_header : LightClientHeader → Bool
  | .electra beacon execution execution_branch =>
    let epoch := compute_epoch_at_slot cfg beacon.slot
    if epoch < cfg.DENEB_FORK_EPOCH && (execution.blobGasUsed != 0 || execution.excessBlobGas != 0)
    then false
    else if epoch < cfg.CAPELLA_FORK_EPOCH then
      payloadIsEmpty execution && execution_branch.all isZero
    else
      is_valid_merkle_branch (get_lc_execution_root_electra cfg beacon execution) execution_branch
        (floorlog2 EXECUTION_PAYLOAD_GINDEX) (get_subtree_index EXECUTION_PAYLOAD_GINDEX)
        beacon.bodyRoot
  | .gloas beacon execution_block_hash execution_branch =>
    let epoch := compute_epoch_at_slot cfg beacon.slot
    if epoch ≥ cfg.GLOAS_FORK_EPOCH then
      is_valid_normalized_merkle_branch execution_block_hash execution_branch
        EXECUTION_BLOCK_HASH_GINDEX_GLOAS beacon.bodyRoot
    else if epoch ≥ cfg.DENEB_FORK_EPOCH then
      is_valid_normalized_merkle_branch execution_block_hash execution_branch
        EXECUTION_BLOCK_HASH_GINDEX_DENEB beacon.bodyRoot
    else if epoch ≥ cfg.CAPELLA_FORK_EPOCH then
      is_valid_normalized_merkle_branch execution_block_hash execution_branch
        EXECUTION_BLOCK_HASH_GINDEX beacon.bodyRoot
    else isZero execution_block_hash && execution_branch.all isZero

/-- `is_sync_committee_update`. -/
def is_sync_committee_update (update : LightClientUpdate) : Bool :=
  !(update.next_sync_committee_branch.all isZero)

/-- `is_finality_update`. -/
def is_finality_update (update : LightClientUpdate) : Bool :=
  !(update.finality_branch.all isZero)

/-- Bit `i` of a `Bitvector`, held as its bytes: bit `i % 8` of byte `i / 8`. -/
def bitAt (bits : ByteArray) (i : Nat) : Bool := ((bits[i / 8]?.getD 0).toNat.testBit (i % 8))

/-- `get_set_bit_count` of a `Bitvector[SYNC_COMMITTEE_SIZE]`. -/
def get_set_bit_count (bits : ByteArray) : Nat :=
  (List.range cfg.SYNC_COMMITTEE_SIZE).countP (bitAt bits)

/-- `is_better_update`. -/
def is_better_update (new_update old_update : LightClientUpdate) : Bool :=
  -- Compare supermajority (> 2/3) sync committee participation
  let max_active_participants := cfg.SYNC_COMMITTEE_SIZE
  let new_num_active_participants := get_set_bit_count cfg new_update.sync_aggregate.bits
  let old_num_active_participants := get_set_bit_count cfg old_update.sync_aggregate.bits
  let new_has_supermajority : Bool := new_num_active_participants * 3 ≥ max_active_participants * 2
  let old_has_supermajority : Bool := old_num_active_participants * 3 ≥ max_active_participants * 2
  if new_has_supermajority ≠ old_has_supermajority then new_has_supermajority
  else if !new_has_supermajority ∧ new_num_active_participants ≠ old_num_active_participants then
    new_num_active_participants > old_num_active_participants
  else
  -- Compare presence of relevant sync committee
  let new_has_relevant_sync_committee : Bool := is_sync_committee_update new_update ∧
    compute_sync_committee_period_at_slot cfg new_update.attested_header.beacon.slot =
      compute_sync_committee_period_at_slot cfg new_update.signature_slot
  let old_has_relevant_sync_committee : Bool := is_sync_committee_update old_update ∧
    compute_sync_committee_period_at_slot cfg old_update.attested_header.beacon.slot =
      compute_sync_committee_period_at_slot cfg old_update.signature_slot
  if new_has_relevant_sync_committee ≠ old_has_relevant_sync_committee then
    new_has_relevant_sync_committee
  else
  -- Compare indication of any finality
  let new_has_finality := is_finality_update new_update
  let old_has_finality := is_finality_update old_update
  if new_has_finality ≠ old_has_finality then new_has_finality
  else
  -- Compare sync committee finality
  let new_has_sync_committee_finality : Bool :=
    compute_sync_committee_period_at_slot cfg new_update.finalized_header.beacon.slot =
      compute_sync_committee_period_at_slot cfg new_update.attested_header.beacon.slot
  let old_has_sync_committee_finality : Bool :=
    compute_sync_committee_period_at_slot cfg old_update.finalized_header.beacon.slot =
      compute_sync_committee_period_at_slot cfg old_update.attested_header.beacon.slot
  if new_has_finality ∧ new_has_sync_committee_finality ≠ old_has_sync_committee_finality then
    new_has_sync_committee_finality
  -- Tiebreaker 1: Sync committee participation beyond supermajority
  else if new_num_active_participants ≠ old_num_active_participants then
    new_num_active_participants > old_num_active_participants
  -- Tiebreaker 2: Prefer older data (fewer changes to best)
  else if new_update.attested_header.beacon.slot ≠ old_update.attested_header.beacon.slot then
    new_update.attested_header.beacon.slot < old_update.attested_header.beacon.slot
  -- Tiebreaker 3: Prefer updates with earlier signature slots
  else new_update.signature_slot < old_update.signature_slot

/-- `is_next_sync_committee_known`. -/
def is_next_sync_committee_known (store : LightClientStore) : Bool :=
  !SyncCommittee.isEmpty store.next_sync_committee

/-- `get_safety_threshold`. -/
def get_safety_threshold (store : LightClientStore) : Nat :=
  max store.previous_max_active_participants store.current_max_active_participants / 2

/-! ## Initialization and updates -/

/-- `assert`: the exception when false. -/
def require (b : Bool) : Option Unit := if b then some () else none

/-- `initialize_light_client_store`. -/
def initialize_light_client_store (trusted_block_root : ByteArray)
    (bootstrap : LightClientBootstrap) : Option LightClientStore := do
  require (is_valid_light_client_header cfg bootstrap.header)
  require (bootstrap.header.beacon.root = trusted_block_root)
  require (is_valid_normalized_merkle_branch
    (hash_tree_root_sync_committee cfg bootstrap.current_sync_committee)
    bootstrap.current_sync_committee_branch
    (current_sync_committee_gindex_at_slot cfg bootstrap.header.beacon.slot)
    bootstrap.header.beacon.stateRoot)
  pure { finalized_header := bootstrap.header,
         current_sync_committee := bootstrap.current_sync_committee,
         next_sync_committee := SyncCommittee.empty cfg,
         best_valid_update := none,
         optimistic_header := bootstrap.header,
         previous_max_active_participants := 0,
         current_max_active_participants := 0 }

/-- The keys of `pubkeys` whose bit is set: `[pubkey for (bit, pubkey) in zip(bits, pubkeys,
strict=True) if bit]`, `strict` refusing a committee of another length. -/
def participant_pubkeys (bits : ByteArray) (pubkeys : Array ByteArray) : Option (Array ByteArray) :=
  if pubkeys.size = cfg.SYNC_COMMITTEE_SIZE then
    some ((List.range pubkeys.size).filterMap fun i =>
      if bitAt bits i then pubkeys[i]? else none).toArray
  else none

/-- `validate_light_client_update`. -/
def validate_light_client_update (store : LightClientStore) (update : LightClientUpdate)
    (current_slot : Nat) (genesis_validators_root : ByteArray) : Option Unit := do
  -- Verify sync committee has sufficient participants
  let sync_aggregate := update.sync_aggregate
  require (get_set_bit_count cfg sync_aggregate.bits ≥ cfg.MIN_SYNC_COMMITTEE_PARTICIPANTS)
  -- Verify update does not skip a sync committee period
  require (is_valid_light_client_header cfg update.attested_header)
  let update_attested_slot := update.attested_header.beacon.slot
  let update_finalized_slot := update.finalized_header.beacon.slot
  require (current_slot ≥ update.signature_slot ∧ update.signature_slot > update_attested_slot ∧
    update_attested_slot ≥ update_finalized_slot)
  let store_period := compute_sync_committee_period_at_slot cfg store.finalized_header.beacon.slot
  let update_signature_period := compute_sync_committee_period_at_slot cfg update.signature_slot
  if is_next_sync_committee_known store then
    require (update_signature_period = store_period ∨ update_signature_period = store_period + 1)
  else
    require (update_signature_period = store_period)
  -- Verify update is relevant
  let update_attested_period := compute_sync_committee_period_at_slot cfg update_attested_slot
  let update_has_next_sync_committee := !is_next_sync_committee_known store &&
    (is_sync_committee_update update && update_attested_period == store_period)
  require (update_attested_slot > store.finalized_header.beacon.slot ||
    update_has_next_sync_committee)
  -- Verify that the `finality_branch`, if present, confirms `finalized_header`
  -- to match the finalized checkpoint root saved in the state of `attested_header`.
  -- Note that the genesis finalized checkpoint root is represented as a zero hash.
  if !is_finality_update update then
    require update.finalized_header.isEmpty
  else
    let finalized_root ← if update_finalized_slot = GENESIS_SLOT then do
        require update.finalized_header.isEmpty
        pure zeroChunk
      else do
        require (is_valid_light_client_header cfg update.finalized_header)
        pure update.finalized_header.beacon.root
    require (is_valid_normalized_merkle_branch finalized_root update.finality_branch
      (finalized_root_gindex_at_slot cfg update.attested_header.beacon.slot)
      update.attested_header.beacon.stateRoot)
  -- Verify that the `next_sync_committee`, if present, actually is the next sync committee saved
  -- in the state of the `attested_header`
  if !is_sync_committee_update update then
    require (SyncCommittee.isEmpty update.next_sync_committee)
  else
    if update_attested_period = store_period ∧ is_next_sync_committee_known store then
      require (SyncCommittee.eq update.next_sync_committee store.next_sync_committee)
    require (is_valid_normalized_merkle_branch
      (hash_tree_root_sync_committee cfg update.next_sync_committee)
      update.next_sync_committee_branch
      (next_sync_committee_gindex_at_slot cfg update.attested_header.beacon.slot)
      update.attested_header.beacon.stateRoot)
  -- Verify sync committee aggregate signature
  let sync_committee := if update_signature_period = store_period then store.current_sync_committee
    else store.next_sync_committee
  let participant_pubkeys ← participant_pubkeys cfg sync_aggregate.bits sync_committee.pubkeys
  let fork_version_slot := saturating_sub update.signature_slot 1
  let fork_version := compute_fork_version cfg (compute_epoch_at_slot cfg fork_version_slot)
  let domain := Forks.computeDomain DOMAIN_SYNC_COMMITTEE fork_version genesis_validators_root
  let signing_root := Forks.signingRoot update.attested_header.beacon.root domain
  require (Bls.fastAggregateVerifyBytes participant_pubkeys signing_root sync_aggregate.signature)

/-- `apply_light_client_update`. -/
def apply_light_client_update (store : LightClientStore) (update : LightClientUpdate) :
    Option LightClientStore := do
  let store_period := compute_sync_committee_period_at_slot cfg store.finalized_header.beacon.slot
  let update_finalized_period :=
    compute_sync_committee_period_at_slot cfg update.finalized_header.beacon.slot
  let store ← if !is_next_sync_committee_known store then do
      require (update_finalized_period = store_period)
      pure { store with next_sync_committee := update.next_sync_committee }
    else if update_finalized_period = store_period + 1 then
      pure { store with
        current_sync_committee := store.next_sync_committee
        next_sync_committee := update.next_sync_committee
        previous_max_active_participants := store.current_max_active_participants
        current_max_active_participants := 0 }
    else pure store
  if update.finalized_header.beacon.slot > store.finalized_header.beacon.slot then
    let store := { store with finalized_header := update.finalized_header }
    if store.finalized_header.beacon.slot > store.optimistic_header.beacon.slot then
      pure { store with optimistic_header := store.finalized_header }
    else pure store
  else pure store

/-- `process_light_client_store_force_update`. -/
def process_light_client_store_force_update (store : LightClientStore) (current_slot : Nat) :
    Option LightClientStore :=
  match store.best_valid_update with
  | some best_valid_update =>
    if current_slot > store.finalized_header.beacon.slot + UPDATE_TIMEOUT cfg then do
      -- Forced best update when the update timeout has elapsed.
      let best_valid_update :=
        if best_valid_update.finalized_header.beacon.slot ≤ store.finalized_header.beacon.slot then
          { best_valid_update with finalized_header := best_valid_update.attested_header }
        else best_valid_update
      let store ← apply_light_client_update cfg store best_valid_update
      pure { store with best_valid_update := none }
    else pure store
  | none => pure store

/-- `process_light_client_update`. -/
def process_light_client_update (store : LightClientStore) (update : LightClientUpdate)
    (current_slot : Nat) (genesis_validators_root : ByteArray) : Option LightClientStore := do
  validate_light_client_update cfg store update current_slot genesis_validators_root
  let sync_committee_bits := update.sync_aggregate.bits
  -- Update the best update in case we have to force-update to it if the timeout elapses
  let store := match store.best_valid_update with
    | none => { store with best_valid_update := some update }
    | some best => if is_better_update cfg update best then
        { store with best_valid_update := some update } else store
  -- Track the maximum number of active participants in the committee signatures
  let store := { store with
    current_max_active_participants :=
      max store.current_max_active_participants (get_set_bit_count cfg sync_committee_bits) }
  -- Update the optimistic header
  let store :=
    if get_set_bit_count cfg sync_committee_bits > get_safety_threshold store ∧
        update.attested_header.beacon.slot > store.optimistic_header.beacon.slot then
      { store with optimistic_header := update.attested_header }
    else store
  -- Update finalized header
  let update_has_finalized_next_sync_committee :=
    !is_next_sync_committee_known store && is_sync_committee_update update &&
      is_finality_update update &&
      compute_sync_committee_period_at_slot cfg update.finalized_header.beacon.slot ==
        compute_sync_committee_period_at_slot cfg update.attested_header.beacon.slot
  if get_set_bit_count cfg sync_committee_bits * 3 ≥ cfg.SYNC_COMMITTEE_SIZE * 2 ∧
      (update.finalized_header.beacon.slot > store.finalized_header.beacon.slot ∨
        update_has_finalized_next_sync_committee) then
    -- Normal update through 2/3 threshold
    let store ← apply_light_client_update cfg store update
    pure { store with best_valid_update := none }
  else pure store

/-- `NextSyncCommitteeBranch()`, `FinalityBranch()` and `LightClientHeader.empty()` of the fork
whose containers carry `header`: Electra's and Fulu's branches are 6 and 7 roots deep, Gloas's 11
and 9. -/
def defaultsOf : LightClientHeader → Array ByteArray × Array ByteArray × LightClientHeader
  | .electra .. =>
    (Array.replicate (floorlog2 NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA) zeroChunk,
      Array.replicate (floorlog2 FINALIZED_ROOT_GINDEX_ELECTRA) zeroChunk,
      .electra ⟨0, 0, zeroChunk, zeroChunk, zeroChunk⟩
        ⟨zeroChunk, ⟨Array.replicate 20 0⟩, zeroChunk, zeroChunk, ⟨Array.replicate 256 0⟩,
          zeroChunk, 0, 0, 0, 0, ByteArray.empty, 0, zeroChunk, zeroChunk, zeroChunk, 0, 0⟩
        (Array.replicate (floorlog2 EXECUTION_PAYLOAD_GINDEX) zeroChunk))
  | .gloas .. =>
    (Array.replicate (floorlog2 NEXT_SYNC_COMMITTEE_GINDEX_GLOAS) zeroChunk,
      Array.replicate (floorlog2 FINALIZED_ROOT_GINDEX_GLOAS) zeroChunk,
      .gloas ⟨0, 0, zeroChunk, zeroChunk, zeroChunk⟩ zeroChunk
        (Array.replicate (floorlog2 EXECUTION_BLOCK_HASH_GINDEX_GLOAS) zeroChunk))

/-- `process_light_client_finality_update`. -/
def process_light_client_finality_update (store : LightClientStore)
    (finality_update : LightClientFinalityUpdate) (current_slot : Nat)
    (genesis_validators_root : ByteArray) : Option LightClientStore :=
  process_light_client_update cfg store
    { attested_header := finality_update.attested_header,
      next_sync_committee := SyncCommittee.empty cfg,
      next_sync_committee_branch := (defaultsOf finality_update.attested_header).1,
      finalized_header := finality_update.finalized_header,
      finality_branch := finality_update.finality_branch,
      sync_aggregate := finality_update.sync_aggregate,
      signature_slot := finality_update.signature_slot }
    current_slot genesis_validators_root

/-- `process_light_client_optimistic_update`. -/
def process_light_client_optimistic_update (store : LightClientStore)
    (optimistic_update : LightClientOptimisticUpdate) (current_slot : Nat)
    (genesis_validators_root : ByteArray) : Option LightClientStore :=
  process_light_client_update cfg store
    { attested_header := optimistic_update.attested_header,
      next_sync_committee := SyncCommittee.empty cfg,
      next_sync_committee_branch := (defaultsOf optimistic_update.attested_header).1,
      finalized_header := (defaultsOf optimistic_update.attested_header).2.2,
      finality_branch := (defaultsOf optimistic_update.attested_header).2.1,
      sync_aggregate := optimistic_update.sync_aggregate,
      signature_slot := optimistic_update.signature_slot }
    current_slot genesis_validators_root

/-! ## The stores the specification reaches -/

/-- The stores a light client following the specification reaches from `trusted_block_root`:
`initialize_light_client_store` of a bootstrap, then any number of
`process_light_client_update` steps (each passing `validate_light_client_update`) at clocks
`current_slot`, and of `process_light_client_store_force_update`, which the specification lets a
client call at its discretion. An update the specification rejects leaves the store as it was,
so a client that receives it reaches the same store. -/
inductive Reaches (genesis_validators_root trusted_block_root : ByteArray) :
    LightClientStore → Prop
  | init {bootstrap : LightClientBootstrap} {store : LightClientStore} :
      initialize_light_client_store cfg trusted_block_root bootstrap = some store →
      Reaches genesis_validators_root trusted_block_root store
  | update {store store' : LightClientStore} (update : LightClientUpdate) (current_slot : Nat) :
      Reaches genesis_validators_root trusted_block_root store →
      process_light_client_update cfg store update current_slot genesis_validators_root =
        some store' →
      Reaches genesis_validators_root trusted_block_root store'
  | force {store store' : LightClientStore} (current_slot : Nat) :
      Reaches genesis_validators_root trusted_block_root store →
      process_light_client_store_force_update cfg store current_slot = some store' →
      Reaches genesis_validators_root trusted_block_root store'

end LeanLight.Spec.LightClient
