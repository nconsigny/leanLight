import LeanLight.Base.Sha256
import LeanLight.Ssz.Decode

/-!
# SSZ: merkleization and branches

`hash_tree_root`'s building blocks over `ByteArray`, each written as ssz-specs' (vendored in
`LeanLightProofs/Vendor/SszSpecs`) is over `Array UInt8`, so that `LeanLightProofs.Ssz` proves each equal
to it: `hash64` is `combine`, `zeroHashes` is `zeroRoots`, `subtree` is `subtreeAt` (a bounded
tree's root, zero-padded), `pack` is `packBytes`, `leBytes` is `uintBytes`. Recursion is over a
tree's depth (at most 9 here: 512 keys) or an integer's width (at most 32 bytes), both fixed by
the type.

Branches: `climb` is ssz-specs' `climbBranch`, and `isValidNormalizedBranch` is the light client's
`is_valid_normalized_merkle_branch` (consensus-specs v1.7.0-beta.4,
`altair/light-client/sync-protocol.md:332-343`): the branch's leading extra roots are zero, and
the rest verifies as ssz-specs' `verifyMerkleProof` does, with every node 32 bytes.

The generalized indices the light client proves against are pinned here (`gindex*`) and
recomputed from the containers' field positions by `LeanLightProofs.SszGindex` (25b).
-/

namespace LeanLight.Lc.Ssz

/-- A node's width. -/
abbrev chunkSize : Nat := 32

/-- The all-zero node. -/
def zeroChunk : ByteArray := ⟨Array.replicate chunkSize 0⟩

/-- Two nodes folded into their parent: SHA-256 of the 64 bytes. -/
def hash64 (left right : ByteArray) : ByteArray := Ssz.Sha256.hash (left ++ right)

/-- The roots of the all-zero trees of depth 0 to `d`. -/
def zeroHashesUpTo : Nat → Array ByteArray
  | 0 => #[zeroChunk]
  | d + 1 =>
    let below := zeroHashesUpTo d
    let deepest := below[d]?.getD zeroChunk
    below.push (hash64 deepest deepest)

/-- The roots of the all-zero trees of depth 0 to 64, computed once. -/
def zeroHashes : Array ByteArray := zeroHashesUpTo 64

/-- The root of the all-zero tree of depth `d`, for `d ≤ 64`. -/
def zeroHash (d : Nat) : ByteArray := zeroHashes[d]?.getD zeroChunk

/-- The root of the perfect tree of depth `d` over the nodes of `chunks` from `start`, a node past
the end being zero: ssz-specs' `subtreeAt`. -/
def subtree (chunks : Array ByteArray) : Nat → Nat → ByteArray
  | d, start =>
    if start ≥ chunks.size then zeroHash d
    else
      match d with
      | 0 => chunks[start]?.getD zeroChunk
      | d + 1 => hash64 (subtree chunks d start) (subtree chunks d (start + 2 ^ d))

/-- Bytes cut into 32-byte nodes, the last one zero-padded: ssz-specs' `packBytes`. -/
def pack (data : ByteArray) : Array ByteArray :=
  Array.ofFn (n := (data.size + chunkSize - 1) / chunkSize) fun p =>
    let piece := Bytes.extract data (p.val * chunkSize) (p.val * chunkSize + chunkSize)
    piece ++ ⟨Array.replicate (chunkSize - piece.size) 0⟩

/-- The `w` little-endian bytes of `v mod 256 ^ w`: ssz-specs' `uintBytes`. -/
def leBytes : Nat → Nat → ByteArray
  | 0, _ => .empty
  | w + 1, v => ⟨#[UInt8.ofNat (v % 256)]⟩ ++ leBytes w (v / 256)

/-- The root of bytes packed into a tree of depth `d` (a `ByteVector`, or a basic value). -/
def bytesRoot (data : ByteArray) (d : Nat) : ByteArray := subtree (pack data) d 0

/-- The root of a `uint64`. -/
def u64Root (v : Nat) : ByteArray := bytesRoot (leBytes 8 v) 0

/-- The root of a `uint256`. -/
def u256Root (v : Nat) : ByteArray := bytesRoot (leBytes 32 v) 0

/-- A root mixed with a length, as a list's root is: `mix_in_length`. -/
def mixInLength (root : ByteArray) (length : Nat) : ByteArray := hash64 root (leBytes 32 length)

/-! ## Branches -/

/-- The root a branch climbs to from `node`, its siblings `branch[from + level]` for `level`
below `n`, the side of each read from bit `level` of `gindex`: ssz-specs' `climbBranch`. -/
def climb (gindex : Nat) (branch : Array ByteArray) (start : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, node => node
  | n + 1, level, node =>
    let sibling := branch[start + level]?.getD zeroChunk
    climb gindex branch start n (level + 1)
      (if gindex.testBit level then hash64 sibling node else hash64 node sibling)

/-- Whether `leaf` sits at `gindex` under `root`, by a branch whose leading extra roots are zero:
consensus-specs' `is_valid_normalized_merkle_branch`, refusing what ssz-specs' verifier refuses
(a root as the index, a branch shorter than the depth, a node not 32 bytes wide). -/
def isValidNormalizedBranch (leaf : ByteArray) (branch : Array ByteArray) (gindex : Nat)
    (root : ByteArray) : Bool :=
  let depth := gindex.log2
  let extra := branch.size - depth
  2 ≤ gindex && depth ≤ branch.size && leaf.size == chunkSize &&
    branch.all (·.size == chunkSize) &&
    (branch.extract 0 extra).all (·.data.all (· == 0)) &&
    (climb gindex branch extra depth 0 leaf).data == root.data

/-! ## The generalized indices -/

/-- `finalized_checkpoint.root` in an Altair to Deneb `BeaconState` (`FINALIZED_ROOT_GINDEX`). -/
def gindexFinalizedRootAltair : Nat := 105
/-- `current_sync_committee` in an Altair to Deneb `BeaconState` (`CURRENT_SYNC_COMMITTEE_GINDEX`). -/
def gindexCurrentSyncCommitteeAltair : Nat := 54
/-- `next_sync_committee` in an Altair to Deneb `BeaconState` (`NEXT_SYNC_COMMITTEE_GINDEX`). -/
def gindexNextSyncCommitteeAltair : Nat := 55
/-- `finalized_checkpoint.root` in an Electra or Fulu `BeaconState` (`FINALIZED_ROOT_GINDEX_ELECTRA`). -/
def gindexFinalizedRootElectra : Nat := 169
/-- `current_sync_committee` in an Electra or Fulu `BeaconState`. -/
def gindexCurrentSyncCommitteeElectra : Nat := 86
/-- `next_sync_committee` in an Electra or Fulu `BeaconState`. -/
def gindexNextSyncCommitteeElectra : Nat := 87
/-- `execution_payload` in a Capella to Fulu `BeaconBlockBody` (`EXECUTION_PAYLOAD_GINDEX`). -/
def gindexExecutionPayload : Nat := 25
/-- `execution_payload.block_hash` in a Deneb to Fulu `BeaconBlockBody`
(`EXECUTION_BLOCK_HASH_GINDEX_DENEB`): the block's own payload hash, under an upgraded header. -/
def gindexExecutionBlockHashDeneb : Nat := 812
/-- `finalized_checkpoint.root` in a Gloas `BeaconState` (a `ProgressiveContainer`). -/
def gindexFinalizedRootGloas : Nat := 735
/-- `current_sync_committee` in a Gloas `BeaconState`. -/
def gindexCurrentSyncCommitteeGloas : Nat := 2945
/-- `next_sync_committee` in a Gloas `BeaconState`. -/
def gindexNextSyncCommitteeGloas : Nat := 2946
/-- `signed_execution_payload_bid.message.parent_block_hash` in a Gloas `BeaconBlockBody`
(`EXECUTION_BLOCK_HASH_GINDEX_GLOAS`): the parent payload's hash. -/
def gindexExecutionBlockHashGloas : Nat := 2856

end LeanLight.Lc.Ssz
