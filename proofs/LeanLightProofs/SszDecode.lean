import LeanLightProofs.SszRoot

/-!
# The light client's decoders are ssz-specs' `deserialize`, and canonical

Every fixed-size `LeanLight.Ssz` decoder (`BeaconBlockHeader`, `SyncCommittee`, `SyncAggregate`,
and the five `Gloas.*` containers; variable-size containers follow in `SszDecodeElectra`) accepts
exactly what ssz-specs' `deserialize` accepts at the container's `Desc` (`decode_iff` for each,
alongside `Fits` on containers holding a `SyncAggregate`, whose `toValue` unpacks 512 bits from
its 64-byte `bits` field), and returns the typed value denoting what `deserialize` returns
(`deserialize_isSome` when it rejects, `decode_iff` when it accepts).

Every value any of the fourteen decoders returns fits its container's type (`decode_fits`, and
`toValue_fits` for ssz-specs' `Fits`): integers below 2⁶⁴ (2²⁵⁶ for `base_fee_per_gas`), roots of
32 bytes, 512 keys of 48 bytes, 64 bytes of `sync_committee_bits`, branches of the type's length,
at most 32 bytes of `extra_data`. So:

* **Merkle root** (`decode_root`): its `root` is ssz-specs' `hashTreeRoot` of the value it denotes;
* **Canonicality** (`decode_canonical`): `serialize` of the decoded value reproduces the input
  bytes `bs.data` byte for byte;
* **Non-malleability** (`decode_injective_bytes`): no two accepted `ByteArray`s decode to the
  same container value;
* **Round trip** (`decode_serialize`): every `Fits` value serializes to bytes that `decode`
  recovers identically (`toValue_inj`).
-/

namespace LeanLight.Lc.Ssz

open LeanLight.Lc.Bytes (byteAt)
open _root_.Ssz (Bytes Desc Value Err hashTreeRoot deserialize serialize readUint unpackBits
  readSlots structBudget structSlices vectorSlices deserializeEach deserializeFields offsetSpans
  takeSlots bodyStarts Slot bytesPerOffset)

theorem readLE_lt (bs : ByteArray) (off w : Nat) : readLE bs off w < 2 ^ (8 * w) := by
  induction w generalizing off with
  | zero => simp [readLE]
  | succ w ih =>
    have h1 := ih (off + 1)
    have h2 := (byteAt bs off).toNat_lt
    rw [readLE, show 8 * (w + 1) = 8 * w + 8 by omega, Nat.pow_add,
      show (2 : Nat) ^ 8 = 256 from rfl]
    generalize 2 ^ (8 * w) = X at h1 ⊢
    generalize readLE bs (off + 1) w = r at h1 ⊢
    generalize (byteAt bs off).toNat = b at h2 ⊢
    have : 2 ^ 8 = 256 := rfl
    omega

theorem u64_lt (bs : ByteArray) (off : Nat) : u64 bs off < 2 ^ 64 := readLE_lt bs off 8

theorem slice_size (bs : ByteArray) (off n : Nat) (h : off + n ≤ bs.size) :
    (slice bs off n).size = n := by
  simp [slice, Bytes.extract]; omega

theorem fields_size (bs : ByteArray) (off w k : Nat) : (fields bs off w k).size = k := by
  simp [fields]

theorem fields_mem (bs : ByteArray) (off w k : Nat) (h : off + w * k ≤ bs.size) :
    ∀ x ∈ fields bs off w k, x.size = w := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  simp only [fields, Array.getElem_ofFn]
  apply slice_size
  have : i < k := by simpa [fields] using hi
  have : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left _ this
  rw [Nat.mul_succ] at this
  omega

theorem roots_fits (bs : ByteArray) (off k : Nat) (h : off + 32 * k ≤ bs.size) :
    BranchFits (roots bs off k) k :=
  ⟨fields_size _ _ _ _, fields_mem _ _ _ _ h⟩

theorem BeaconBlockHeader.read_fits (bs : ByteArray) (h : 112 ≤ bs.size) : (read bs).Fits :=
  ⟨u64_lt _ _, u64_lt _ _, slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
    slice_size _ _ _ (by omega)⟩

theorem BeaconBlockHeader.decode_fits {bs : ByteArray} {h : BeaconBlockHeader}
    (hd : decode bs = some h) : h.Fits := by
  unfold decode at hd
  split at hd
  · rename_i hs; cases hd; exact read_fits bs (by rw [hs]; decide)
  · cases hd

theorem SyncCommittee.read_fits (bs : ByteArray) (h : 24624 ≤ bs.size) : (read bs).Fits := by
  have hp : (read bs).pubkeys = fields bs 0 48 syncCommitteeSize := by simp only [read]
  have ha : (read bs).aggregatePubkey = slice bs (48 * syncCommitteeSize) 48 := by simp only [read]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]; exact fields_size _ _ _ _
  · rw [hp]; exact fields_mem bs 0 48 syncCommitteeSize (by show 0 + 48 * 512 ≤ bs.size; omega)
  · rw [ha]; exact slice_size bs (48 * syncCommitteeSize) 48 (by show 48 * 512 + 48 ≤ bs.size; omega)

theorem SyncCommittee.decode_fits {bs : ByteArray} {c : SyncCommittee}
    (hd : decode bs = some c) : c.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    rw [← Option.some.inj hd]
    exact read_fits bs (by rw [hs]; show 24624 ≤ 48 * 512 + 48; omega)
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem SyncAggregate.read_fits (bs : ByteArray) (h : 160 ≤ bs.size) : (read bs).Fits where
  bits := slice_size bs 0 (syncCommitteeSize / 8) (by show 0 + 512 / 8 ≤ bs.size; omega)
  signature := slice_size bs (syncCommitteeSize / 8) 96 (by show 512 / 8 + 96 ≤ bs.size; omega)

theorem SyncAggregate.decode_fits {bs : ByteArray} {a : SyncAggregate}
    (hd : decode bs = some a) : a.Fits := by
  unfold decode at hd
  split at hd
  · rename_i hs; cases hd; exact read_fits bs (by rw [hs]; decide)
  · cases hd

theorem extract_size (bs : ByteArray) (a b : Nat) (h : a ≤ b) (hb : b ≤ bs.size) :
    (Bytes.extract bs a b).size = b - a := by
  simp [Bytes.extract]; omega

theorem ExecutionPayloadHeader.decode_fits {bs : ByteArray} {e : ExecutionPayloadHeader}
    (hd : decode bs = some e) : e.Fits := by
  unfold decode at hd
  split at hd
  · rename_i hc
    have h₁ : 584 ≤ bs.size := hc.1
    have h₂ : bs.size ≤ 616 := hc.2.1
    cases hd
    exact ⟨slice_size _ _ _ (by omega), slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
      slice_size _ _ _ (by omega), slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
      u64_lt _ _, u64_lt _ _, u64_lt _ _, u64_lt _ _,
      by rw [extract_size _ _ _ (by show 584 ≤ bs.size; omega) (Nat.le_refl _)]
         show bs.size - 584 ≤ 32; omega,
      readLE_lt _ _ 32, slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
      slice_size _ _ _ (by omega), u64_lt _ _, u64_lt _ _⟩
  · cases hd

theorem Electra.Header.decode_fits {bs : ByteArray} {h : Electra.Header}
    (hd : decode bs = some h) : h.Fits := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 112 = fixedSize
  · rw [ite_eq_left hc] at hd
    have hs : 244 ≤ bs.size := hc.1
    cases he : ExecutionPayloadHeader.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [he] at hd; exact absurd hd (by simp)
    | some e =>
      rw [he] at hd
      rw [← Option.some.inj hd]
      refine ⟨BeaconBlockHeader.read_fits _ ?_, ExecutionPayloadHeader.decode_fits he, ?_⟩
      · rw [slice_size bs 0 112 (by omega)]; exact Nat.le_refl _
      · exact roots_fits bs 116 executionBranchLength (by show 116 + 32 * 4 ≤ bs.size; omega)
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.Bootstrap.decode_fits {bs : ByteArray} {b : Electra.Bootstrap}
    (hd : decode bs = some b) : b.Fits := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · rw [ite_eq_left hc] at hd
    have hs : 24820 ≤ bs.size := hc.1
    cases he : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [he] at hd; exact absurd hd (by simp)
    | some h =>
      rw [he] at hd
      rw [← Option.some.inj hd]
      refine ⟨Header.decode_fits he, SyncCommittee.read_fits _ ?_, ?_⟩
      · rw [slice_size _ _ _ (by show 4 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
      · exact roots_fits _ _ _ (by show 4 + (48 * 512 + 48) + 32 * 6 ≤ bs.size; omega)
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.Update.decode_fits {bs : ByteArray} {u : Electra.Update}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  simp only at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs finalizedOffsetAt ∧ offsetAt bs finalizedOffsetAt ≤ bs.size
  · rw [ite_eq_left hc] at hd
    have hs : 25216 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt)) with
    | none => rw [ha] at hd; exact absurd hd (by simp)
    | some a =>
      cases hf : Header.decode (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size) with
      | none => rw [ha, hf] at hd; exact absurd hd (by simp)
      | some f =>
        rw [ha, hf] at hd
        rw [← Option.some.inj hd]
        refine ⟨Header.decode_fits ha, SyncCommittee.read_fits _ ?_, ?_, Header.decode_fits hf,
          ?_, SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
        · rw [slice_size _ _ _ (by show 4 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
        · exact roots_fits _ _ _ (by show 4 + (48 * 512 + 48) + 32 * 6 ≤ bs.size; omega)
        · exact roots_fits _ _ _ (by
            show 4 + (48 * 512 + 48) + 32 * 6 + 4 + 32 * 7 ≤ bs.size; omega)
        · rw [slice_size _ _ _ (by
            show 4 + (48 * 512 + 48) + 32 * 6 + 4 + 32 * 7 + (512 / 8 + 96) ≤ bs.size; omega)]
          decide
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.FinalityUpdate.decode_fits {bs : ByteArray} {u : Electra.FinalityUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  simp only at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs 4 ∧ offsetAt bs 4 ≤ bs.size
  · rw [ite_eq_left hc] at hd
    have hs : 400 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize (offsetAt bs 4)) with
    | none => rw [ha] at hd; exact absurd hd (by simp)
    | some a =>
      cases hf : Header.decode (Bytes.extract bs (offsetAt bs 4) bs.size) with
      | none => rw [ha, hf] at hd; exact absurd hd (by simp)
      | some f =>
        rw [ha, hf] at hd
        rw [← Option.some.inj hd]
        refine ⟨Header.decode_fits ha, Header.decode_fits hf, ?_, SyncAggregate.read_fits _ ?_,
          u64_lt _ _⟩
        · exact roots_fits _ _ _ (by show 8 + 32 * 7 ≤ bs.size; omega)
        · rw [slice_size _ _ _ (by show 8 + 32 * 7 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.OptimisticUpdate.decode_fits {bs : ByteArray} {u : Electra.OptimisticUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · rw [ite_eq_left hc] at hd
    have hs : 172 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [ha] at hd; exact absurd hd (by simp)
    | some a =>
      rw [ha] at hd
      rw [← Option.some.inj hd]
      refine ⟨Header.decode_fits ha, SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
      rw [slice_size _ _ _ (by show 4 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Gloas.Header.read_fits (bs : ByteArray) (h : 496 ≤ bs.size) : (read bs).Fits := by
  refine ⟨BeaconBlockHeader.read_fits _ ?_, ?_, ?_⟩
  · rw [slice_size _ _ _ (by show 0 + 112 ≤ bs.size; omega)]; decide
  · exact slice_size _ _ _ (by show 112 + 32 ≤ bs.size; omega)
  · exact roots_fits _ _ _ (by show 112 + 32 + 32 * 11 ≤ bs.size; omega)

theorem Gloas.Header.decode_fits {bs : ByteArray} {h : Gloas.Header}
    (hd : decode bs = some h) : h.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    rw [← Option.some.inj hd]
    exact read_fits bs (by rw [hs]; decide)
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.Bootstrap.decode_fits {bs : ByteArray} {b : Gloas.Bootstrap}
    (hd : decode bs = some b) : b.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 25472 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, SyncCommittee.read_fits _ ?_, ?_⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 496 + (48 * 512 + 48) + 32 * 11 ≤ bs.size; omega)
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.Update.decode_fits {bs : ByteArray} {u : Gloas.Update}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 26424 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, SyncCommittee.read_fits _ ?_, ?_, Header.read_fits _ ?_, ?_,
      SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 496 + (48 * 512 + 48) + 32 * 11 ≤ bs.size; omega)
    · rw [slice_size _ _ _ (by show 25472 + 496 ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 25472 + 496 + 32 * 9 ≤ bs.size; omega)
    · rw [slice_size _ _ _ (by show 26256 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.FinalityUpdate.decode_fits {bs : ByteArray} {u : Gloas.FinalityUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 1448 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, Header.read_fits _ ?_, ?_, SyncAggregate.read_fits _ ?_,
      u64_lt _ _⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + 496 ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 2 * 496 + 32 * 9 ≤ bs.size; omega)
    · rw [slice_size _ _ _ (by show 1280 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.OptimisticUpdate.decode_fits {bs : ByteArray} {u : Gloas.OptimisticUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 664 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

/-! ## Decoded, then hashed -/

/-- The root of a `BeaconBlockHeader` decoded from any bytes is ssz-specs' `hashTreeRoot` of the
value it denotes. -/
theorem BeaconBlockHeader.decode_root {bs : ByteArray} {h : BeaconBlockHeader}
    (hd : decode bs = some h) : hashTreeRoot beaconBlockHeaderDesc h.toValue = .ok h.root.data :=
  root_eq h (decode_fits hd)

/-- Likewise for a `SyncCommittee`. -/
theorem SyncCommittee.decode_root {bs : ByteArray} {c : SyncCommittee}
    (hd : decode bs = some c) : hashTreeRoot syncCommitteeDesc c.toValue = .ok c.root.data :=
  root_eq c (decode_fits hd)

/-- Likewise for a `SyncAggregate`. -/
theorem SyncAggregate.decode_root {bs : ByteArray} {a : SyncAggregate}
    (hd : decode bs = some a) : hashTreeRoot syncAggregateDesc a.toValue = .ok a.root.data :=
  root_eq a (decode_fits hd)

/-- Likewise for an `ExecutionPayloadHeader`. -/
theorem ExecutionPayloadHeader.decode_root {bs : ByteArray} {e : ExecutionPayloadHeader}
    (hd : decode bs = some e) :
    hashTreeRoot executionPayloadHeaderDesc e.toValue = .ok e.root.data :=
  root_eq e (decode_fits hd)

/-- Likewise for an Electra (or Fulu) `LightClientHeader`. -/
theorem Electra.Header.decode_root {bs : ByteArray} {h : Electra.Header}
    (hd : decode bs = some h) : hashTreeRoot electraHeaderDesc h.toValue = .ok h.root.data :=
  root_eq h (decode_fits hd)

/-- Likewise for an Electra `LightClientBootstrap`. -/
theorem Electra.Bootstrap.decode_root {bs : ByteArray} {b : Electra.Bootstrap}
    (hd : decode bs = some b) : hashTreeRoot electraBootstrapDesc b.toValue = .ok b.root.data :=
  root_eq b (decode_fits hd)

/-- Likewise for an Electra `LightClientUpdate`. -/
theorem Electra.Update.decode_root {bs : ByteArray} {u : Electra.Update}
    (hd : decode bs = some u) : hashTreeRoot electraUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for an Electra `LightClientFinalityUpdate`. -/
theorem Electra.FinalityUpdate.decode_root {bs : ByteArray} {u : Electra.FinalityUpdate}
    (hd : decode bs = some u) :
    hashTreeRoot electraFinalityUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for an Electra `LightClientOptimisticUpdate`. -/
theorem Electra.OptimisticUpdate.decode_root {bs : ByteArray} {u : Electra.OptimisticUpdate}
    (hd : decode bs = some u) :
    hashTreeRoot electraOptimisticUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for a Gloas `LightClientHeader`. -/
theorem Gloas.Header.decode_root {bs : ByteArray} {h : Gloas.Header}
    (hd : decode bs = some h) : hashTreeRoot gloasHeaderDesc h.toValue = .ok h.root.data :=
  root_eq h (decode_fits hd)

/-- Likewise for a Gloas `LightClientBootstrap`. -/
theorem Gloas.Bootstrap.decode_root {bs : ByteArray} {b : Gloas.Bootstrap}
    (hd : decode bs = some b) : hashTreeRoot gloasBootstrapDesc b.toValue = .ok b.root.data :=
  root_eq b (decode_fits hd)

/-- Likewise for a Gloas `LightClientUpdate`. -/
theorem Gloas.Update.decode_root {bs : ByteArray} {u : Gloas.Update}
    (hd : decode bs = some u) : hashTreeRoot gloasUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for a Gloas `LightClientFinalityUpdate`. -/
theorem Gloas.FinalityUpdate.decode_root {bs : ByteArray} {u : Gloas.FinalityUpdate}
    (hd : decode bs = some u) : hashTreeRoot gloasFinalityUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for a Gloas `LightClientOptimisticUpdate`. -/
theorem Gloas.OptimisticUpdate.decode_root {bs : ByteArray} {u : Gloas.OptimisticUpdate}
    (hd : decode bs = some u) :
    hashTreeRoot gloasOptimisticUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-! ## Field readers and slice steps -/

theorem byteAt_data (bs : ByteArray) (i : Nat) : byteAt bs i = bs.data[i]?.getD 0 := by
  rw [Bytes.byteAt_eq, Array.getElem?_toList]

/-- `readLE` is ssz-specs' `readUint` on `bs.data`. -/
theorem readLE_eq_readUint (bs : ByteArray) (off w : Nat) :
    readLE bs off w = readUint bs.data off w := by
  induction w generalizing off with
  | zero => rfl
  | succ w ih =>
    simp only [readLE, readUint, byteAt_data, ih]

theorem u64_eq_readUint (bs : ByteArray) (off : Nat) :
    u64 bs off = readUint bs.data off 8 :=
  readLE_eq_readUint bs off 8

theorem offsetAt_eq_readUint (bs : ByteArray) (off : Nat) :
    offsetAt bs off = readUint bs.data off 4 :=
  readLE_eq_readUint bs off 4

theorem extract_data_of_le (bs : ByteArray) (a b : Nat) (ha : a ≤ b) (hb : b ≤ bs.size) :
    (Bytes.extract bs a b).data = bs.data.extract a b := by
  simp only [Bytes.extract, ByteArray.data_extract, Nat.min_eq_left (Nat.le_trans ha hb),
    Nat.min_eq_left hb]

theorem slice_data_of_le (bs : ByteArray) (off n : Nat) (h : off + n ≤ bs.size) :
    (slice bs off n).data = bs.data.extract off (off + n) :=
  extract_data_of_le bs off (off + n) (by omega) h

theorem extract_slice (bs : ByteArray) (off n a b : Nat) (h : off + n ≤ bs.size) (hb : b ≤ n) :
    Bytes.extract (slice bs off n) a b = Bytes.extract bs (off + a) (off + b) := by
  by_cases ha : a ≤ b
  · apply ByteArray.ext
    rw [extract_data_of_le (slice bs off n) a b ha (by rw [slice_size bs off n h]; exact hb),
      slice_data_of_le bs off n h,
      extract_data_of_le bs (off + a) (off + b) (by omega) (by omega)]
    apply Array.ext
    · simp; omega
    · intro i h1 h2
      simp [Nat.add_assoc]
  · apply ByteArray.ext
    simp only [Bytes.extract, ByteArray.data_extract]
    apply Array.ext
    · simp; omega
    · intro i h1 _
      simp at h1; omega

theorem slice_slice (bs : ByteArray) (off n a m : Nat) (h : off + n ≤ bs.size) (hm : a + m ≤ n) :
    slice (slice bs off n) a m = slice bs (off + a) m := by
  simpa [slice, Nat.add_assoc] using extract_slice bs off n a (a + m) h hm

theorem byteAt_slice (bs : ByteArray) (off n i : Nat) (_h : off + n ≤ bs.size) (hi : i < n) :
    byteAt (slice bs off n) i = byteAt bs (off + i) := by
  rw [Bytes.byteAt_eq, slice, Bytes.extract_eq, Bytes.byteAt_eq]
  simp only [List.getElem?_take, List.getElem?_drop, show off + i < off + n by omega, ite_true]

theorem readLE_slice (bs : ByteArray) (off n a w : Nat) (h : off + n ≤ bs.size)
    (hw : a + w ≤ n) : readLE (slice bs off n) a w = readLE bs (off + a) w := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    simp only [readLE, byteAt_slice bs off n a h (by omega),
      ih (a + 1) (by omega), Nat.add_assoc]

theorem u64_slice (bs : ByteArray) (off n a : Nat) (h : off + n ≤ bs.size) (hw : a + 8 ≤ n) :
    u64 (slice bs off n) a = u64 bs (off + a) :=
  readLE_slice bs off n a 8 h hw

theorem fields_slice (bs : ByteArray) (off n a w k : Nat) (h : off + n ≤ bs.size)
    (hk : a + w * k ≤ n) : fields (slice bs off n) a w k = fields bs (off + a) w k := by
  apply Array.ext
  · simp [fields]
  · intro i h1 h2
    simp only [fields, Array.getElem_ofFn]
    have hi : i < k := by simpa [fields] using h1
    have : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    rw [slice_slice bs off n (a + w * i) w h (by omega), Nat.add_assoc]

theorem roots_slice (bs : ByteArray) (off n a k : Nat) (h : off + n ≤ bs.size)
    (hk : a + 32 * k ≤ n) : roots (slice bs off n) a k = roots bs (off + a) k :=
  fields_slice bs off n a 32 k h hk

theorem readUint_extract (data : Bytes) (off n w : Nat) (h : off + n ≤ data.size) (hw : w ≤ n) :
    readUint (data.extract off (off + n)) 0 w = readUint data off w := by
  have hs : (slice ⟨data⟩ off n).data = data.extract off (off + n) :=
    slice_data_of_le ⟨data⟩ off n h
  rw [← hs, ← readLE_eq_readUint, ← readLE_eq_readUint ⟨data⟩]
  simpa using readLE_slice ⟨data⟩ off n 0 w h (by omega)

theorem deserialize_uint_slice (bs : ByteArray) (off w : Nat) (h : off + w ≤ bs.size) :
    deserialize (.uint w) (bs.data.extract off (off + w)) = .ok (.uint (readLE bs off w)) := by
  have hs : (bs.data.extract off (off + w)).size = w := by simp; omega
  simp only [deserialize, hs, bne_self_eq_false, Bool.false_eq_true, ite_false,
    readUint_extract bs.data off w w (by simpa using h) (Nat.le_refl _),
    ← readLE_eq_readUint, pure, Except.pure]

theorem deserialize_byteVector_slice (bs : ByteArray) (off k : Nat)
    (hk : k < 2 ^ (8 * bytesPerOffset)) (h : off + k ≤ bs.size) :
    deserialize (.byteVector k) (bs.data.extract off (off + k)) =
      .ok (.bytes (slice bs off k).data) := by
  have hs : (bs.data.extract off (off + k)).size = k := by simp; omega
  rw [← slice_data_of_le bs off k h] at hs ⊢
  simp only [deserialize, hs, show ¬ k ≥ 2 ^ (8 * bytesPerOffset) by omega, ite_false,
    bne_self_eq_false, Bool.false_eq_true, pure, Except.pure]

theorem deserialize_bitVector_512_slice (bs : ByteArray) (off : Nat) (h : off + 64 ≤ bs.size) :
    deserialize (.bitVector 512) (bs.data.extract off (off + 64)) =
      .ok (.bits (unpackBits (slice bs off 64).data 512)) := by
  rw [← slice_data_of_le bs off 64 h]
  have hs : (slice bs off 64).data.size = 64 := by simpa using slice_size bs off 64 h
  simp [deserialize, hs, pure, Except.pure]

theorem deserializeEach_byteVector (w : Nat) (hw : w < 2 ^ (8 * bytesPerOffset)) :
    ∀ (k : Nat) (bs : ByteArray) (off : Nat), off + w * k ≤ bs.size →
      deserializeEach (.byteVector w)
        ((List.range k).map fun i => (bs.data.extract off (off + w * k)).extract (i * w) ((i + 1) * w)) =
        .ok ((fields bs off w k).toList.map fun x => .bytes x.data) := by
  intro k
  induction k with
  | zero => intro _ _ _; simp [deserializeEach, fields]
  | succ k ih =>
    intro bs off h
    have hmul : w * (k + 1) = w * k + w := Nat.mul_succ w k
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, deserializeEach]
    have hex0 : (bs.data.extract off (off + w * (k + 1))).extract (0 * w) ((0 + 1) * w) =
        bs.data.extract off (off + w) := by
      apply Array.ext
      · simp [hmul]
      · intro j hj1 hj2
        simp only [Array.getElem_extract, Nat.zero_mul, Nat.zero_add]
    rw [hex0, deserialize_byteVector_slice bs off w hw (by omega)]
    have hrest : (List.map ((fun i => (bs.data.extract off (off + w * (k + 1))).extract (i * w) ((i + 1) * w)) ∘ Nat.succ) (List.range k)) =
        (List.range k).map fun i => (bs.data.extract (off + w) (off + w + w * k)).extract (i * w) ((i + 1) * w) := by
      apply List.map_congr_left
      intro i hi
      have hik : i < k := List.mem_range.mp hi
      have hwi : i * w + w ≤ w * k := by
        have := Nat.mul_le_mul_left w hik
        rw [Nat.mul_succ, Nat.mul_comm w i] at this
        exact this
      simp only [Function.comp]
      apply Array.ext
      · simp [Nat.succ_mul, hmul]; omega
      · intro j hj1 hj2
        simp only [Array.getElem_extract]
        congr 1; simp [Nat.succ_mul]; omega
    rw [hrest, ih bs (off + w) (by omega)]
    simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    have hfn : (fields bs off w (k + 1)).toList =
        slice bs off w :: (fields bs (off + w) w k).toList := by
      apply List.ext_getElem
      · simp [fields]
      · intro i hi1 hi2
        cases i with
        | zero => simp [fields]
        | succ j =>
          simp only [Array.getElem_toList, List.getElem_cons_succ, fields, Array.getElem_ofFn,
            Nat.mul_succ]
          congr 1; omega
    rw [hfn, List.map_cons]

theorem deserialize_vector_byteVector_slice (bs : ByteArray) (off w k : Nat)
    (hwk : w * k < 2 ^ (8 * bytesPerOffset)) (hw : w < 2 ^ (8 * bytesPerOffset))
    (h : off + w * k ≤ bs.size) :
    deserialize (.vector (.byteVector w) k) (bs.data.extract off (off + w * k)) =
      .ok (.seq ((fields bs off w k).toList.map fun x => .bytes x.data)) := by
  have hs : (bs.data.extract off (off + w * k)).size = w * k := by simp; omega
  have hf : (Desc.byteVector w).fixedSize = some w := rfl
  simp only [deserialize, vectorSlices, hf, hs,
    show ¬ w * k ≥ 2 ^ (8 * bytesPerOffset) by omega, ite_false,
    bne_self_eq_false, Bool.false_eq_true, Bind.bind, Except.bind, pure, Except.pure,
    deserializeEach_byteVector w hw k bs off h]

theorem deserialize_branch_slice (bs : ByteArray) (off k : Nat)
    (hk : 32 * k < 2 ^ (8 * bytesPerOffset)) (h : off + 32 * k ≤ bs.size) :
    deserialize (branchDesc k) (bs.data.extract off (off + 32 * k)) =
      .ok (branchValue (roots bs off k)) :=
  deserialize_vector_byteVector_slice bs off 32 k hk (by decide) h

theorem deserialize_byteList_slice (bs : ByteArray) (a b lim : Nat)
    (ha : a ≤ b) (hb : b ≤ bs.size) (hsize : b < 2 ^ (8 * bytesPerOffset)) :
    deserialize (.byteList lim) (bs.data.extract a b) =
      if b - a ≤ lim then .ok (.bytes (Bytes.extract bs a b).data)
      else .error (.overLimit lim (b - a)) := by
  have hs : (bs.data.extract a b).size = b - a := by simp; omega
  have hov : ¬ 2 ^ (8 * bytesPerOffset) ≤ b - a := by omega
  rw [extract_data_of_le bs a b ha hb]
  simp only [deserialize, hs, hov, ite_false]
  by_cases hlim : b - a ≤ lim
  · simp [show ¬ lim < b - a by omega, hlim, pure, Except.pure]
  · simp [show lim < b - a by omega, hlim, _root_.Ssz.throw_error, Bind.bind, Except.bind]

theorem deserialize_overflow {names : List String} {fs : List Desc} {data : Bytes}
    (h : data.size ≥ 2 ^ (8 * bytesPerOffset)) :
    deserialize (.container names fs) data = .error (.offsetOverflow data.size) := by
  simp [deserialize, _root_.Ssz.structSlices_overflow fs data h, Bind.bind, Except.bind]

theorem deserialize_size_lt {names : List String} {fs : List Desc} {data : Bytes} {v : Value}
    (hd : deserialize (.container names fs) data = .ok v) :
    data.size < 2 ^ (8 * bytesPerOffset) := by
  by_cases h : data.size < 2 ^ (8 * bytesPerOffset)
  · exact h
  · rw [deserialize_overflow (Nat.not_lt.mp h)] at hd
    cases hd

/-! ## Injectivity of `toValue` and correspondence with ssz-specs' `Fits` -/

theorem unpackBits_512_inj {a b : ByteArray} (ha : a.size = 64) (hb : b.size = 64)
    (h : unpackBits a.data 512 = unpackBits b.data 512) : a = b := by
  apply ByteArray.ext
  rw [← packBits_unpackBits_512 a.data (by simpa using ha),
    ← packBits_unpackBits_512 b.data (by simpa using hb), h]

theorem bytes_list_inj : ∀ {l₁ l₂ : List ByteArray},
    (l₁.map fun x => Value.bytes x.data) = (l₂.map fun x => Value.bytes x.data) → l₁ = l₂
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq, Value.bytes.injEq] at h
    rw [ByteArray.ext h.1, bytes_list_inj h.2]

theorem branchValue_inj {a b : Array ByteArray} (h : branchValue a = branchValue b) : a = b := by
  simp only [branchValue, Value.seq.injEq] at h
  exact Array.toList_inj.mp (bytes_list_inj h)

theorem branchFits_ssz {b : Array ByteArray} {n : Nat} (hf : BranchFits b n) :
    _root_.Ssz.Fits (branchDesc n) (branchValue b) := by
  refine .vector (by simp [hf.1]) ?_
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  exact .byteVector (by simpa using hf.2 r (Array.mem_toList_iff.mp hr))

theorem BeaconBlockHeader.toValue_inj {a b : BeaconBlockHeader}
    (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at h
  obtain ⟨rfl, rfl, h1, h2, h3⟩ := h
  rw [ByteArray.ext h1, ByteArray.ext h2, ByteArray.ext h3]

theorem BeaconBlockHeader.toValue_fits {h : BeaconBlockHeader} (hf : h.Fits) :
    _root_.Ssz.Fits beaconBlockHeaderDesc h.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨.uint hf.slot, .uint hf.proposerIndex, .byteVector (by simpa using hf.parentRoot),
    .byteVector (by simpa using hf.stateRoot), .byteVector (by simpa using hf.bodyRoot)⟩

theorem SyncCommittee.toValue_inj {a b : SyncCommittee} (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.bytes.injEq, and_true] at h
  rw [Array.toList_inj.mp (bytes_list_inj h.1), ByteArray.ext h.2]

theorem SyncCommittee.toValue_fits {c : SyncCommittee} (hf : c.Fits) :
    _root_.Ssz.Fits syncCommitteeDesc c.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  refine ⟨.vector (by simp [hf.count]) ?_, .byteVector (by simpa using hf.aggregate)⟩
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
  exact .byteVector (by simpa using hf.keys k (Array.mem_toList_iff.mp hk))

theorem SyncAggregate.toValue_inj {a b : SyncAggregate} (ha : a.Fits) (hb : b.Fits)
    (h : a.toValue = b.toValue) : a = b := by
  obtain ⟨h1, _⟩ := ha; obtain ⟨h2, _⟩ := hb
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.bits.injEq, Value.bytes.injEq,
    and_true] at h h1 h2
  rw [unpackBits_512_inj h1 h2 h.1, ByteArray.ext h.2]

theorem SyncAggregate.toValue_fits {a : SyncAggregate} (hf : a.Fits) :
    _root_.Ssz.Fits syncAggregateDesc a.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨.bitVector (by simp [unpackBits]), .byteVector (by simpa using hf.signature)⟩

theorem ExecutionPayloadHeader.toValue_inj {a b : ExecutionPayloadHeader}
    (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,
    and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, rfl, rfl, rfl, rfl, h11, rfl, h13, h14, h15, rfl, rfl⟩ := h
  rw [ByteArray.ext h1, ByteArray.ext h2, ByteArray.ext h3, ByteArray.ext h4, ByteArray.ext h5,
    ByteArray.ext h6, ByteArray.ext h11, ByteArray.ext h13, ByteArray.ext h14, ByteArray.ext h15]

theorem ExecutionPayloadHeader.toValue_fits {e : ExecutionPayloadHeader} (hf : e.Fits) :
    _root_.Ssz.Fits executionPayloadHeaderDesc e.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨.byteVector (by simpa using hf.parentHash),
    .byteVector (by simpa using hf.feeRecipient),
    .byteVector (by simpa using hf.stateRoot),
    .byteVector (by simpa using hf.receiptsRoot),
    .byteVector (by simpa using hf.logsBloom),
    .byteVector (by simpa using hf.prevRandao),
    .uint hf.blockNumber, .uint hf.gasLimit, .uint hf.gasUsed, .uint hf.timestamp,
    .byteList (by simpa using hf.extraData), .uint hf.baseFeePerGas,
    .byteVector (by simpa using hf.blockHash),
    .byteVector (by simpa using hf.transactionsRoot),
    .byteVector (by simpa using hf.withdrawalsRoot),
    .uint hf.blobGasUsed, .uint hf.excessBlobGas⟩

theorem Electra.Header.toValue_inj {a b : Electra.Header} (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, and_true] at h
  rw [BeaconBlockHeader.toValue_inj h.1, ExecutionPayloadHeader.toValue_inj h.2.1,
    branchValue_inj h.2.2]

theorem Electra.Header.toValue_fits {h : Electra.Header} (hf : h.Fits) :
    _root_.Ssz.Fits electraHeaderDesc h.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨BeaconBlockHeader.toValue_fits hf.beacon,
    ExecutionPayloadHeader.toValue_fits hf.execution, branchFits_ssz hf.executionBranch⟩

theorem Electra.Bootstrap.toValue_inj {a b : Electra.Bootstrap}
    (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, and_true] at h
  rw [Electra.Header.toValue_inj h.1, SyncCommittee.toValue_inj h.2.1, branchValue_inj h.2.2]

theorem Electra.Bootstrap.toValue_fits {b : Electra.Bootstrap} (hf : b.Fits) :
    _root_.Ssz.Fits electraBootstrapDesc b.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Electra.Header.toValue_fits hf.header, SyncCommittee.toValue_fits hf.committee,
    branchFits_ssz hf.branch⟩

theorem Electra.Update.toValue_inj {a b : Electra.Update} (ha : a.Fits) (hb : b.Fits)
    (h : a.toValue = b.toValue) : a = b := by
  have h1 := ha.aggregate; have h2 := hb.aggregate
  cases a; cases b
  dsimp only at h1 h2
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at h
  obtain ⟨ha1, hc, hcb, hf, hfb, hagg, rfl⟩ := h
  rw [Electra.Header.toValue_inj ha1, SyncCommittee.toValue_inj hc, branchValue_inj hcb,
    Electra.Header.toValue_inj hf, branchValue_inj hfb, SyncAggregate.toValue_inj h1 h2 hagg]

theorem Electra.Update.toValue_fits {u : Electra.Update} (hf : u.Fits) :
    _root_.Ssz.Fits electraUpdateDesc u.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Electra.Header.toValue_fits hf.attested, SyncCommittee.toValue_fits hf.committee,
    branchFits_ssz hf.committeeBranch, Electra.Header.toValue_fits hf.finalized,
    branchFits_ssz hf.finalityBranch, SyncAggregate.toValue_fits hf.aggregate,
    .uint hf.signatureSlot⟩

theorem Electra.FinalityUpdate.toValue_inj {a b : Electra.FinalityUpdate}
    (ha : a.Fits) (hb : b.Fits) (h : a.toValue = b.toValue) : a = b := by
  have h1 := ha.aggregate; have h2 := hb.aggregate
  cases a; cases b
  dsimp only at h1 h2
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at h
  obtain ⟨ha1, hf, hfb, hagg, rfl⟩ := h
  rw [Electra.Header.toValue_inj ha1, Electra.Header.toValue_inj hf, branchValue_inj hfb,
    SyncAggregate.toValue_inj h1 h2 hagg]

theorem Electra.FinalityUpdate.toValue_fits {u : Electra.FinalityUpdate} (hf : u.Fits) :
    _root_.Ssz.Fits electraFinalityUpdateDesc u.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Electra.Header.toValue_fits hf.attested, Electra.Header.toValue_fits hf.finalized,
    branchFits_ssz hf.finalityBranch, SyncAggregate.toValue_fits hf.aggregate,
    .uint hf.signatureSlot⟩

theorem Electra.OptimisticUpdate.toValue_inj {a b : Electra.OptimisticUpdate}
    (ha : a.Fits) (hb : b.Fits) (h : a.toValue = b.toValue) : a = b := by
  have h1 := ha.aggregate; have h2 := hb.aggregate
  cases a; cases b
  dsimp only at h1 h2
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at h
  obtain ⟨ha1, hagg, rfl⟩ := h
  rw [Electra.Header.toValue_inj ha1, SyncAggregate.toValue_inj h1 h2 hagg]

theorem Electra.OptimisticUpdate.toValue_fits {u : Electra.OptimisticUpdate} (hf : u.Fits) :
    _root_.Ssz.Fits electraOptimisticUpdateDesc u.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Electra.Header.toValue_fits hf.attested, SyncAggregate.toValue_fits hf.aggregate,
    .uint hf.signatureSlot⟩

theorem Gloas.Header.toValue_inj {a b : Gloas.Header} (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.bytes.injEq, and_true] at h
  rw [BeaconBlockHeader.toValue_inj h.1, ByteArray.ext h.2.1, branchValue_inj h.2.2]

theorem Gloas.Header.toValue_fits {h : Gloas.Header} (hf : h.Fits) :
    _root_.Ssz.Fits gloasHeaderDesc h.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨BeaconBlockHeader.toValue_fits hf.beacon,
    .byteVector (by simpa using hf.executionBlockHash), branchFits_ssz hf.executionBranch⟩

theorem Gloas.Bootstrap.toValue_inj {a b : Gloas.Bootstrap}
    (h : a.toValue = b.toValue) : a = b := by
  cases a; cases b
  simp only [toValue, Value.seq.injEq, List.cons.injEq, and_true] at h
  rw [Gloas.Header.toValue_inj h.1, SyncCommittee.toValue_inj h.2.1, branchValue_inj h.2.2]

theorem Gloas.Bootstrap.toValue_fits {b : Gloas.Bootstrap} (hf : b.Fits) :
    _root_.Ssz.Fits gloasBootstrapDesc b.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Gloas.Header.toValue_fits hf.header, SyncCommittee.toValue_fits hf.committee,
    branchFits_ssz hf.branch⟩

theorem Gloas.Update.toValue_inj {a b : Gloas.Update} (ha : a.Fits) (hb : b.Fits)
    (h : a.toValue = b.toValue) : a = b := by
  have h1 := ha.aggregate; have h2 := hb.aggregate
  cases a; cases b
  dsimp only at h1 h2
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at h
  obtain ⟨ha1, hc, hcb, hf, hfb, hagg, rfl⟩ := h
  rw [Gloas.Header.toValue_inj ha1, SyncCommittee.toValue_inj hc, branchValue_inj hcb,
    Gloas.Header.toValue_inj hf, branchValue_inj hfb, SyncAggregate.toValue_inj h1 h2 hagg]

theorem Gloas.Update.toValue_fits {u : Gloas.Update} (hf : u.Fits) :
    _root_.Ssz.Fits gloasUpdateDesc u.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Gloas.Header.toValue_fits hf.attested, SyncCommittee.toValue_fits hf.committee,
    branchFits_ssz hf.committeeBranch, Gloas.Header.toValue_fits hf.finalized,
    branchFits_ssz hf.finalityBranch, SyncAggregate.toValue_fits hf.aggregate,
    .uint hf.signatureSlot⟩

theorem Gloas.FinalityUpdate.toValue_inj {a b : Gloas.FinalityUpdate}
    (ha : a.Fits) (hb : b.Fits) (h : a.toValue = b.toValue) : a = b := by
  have h1 := ha.aggregate; have h2 := hb.aggregate
  cases a; cases b
  dsimp only at h1 h2
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at h
  obtain ⟨ha1, hf, hfb, hagg, rfl⟩ := h
  rw [Gloas.Header.toValue_inj ha1, Gloas.Header.toValue_inj hf, branchValue_inj hfb,
    SyncAggregate.toValue_inj h1 h2 hagg]

theorem Gloas.FinalityUpdate.toValue_fits {u : Gloas.FinalityUpdate} (hf : u.Fits) :
    _root_.Ssz.Fits gloasFinalityUpdateDesc u.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Gloas.Header.toValue_fits hf.attested, Gloas.Header.toValue_fits hf.finalized,
    branchFits_ssz hf.finalityBranch, SyncAggregate.toValue_fits hf.aggregate,
    .uint hf.signatureSlot⟩

theorem Gloas.OptimisticUpdate.toValue_inj {a b : Gloas.OptimisticUpdate}
    (ha : a.Fits) (hb : b.Fits) (h : a.toValue = b.toValue) : a = b := by
  have h1 := ha.aggregate; have h2 := hb.aggregate
  cases a; cases b
  dsimp only at h1 h2
  simp only [toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, and_true] at h
  obtain ⟨ha1, hagg, rfl⟩ := h
  rw [Gloas.Header.toValue_inj ha1, SyncAggregate.toValue_inj h1 h2 hagg]

theorem Gloas.OptimisticUpdate.toValue_fits {u : Gloas.OptimisticUpdate} (hf : u.Fits) :
    _root_.Ssz.Fits gloasOptimisticUpdateDesc u.toValue := by
  refine .container rfl ?_
  simp only [List.zip, List.zipWith, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨Gloas.Header.toValue_fits hf.attested, SyncAggregate.toValue_fits hf.aggregate,
    .uint hf.signatureSlot⟩

/-! ## Well-formedness of every container's `Desc` -/

theorem beaconBlockHeaderDesc_wellFormed : beaconBlockHeaderDesc.wellFormed = .ok () := rfl
theorem syncCommitteeDesc_wellFormed : syncCommitteeDesc.wellFormed = .ok () := rfl
theorem syncAggregateDesc_wellFormed : syncAggregateDesc.wellFormed = .ok () := rfl
theorem executionPayloadHeaderDesc_wellFormed :
    executionPayloadHeaderDesc.wellFormed = .ok () := rfl
theorem electraHeaderDesc_wellFormed : electraHeaderDesc.wellFormed = .ok () := rfl
theorem electraBootstrapDesc_wellFormed : electraBootstrapDesc.wellFormed = .ok () := rfl
theorem electraUpdateDesc_wellFormed : electraUpdateDesc.wellFormed = .ok () := rfl
theorem electraFinalityUpdateDesc_wellFormed :
    electraFinalityUpdateDesc.wellFormed = .ok () := rfl
theorem electraOptimisticUpdateDesc_wellFormed :
    electraOptimisticUpdateDesc.wellFormed = .ok () := rfl
theorem gloasHeaderDesc_wellFormed : gloasHeaderDesc.wellFormed = .ok () := rfl
theorem gloasBootstrapDesc_wellFormed : gloasBootstrapDesc.wellFormed = .ok () := rfl
theorem gloasUpdateDesc_wellFormed : gloasUpdateDesc.wellFormed = .ok () := rfl
theorem gloasFinalityUpdateDesc_wellFormed :
    gloasFinalityUpdateDesc.wellFormed = .ok () := rfl
theorem gloasOptimisticUpdateDesc_wellFormed :
    gloasOptimisticUpdateDesc.wellFormed = .ok () := rfl

/-! ## Struct slot and slice lemmas -/

theorem pow_offset_bound_eq : 2 ^ (8 * bytesPerOffset) = 4294967296 := by
  show 2 ^ 32 = 4294967296; omega

theorem nat_lt_pow_offset {n : Nat} (h : n < 4294967296) :
    n < 2 ^ (8 * bytesPerOffset) := by
  rwa [pow_offset_bound_eq]

theorem readSlots_nil (data : Bytes) (pos : Nat) : readSlots [] data pos = .ok ([], pos) := rfl

theorem deserializeFields_nil : deserializeFields [] [] = .ok [] := by
  rw [deserializeFields]

theorem deserializeFields_cons_ok {f : Desc} {fs : List Desc} {p : Bytes} {ps : List Bytes}
    {v : Value} {vs : List Value}
    (hf : deserialize f p = .ok v) (hfs : deserializeFields fs ps = .ok vs) :
    deserializeFields (f :: fs) (p :: ps) = .ok (v :: vs) := by
  rw [deserializeFields]
  simp only [hf, hfs, Bind.bind, Except.bind, pure, Except.pure]

theorem bodyStarts_nil : bodyStarts [] = [] := rfl
theorem bodyStarts_inline (b : Bytes) (s : List Slot) :
    bodyStarts (.inline b :: s) = bodyStarts s := rfl
theorem bodyStarts_body (o : Nat) (s : List Slot) :
    bodyStarts (.body o :: s) = o :: bodyStarts s := rfl
theorem slotHeld_inline (b : Bytes) : Slot.held (.inline b) = b := rfl

theorem fieldsFixedSize_nil : Desc.fieldsFixedSize [] = some 0 := rfl
theorem fieldsFixedSize_cons_some {f : Desc} {fs : List Desc} {w₁ w₂ w : Nat}
    (hf : f.fixedSize = some w₁) (hfs : Desc.fieldsFixedSize fs = some w₂) (hw : w₁ + w₂ = w) :
    Desc.fieldsFixedSize (f :: fs) = some w := by
  simp [Desc.fieldsFixedSize, hf, hfs, hw]
theorem fieldsFixedSize_cons_none_left {f : Desc} {fs : List Desc} (hf : f.fixedSize = none) :
    Desc.fieldsFixedSize (f :: fs) = none := by
  simp [Desc.fieldsFixedSize, hf]
theorem fieldsFixedSize_cons_none_right {f : Desc} {fs : List Desc} {w : Nat}
    (hf : f.fixedSize = some w) (hfs : Desc.fieldsFixedSize fs = none) :
    Desc.fieldsFixedSize (f :: fs) = none := by
  simp [Desc.fieldsFixedSize, hf, hfs]

theorem readSlots_fixed_cons {f : Desc} {fs : List Desc} {w : Nat}
    (hf : f.fixedSize = some w) {data : Bytes} {pos : Nat} (h : pos + w ≤ data.size) :
    readSlots (f :: fs) data pos = do
      let (rest, ending) ← readSlots fs data (pos + w)
      return (.inline (data.extract pos (pos + w)) :: rest, ending) := by
  simp only [readSlots, hf, show ¬ pos + w > data.size by omega, ite_false]

theorem readSlots_var_cons {f : Desc} {fs : List Desc}
    (hf : f.fixedSize = none) {data : Bytes} {pos : Nat} (h : pos + 4 ≤ data.size) :
    readSlots (f :: fs) data pos = do
      let (rest, ending) ← readSlots fs data (pos + 4)
      return (.body (readUint data pos 4) :: rest, ending) := by
  simp only [readSlots, hf, bytesPerOffset, show ¬ pos + 4 > data.size by omega, ite_false]

theorem structSlices_of_fixed_eq {fs : List Desc} {w : Nat} {data : Bytes} {slots : List Slot}
    (hfw : Desc.fieldsFixedSize fs = some w)
    (hw : w < 2 ^ (8 * bytesPerOffset))
    (hsz : data.size = w)
    (hr : readSlots fs data 0 = .ok (slots, w))
    (hb : bodyStarts slots = []) :
    structSlices fs data = .ok (slots.map Slot.held) := by
  have hov : ¬ data.size ≥ 2 ^ (8 * bytesPerOffset) := fun h => Nat.not_lt.mpr h (hsz ▸ hw)
  have hne : (data.size != w) = false := bne_eq_false_iff_eq.mpr hsz
  rw [structSlices, ite_eq_right hov]
  simp only [Bind.bind, Except.bind, pure, Except.pure, structBudget, hfw, hne,
    hr, hb, List.isEmpty_nil, Bool.false_eq_true, ite_false, ite_true]

theorem deserialize_container_fixed_reject {names : List String} {fs : List Desc} {w : Nat}
    {bs : ByteArray} (hfw : Desc.fieldsFixedSize fs = some w) (hne : bs.size ≠ w) :
    (deserialize (.container names fs) bs.data).isOk = false := by
  by_cases hov : 2 ^ (8 * bytesPerOffset) ≤ bs.size
  · have hov' : bs.data.size ≥ 2 ^ (8 * bytesPerOffset) := hov
    rw [deserialize, structSlices, ite_eq_left hov']
    rfl
  · have hov' : ¬ bs.data.size ≥ 2 ^ (8 * bytesPerOffset) := hov
    have hne' : (bs.data.size != w) = true := bne_iff_ne.mpr hne
    rw [deserialize, structSlices, ite_eq_right hov']
    simp only [Bind.bind, Except.bind, structBudget, hfw, hne', ite_true,
      Except.isOk, Except.toBool]

theorem deserialize_container_ok_of_slices {names : List String} {fs : List Desc}
    {data : Bytes} {parts : List Bytes} {vs : List Value}
    (hs : structSlices fs data = .ok parts)
    (hdf : deserializeFields fs parts = .ok vs) :
    ∀ v, deserialize (.container names fs) data = .ok v ↔ v = .seq vs := by
  intro v
  rw [deserialize, hs]
  change (do let vs ← deserializeFields fs parts; pure (Value.seq vs)) = .ok v ↔ v = .seq vs
  rw [hdf]
  change Except.ok (Value.seq vs) = Except.ok v ↔ v = .seq vs
  exact ⟨fun h => (Except.ok.inj h).symm, fun h => h ▸ rfl⟩

theorem deserialize_container_fixed {names : List String} {fs : List Desc} {w : Nat}
    {bs : ByteArray} {slots : List Slot} {parts : List Bytes} {vs : List Value}
    (hfw : Desc.fieldsFixedSize fs = some w)
    (hw : w < 2 ^ (8 * bytesPerOffset))
    (hr : bs.size = w → readSlots fs bs.data 0 = .ok (slots, w))
    (hb : bs.size = w → bodyStarts slots = [])
    (hp : bs.size = w → slots.map Slot.held = parts)
    (hdf : bs.size = w → deserializeFields fs parts = .ok vs) :
    (∀ v, deserialize (.container names fs) bs.data = .ok v ↔ bs.size = w ∧ v = .seq vs) ∧
      (bs.size ≠ w → (deserialize (.container names fs) bs.data).isOk = false) := by
  refine ⟨fun v => ?_, fun hne => deserialize_container_fixed_reject hfw hne⟩
  by_cases hsz : bs.size = w
  · have hs : structSlices fs bs.data = .ok parts := by
      rw [← hp hsz]
      exact structSlices_of_fixed_eq hfw hw hsz (hr hsz) (hb hsz)
    have hok := deserialize_container_ok_of_slices (names := names) hs (hdf hsz) v
    exact ⟨fun h => ⟨hsz, hok.mp h⟩, fun ⟨_, hv⟩ => hok.mpr hv⟩
  · have hrej := deserialize_container_fixed_reject (names := names) hfw hsz
    refine ⟨fun h => ?_, fun ⟨h, _⟩ => absurd h hsz⟩
    rw [h] at hrej
    cases hrej

theorem structSlices_of_var1 {fs : List Desc} {lead : Nat} {data : Bytes}
    {slots : List Slot} {o₁ : Nat} {parts : List Bytes}
    (hfw : Desc.fieldsFixedSize fs = none)
    (hlw : Desc.leadingWidth fs = lead)
    (hov : data.size < 2 ^ (8 * bytesPerOffset))
    (hr : lead ≤ data.size → readSlots fs data 0 = .ok (slots, lead))
    (hb : lead ≤ data.size → bodyStarts slots = [o₁])
    (ht : lead ≤ data.size → o₁ = lead → takeSlots data slots [data.size - o₁] = .ok parts) :
    (∀ ps, structSlices fs data = .ok ps ↔ (lead ≤ data.size ∧ o₁ = lead) ∧ ps = parts) ∧
      (¬ (lead ≤ data.size ∧ o₁ = lead) → (structSlices fs data).isOk = false) := by
  have hnov : ¬ data.size ≥ 2 ^ (8 * bytesPerOffset) := by omega
  refine ⟨fun ps => ?_, fun hbad => ?_⟩
  · by_cases hle : lead ≤ data.size
    · have hbud : structBudget fs data.size = .ok () := by
        simp [structBudget, hfw, hlw, show ¬ data.size < lead by omega]
      by_cases ho : o₁ = lead
      · have hsp : offsetSpans [lead] data.size = .ok [data.size - lead] := by
          simp [offsetSpans, show ¬ data.size < lead by omega]
        have ht' := ht hle ho
        rw [ho] at ht'
        simp [structSlices, hnov, hbud, hr hle, hb hle, ho, hle, hsp, ht',
          Bind.bind, Except.bind, eq_comm]
      · have hne : (o₁ != lead) = true := bne_iff_ne.mpr ho
        simp [structSlices, hnov, hbud, hr hle, hb hle, ho, hle, hne,
          _root_.Ssz.throw_error, Bind.bind, Except.bind]
    · have hbud : structBudget fs data.size = .error (.scopeTooSmall lead data.size) := by
        simp [structBudget, hfw, hlw, show data.size < lead by omega]
      simp [structSlices, hnov, hbud, hle, Bind.bind, Except.bind]
  · by_cases hle : lead ≤ data.size
    · have ho : o₁ ≠ lead := fun h => hbad ⟨hle, h⟩
      have hbud : structBudget fs data.size = .ok () := by
        simp [structBudget, hfw, hlw, show ¬ data.size < lead by omega]
      have hne : (o₁ != lead) = true := bne_iff_ne.mpr ho
      simp [structSlices, hnov, hbud, hr hle, hb hle, hne, _root_.Ssz.throw_error,
        Bind.bind, Except.bind, Except.isOk, Except.toBool]
    · have hbud : structBudget fs data.size = .error (.scopeTooSmall lead data.size) := by
        simp [structBudget, hfw, hlw, show data.size < lead by omega]
      simp [structSlices, hnov, hbud, Bind.bind, Except.bind, Except.isOk, Except.toBool]

theorem structSlices_of_var2 {fs : List Desc} {lead : Nat} {data : Bytes}
    {slots : List Slot} {o₁ o₂ : Nat} {parts : List Bytes}
    (hfw : Desc.fieldsFixedSize fs = none)
    (hlw : Desc.leadingWidth fs = lead)
    (hov : data.size < 2 ^ (8 * bytesPerOffset))
    (hr : lead ≤ data.size → readSlots fs data 0 = .ok (slots, lead))
    (hb : lead ≤ data.size → bodyStarts slots = [o₁, o₂])
    (ht : lead ≤ data.size → o₁ = lead → lead ≤ o₂ → o₂ ≤ data.size →
      takeSlots data slots [o₂ - o₁, data.size - o₂] = .ok parts) :
    (∀ ps, structSlices fs data = .ok ps ↔
      (lead ≤ data.size ∧ o₁ = lead ∧ lead ≤ o₂ ∧ o₂ ≤ data.size) ∧ ps = parts) ∧
      (¬ (lead ≤ data.size ∧ o₁ = lead ∧ lead ≤ o₂ ∧ o₂ ≤ data.size) →
        (structSlices fs data).isOk = false) := by
  have hnov : ¬ data.size ≥ 2 ^ (8 * bytesPerOffset) := by omega
  refine ⟨fun ps => ?_, fun hbad => ?_⟩
  · by_cases hle : lead ≤ data.size
    · have hbud : structBudget fs data.size = .ok () := by
        simp [structBudget, hfw, hlw, show ¬ data.size < lead by omega]
      by_cases ho1 : o₁ = lead
      · by_cases ho2 : lead ≤ o₂
        · by_cases ho3 : o₂ ≤ data.size
          · have hsp : offsetSpans [lead, o₂] data.size = .ok [o₂ - lead, data.size - o₂] := by
              simp [offsetSpans, show ¬ o₂ < lead by omega, show ¬ data.size < o₂ by omega,
                Bind.bind, Except.bind, pure, Except.pure]
            have ht' := ht hle ho1 ho2 ho3
            rw [ho1] at ht'
            simp [structSlices, hnov, hbud, hr hle, hb hle, ho1, hle, ho2, ho3, hsp, ht',
              Bind.bind, Except.bind, eq_comm]
          · have hsp : offsetSpans [lead, o₂] data.size = .error .offsetPastScope := by
              simp [offsetSpans, show ¬ o₂ < lead by omega, show data.size < o₂ by omega,
                Bind.bind, Except.bind]
            simp [structSlices, hnov, hbud, hr hle, hb hle, ho1, hle, ho2, ho3, hsp,
              Bind.bind, Except.bind]
        · have hsp : offsetSpans [lead, o₂] data.size = .error .offsetUnordered := by
            simp [offsetSpans, show o₂ < lead by omega]
          simp [structSlices, hnov, hbud, hr hle, hb hle, ho1, hle, ho2, hsp,
            Bind.bind, Except.bind]
      · have hne : (o₁ != lead) = true := bne_iff_ne.mpr ho1
        simp [structSlices, hnov, hbud, hr hle, hb hle, ho1, hle, hne,
          _root_.Ssz.throw_error, Bind.bind, Except.bind]
    · have hbud : structBudget fs data.size = .error (.scopeTooSmall lead data.size) := by
        simp [structBudget, hfw, hlw, show data.size < lead by omega]
      simp [structSlices, hnov, hbud, hle, Bind.bind, Except.bind]
  · by_cases hle : lead ≤ data.size
    · have hbud : structBudget fs data.size = .ok () := by
        simp [structBudget, hfw, hlw, show ¬ data.size < lead by omega]
      by_cases ho1 : o₁ = lead
      · by_cases ho2 : lead ≤ o₂
        · have ho3 : ¬ o₂ ≤ data.size := fun h => hbad ⟨hle, ho1, ho2, h⟩
          have hsp : offsetSpans [lead, o₂] data.size = .error .offsetPastScope := by
            simp [offsetSpans, show ¬ o₂ < lead by omega, show data.size < o₂ by omega,
              Bind.bind, Except.bind]
          simp [structSlices, hnov, hbud, hr hle, hb hle, ho1, hsp,
            Bind.bind, Except.bind, Except.isOk, Except.toBool]
        · have hsp : offsetSpans [lead, o₂] data.size = .error .offsetUnordered := by
            simp [offsetSpans, show o₂ < lead by omega]
          simp [structSlices, hnov, hbud, hr hle, hb hle, ho1, hsp,
            Bind.bind, Except.bind, Except.isOk, Except.toBool]
      · have hne : (o₁ != lead) = true := bne_iff_ne.mpr ho1
        simp [structSlices, hnov, hbud, hr hle, hb hle, hne, _root_.Ssz.throw_error,
          Bind.bind, Except.bind, Except.isOk, Except.toBool]
    · have hbud : structBudget fs data.size = .error (.scopeTooSmall lead data.size) := by
        simp [structBudget, hfw, hlw, show data.size < lead by omega]
      simp [structSlices, hnov, hbud, Bind.bind, Except.bind, Except.isOk, Except.toBool]

/-! ## Generic decoder correspondence, canonicality, non-malleability, and round trip -/

theorem decode_canonical_of_iff {α : Type} {desc : Desc} {decode : ByteArray → Option α}
    {toValue : α → Value} (hwf : desc.wellFormed = .ok ())
    (hiff : ∀ bs x, decode bs = some x ↔ deserialize desc bs.data = .ok (toValue x))
    {bs : ByteArray} {x : α} (hd : decode bs = some x) :
    serialize desc (toValue x) = .ok bs.data :=
  _root_.Ssz.serialize_of_deserialize desc hwf bs.data (toValue x) ((hiff bs x).mp hd)

theorem decode_injective_bytes_of_iff {α : Type} {desc : Desc} {decode : ByteArray → Option α}
    {toValue : α → Value} (hwf : desc.wellFormed = .ok ())
    (hiff : ∀ bs x, decode bs = some x ↔ deserialize desc bs.data = .ok (toValue x))
    {bs₁ bs₂ : ByteArray} {x : α} (h₁ : decode bs₁ = some x) (h₂ : decode bs₂ = some x) :
    bs₁ = bs₂ :=
  ByteArray.ext (_root_.Ssz.deserialize_injective hwf ((hiff bs₁ x).mp h₁) ((hiff bs₂ x).mp h₂))

theorem decode_serialize_of_iff {α : Type} {desc : Desc} {decode : ByteArray → Option α}
    {toValue : α → Value} (hwf : desc.wellFormed = .ok ())
    (hisSome : ∀ bs, (decode bs).isSome = (deserialize desc bs.data).isOk)
    (hiff : ∀ bs x, decode bs = some x ↔ deserialize desc bs.data = .ok (toValue x))
    (hinj : ∀ bs x y, decode bs = some y → toValue x = toValue y → x = y)
    {x : α} {data : Bytes} (hs : serialize desc (toValue x) = .ok data) :
    decode ⟨data⟩ = some x := by
  have hd : deserialize desc (⟨data⟩ : ByteArray).data = .ok (toValue x) :=
    _root_.Ssz.roundTrip_of_encoding hwf hs
  have hok : (decode ⟨data⟩).isSome = true := by
    rw [hisSome ⟨data⟩, hd]; rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hok
  have hval : toValue x = toValue y :=
    Except.ok.inj (hd.symm.trans ((hiff ⟨data⟩ y).mp hy))
  exact hinj ⟨data⟩ x y hy hval ▸ hy

theorem decode_canonical_of_iff_fits {α : Type} {desc : Desc} {decode : ByteArray → Option α}
    {toValue : α → Value} {Fits : α → Prop} (hwf : desc.wellFormed = .ok ())
    (hiff : ∀ bs x, decode bs = some x ↔ deserialize desc bs.data = .ok (toValue x) ∧ Fits x)
    {bs : ByteArray} {x : α} (hd : decode bs = some x) :
    serialize desc (toValue x) = .ok bs.data :=
  _root_.Ssz.serialize_of_deserialize desc hwf bs.data (toValue x) ((hiff bs x).mp hd).1

theorem decode_injective_bytes_of_iff_fits {α : Type} {desc : Desc} {decode : ByteArray → Option α}
    {toValue : α → Value} {Fits : α → Prop} (hwf : desc.wellFormed = .ok ())
    (hiff : ∀ bs x, decode bs = some x ↔ deserialize desc bs.data = .ok (toValue x) ∧ Fits x)
    {bs₁ bs₂ : ByteArray} {x : α} (h₁ : decode bs₁ = some x) (h₂ : decode bs₂ = some x) :
    bs₁ = bs₂ :=
  ByteArray.ext (_root_.Ssz.deserialize_injective hwf
    ((hiff bs₁ x).mp h₁).1 ((hiff bs₂ x).mp h₂).1)

theorem decode_serialize_of_iff_fits {α : Type} {desc : Desc} {decode : ByteArray → Option α}
    {toValue : α → Value} {Fits : α → Prop} (hwf : desc.wellFormed = .ok ())
    (hisSome : ∀ bs, (decode bs).isSome = (deserialize desc bs.data).isOk)
    (hiff : ∀ bs x, decode bs = some x ↔ deserialize desc bs.data = .ok (toValue x) ∧ Fits x)
    (hinj : ∀ x y, Fits x → Fits y → toValue x = toValue y → x = y)
    {x : α} {data : Bytes} (hx : Fits x) (hs : serialize desc (toValue x) = .ok data) :
    decode ⟨data⟩ = some x := by
  have hd : deserialize desc (⟨data⟩ : ByteArray).data = .ok (toValue x) :=
    _root_.Ssz.roundTrip_of_encoding hwf hs
  have hok : (decode ⟨data⟩).isSome = true := by
    rw [hisSome ⟨data⟩, hd]; rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hok
  have ⟨hdy, hfy⟩ := (hiff ⟨data⟩ y).mp hy
  exact hinj x y hx hfy (Except.ok.inj (hd.symm.trans hdy)) ▸ hy

/-! ## `BeaconBlockHeader`, `SyncCommittee`, `SyncAggregate` -/

theorem BeaconBlockHeader.decode_iff (bs : ByteArray) (x : BeaconBlockHeader) :
    decode bs = some x ↔ deserialize beaconBlockHeaderDesc bs.data = .ok x.toValue := by
  have hslots : bs.size = 112 →
      readSlots [.uint 8, .uint 8, bytes32, bytes32, bytes32] bs.data 0 =
        .ok ([.inline (bs.data.extract 0 8), .inline (bs.data.extract 8 16),
          .inline (bs.data.extract 16 48), .inline (bs.data.extract 48 80),
          .inline (bs.data.extract 80 112)], 112) := fun hsz => by
    have : bs.data.size = 112 := by simpa using hsz
    rw [readSlots_fixed_cons rfl (by omega), readSlots_fixed_cons rfl (by omega),
      readSlots_fixed_cons rfl (by omega), readSlots_fixed_cons rfl (by omega),
      readSlots_fixed_cons rfl (by omega)]
    rfl
  have hdf : bs.size = 112 →
      deserializeFields [.uint 8, .uint 8, bytes32, bytes32, bytes32]
        [bs.data.extract 0 8, bs.data.extract 8 16, bs.data.extract 16 48,
          bs.data.extract 48 80, bs.data.extract 80 112] =
        .ok [.uint (u64 bs 0), .uint (u64 bs 8), .bytes (slice bs 16 32).data,
          .bytes (slice bs 48 32).data, .bytes (slice bs 80 32).data] := fun hsz => by
    simp only [deserializeFields, bytes32,
      deserialize_uint_slice bs 0 8 (by omega),
      deserialize_uint_slice bs 8 8 (by omega),
      deserialize_byteVector_slice bs 16 32 (by decide) (by omega),
      deserialize_byteVector_slice bs 48 32 (by decide) (by omega),
      deserialize_byteVector_slice bs 80 32 (by decide) (by omega),
      u64, Bind.bind, Except.bind, pure, Except.pure]
  have hfix := (deserialize_container_fixed
    (names := ["slot", "proposer_index", "parent_root", "state_root", "body_root"])
    (bs := bs) rfl (by decide) hslots (fun _ => rfl) (fun _ => rfl) hdf).1 x.toValue
  rw [beaconBlockHeaderDesc, hfix]
  unfold decode size
  by_cases hsz : bs.size = 112
  · simp only [hsz, ite_true, Option.some.injEq, true_and]
    exact ⟨fun h => h ▸ rfl, fun h => toValue_inj h.symm⟩
  · simp [hsz]

theorem BeaconBlockHeader.deserialize_slice (bs : ByteArray) (off : Nat) (h : off + 112 ≤ bs.size) :
    deserialize beaconBlockHeaderDesc (bs.data.extract off (off + 112)) =
      .ok (BeaconBlockHeader.read (slice bs off 112)).toValue := by
  rw [← slice_data_of_le bs off 112 h]
  exact (decode_iff (slice bs off 112) (read (slice bs off 112))).mp
    (by simp [decode, size, slice_size bs off 112 h])

theorem BeaconBlockHeader.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize beaconBlockHeaderDesc bs.data).isOk := by
  by_cases hsz : bs.size = 112
  · have hd : decode bs = some (read bs) := by simp [decode, size, hsz]
    rw [hd, (decode_iff bs (read bs)).mp hd]; rfl
  · have hd : decode bs = none := by simp [decode, size, hsz]
    have hslots : bs.size = 112 → readSlots [.uint 8, .uint 8, bytes32, bytes32, bytes32] bs.data 0 =
        .ok ([], 112) := fun h => absurd h hsz
    have hdf : bs.size = 112 → deserializeFields [.uint 8, .uint 8, bytes32, bytes32, bytes32] [] =
        .ok [] := fun h => absurd h hsz
    have herr := (deserialize_container_fixed
      (names := ["slot", "proposer_index", "parent_root", "state_root", "body_root"])
      (bs := bs) rfl (by decide) hslots (fun _ => rfl) (fun _ => rfl) hdf).2 hsz
    rw [hd, beaconBlockHeaderDesc, herr]; rfl

theorem BeaconBlockHeader.decode_canonical {bs : ByteArray} {h : BeaconBlockHeader}
    (hd : decode bs = some h) : serialize beaconBlockHeaderDesc h.toValue = .ok bs.data :=
  decode_canonical_of_iff beaconBlockHeaderDesc_wellFormed decode_iff hd

theorem BeaconBlockHeader.decode_injective_bytes {bs₁ bs₂ : ByteArray} {h : BeaconBlockHeader}
    (h₁ : decode bs₁ = some h) (h₂ : decode bs₂ = some h) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff beaconBlockHeaderDesc_wellFormed decode_iff h₁ h₂

theorem BeaconBlockHeader.decode_serialize {h : BeaconBlockHeader} {data : Bytes}
    (hs : serialize beaconBlockHeaderDesc h.toValue = .ok data) : decode ⟨data⟩ = some h :=
  decode_serialize_of_iff beaconBlockHeaderDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

theorem nat_lt_of_ble {a b : Nat} (h : Nat.ble a.succ b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem SyncCommittee.pubkeys_fixedSize :
    (Desc.vector (.byteVector 48) 512).fixedSize = some (48 * syncCommitteeSize) := rfl
theorem SyncCommittee.fieldsFixedSize_eq :
    Desc.fieldsFixedSize [.vector (.byteVector 48) 512, .byteVector 48] = some SyncCommittee.size :=
  rfl
theorem SyncCommittee.size_lt_offset : SyncCommittee.size < 2 ^ (8 * bytesPerOffset) :=
  nat_lt_of_ble rfl
theorem SyncCommittee.pubkeys_lt_offset : 48 * syncCommitteeSize < 2 ^ (8 * bytesPerOffset) :=
  nat_lt_of_ble rfl
theorem lt_offset_48 : 48 < 2 ^ (8 * bytesPerOffset) := nat_lt_of_ble rfl
theorem lt_offset_32 : 32 < 2 ^ (8 * bytesPerOffset) := nat_lt_of_ble rfl

theorem SyncCommittee.read_eq_mk {bs : ByteArray} {pub : Array ByteArray} {agg : ByteArray}
    (hp : fields bs 0 48 syncCommitteeSize = pub)
    (ha : slice bs (48 * syncCommitteeSize) 48 = agg) :
    SyncCommittee.read bs = { pubkeys := pub, aggregatePubkey := agg } := by
  rw [read, hp, ha]

theorem SyncCommittee.readSlots_ok (bs : ByteArray) :
    bs.size = SyncCommittee.size →
      readSlots [.vector (.byteVector 48) 512, .byteVector 48] bs.data 0 =
        .ok ([.inline (bs.data.extract 0 (48 * syncCommitteeSize)),
          .inline (bs.data.extract (48 * syncCommitteeSize) SyncCommittee.size)],
          SyncCommittee.size) :=
  fun hsz => by
    have hbs : bs.data.size = SyncCommittee.size := hsz
    have hw1 : 0 + 48 * syncCommitteeSize ≤ bs.data.size := by
      rw [hbs]; exact Nat.le_of_ble_eq_true rfl
    have hw2 : 48 * syncCommitteeSize + 48 ≤ bs.data.size := by
      rw [hbs]; exact Nat.le_refl _
    rw [readSlots_fixed_cons pubkeys_fixedSize hw1, Nat.zero_add,
      readSlots_fixed_cons (w := 48) rfl hw2,
      readSlots_nil]
    rfl

theorem SyncCommittee.deserializeFields_ok (bs : ByteArray) (pub : Array ByteArray)
    (hpub : fields bs 0 48 syncCommitteeSize = pub) :
    bs.size = SyncCommittee.size →
      deserializeFields [.vector (.byteVector 48) 512, .byteVector 48]
        [bs.data.extract 0 (48 * syncCommitteeSize),
          bs.data.extract (48 * syncCommitteeSize) SyncCommittee.size] =
        .ok [.seq (pub.toList.map fun k => .bytes k.data),
          .bytes (slice bs (48 * syncCommitteeSize) 48).data] := fun hsz => by
  have hv : deserialize (.vector (.byteVector 48) 512) (bs.data.extract 0 (48 * syncCommitteeSize)) =
      .ok (.seq (pub.toList.map fun k => .bytes k.data)) := by
    have hle : 0 + 48 * syncCommitteeSize ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := deserialize_vector_byteVector_slice bs 0 48 syncCommitteeSize
      pubkeys_lt_offset lt_offset_48 hle
    rw [Nat.zero_add, hpub] at h
    exact h
  have hb : deserialize (.byteVector 48)
      (bs.data.extract (48 * syncCommitteeSize) SyncCommittee.size) =
      .ok (.bytes (slice bs (48 * syncCommitteeSize) 48).data) := by
    have hle : 48 * syncCommitteeSize + 48 ≤ bs.size := by
      rw [hsz]; exact Nat.le_refl _
    exact deserialize_byteVector_slice bs (48 * syncCommitteeSize) 48 lt_offset_48 hle
  exact deserializeFields_cons_ok hv (deserializeFields_cons_ok hb deserializeFields_nil)

theorem SyncCommittee.decode_eq_some {bs : ByteArray} {pub : Array ByteArray}
    (hsz : bs.size = SyncCommittee.size)
    (hp : fields bs 0 48 syncCommitteeSize = pub) :
    SyncCommittee.decode bs = some { pubkeys := pub, aggregatePubkey := slice bs (48 * syncCommitteeSize) 48 } := by
  unfold decode
  split
  · exact congrArg some (read_eq_mk hp rfl)
  · rename_i hne; exact absurd hsz hne

theorem SyncCommittee.decode_eq_none {bs : ByteArray} (hsz : bs.size ≠ SyncCommittee.size) :
    SyncCommittee.decode bs = none := by
  unfold decode
  split
  · rename_i heq; exact absurd heq hsz
  · rfl

theorem SyncCommittee.deserialize_iff_aux (bs : ByteArray) (v : Value) (pub : Array ByteArray)
    (agg : ByteArray) (s1 s2 : Bytes)
    (hpub : fields bs 0 48 syncCommitteeSize = pub)
    (hagg : slice bs (48 * syncCommitteeSize) 48 = agg)
    (hs1 : bs.data.extract 0 (48 * syncCommitteeSize) = s1)
    (hs2 : bs.data.extract (48 * syncCommitteeSize) SyncCommittee.size = s2) :
    (deserialize (.container ["pubkeys", "aggregate_pubkey"]
        [.vector (.byteVector 48) 512, .byteVector 48]) bs.data = .ok v) ↔
      bs.size = SyncCommittee.size ∧
        v = .seq [.seq (pub.toList.map fun k => .bytes k.data), .bytes agg.data] := by
  have hslots : bs.size = SyncCommittee.size →
      readSlots [.vector (.byteVector 48) 512, .byteVector 48] bs.data 0 =
        .ok ([.inline s1, .inline s2], SyncCommittee.size) := fun hsz => by
    rw [← hs1, ← hs2]; exact readSlots_ok bs hsz
  have hdf : bs.size = SyncCommittee.size →
      deserializeFields [.vector (.byteVector 48) 512, .byteVector 48] [s1, s2] =
        .ok [.seq (pub.toList.map fun k => .bytes k.data), .bytes agg.data] := fun hsz => by
    rw [← hs1, ← hs2, ← hagg]; exact deserializeFields_ok bs pub hpub hsz
  exact (deserialize_container_fixed (names := ["pubkeys", "aggregate_pubkey"])
    (bs := bs) fieldsFixedSize_eq size_lt_offset hslots
    (fun _ => rfl) (fun _ => rfl) hdf).1 v

theorem SyncCommittee.decode_iff_core (bs : ByteArray) (x : SyncCommittee) (pub : Array ByteArray)
    (agg : ByteArray) (s1 s2 : Bytes)
    (hpub : fields bs 0 48 syncCommitteeSize = pub)
    (hagg : slice bs (48 * syncCommitteeSize) 48 = agg)
    (hs1 : bs.data.extract 0 (48 * syncCommitteeSize) = s1)
    (hs2 : bs.data.extract (48 * syncCommitteeSize) SyncCommittee.size = s2) :
    decode bs = some x ↔ deserialize syncCommitteeDesc bs.data = .ok x.toValue := by
  rw [syncCommitteeDesc, deserialize_iff_aux bs x.toValue pub agg s1 s2 hpub hagg hs1 hs2]
  by_cases hsz : bs.size = SyncCommittee.size
  · have hd : decode bs = some { pubkeys := pub, aggregatePubkey := agg } := by
      rw [← hagg]; exact decode_eq_some hsz hpub
    rw [hd]
    let c₀ : SyncCommittee := { pubkeys := pub, aggregatePubkey := agg }
    have htv : c₀.toValue = .seq [.seq (pub.toList.map fun k => .bytes k.data), .bytes agg.data] := rfl
    rw [← htv]
    refine ⟨fun h => ?_, fun ⟨_, h⟩ => congrArg some (toValue_inj h.symm)⟩
    injection h with h'
    exact ⟨hsz, h' ▸ rfl⟩
  · rw [decode_eq_none hsz]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact absurd h hsz

theorem SyncCommittee.decode_iff (bs : ByteArray) (x : SyncCommittee) :
    decode bs = some x ↔ deserialize syncCommitteeDesc bs.data = .ok x.toValue :=
  decode_iff_core bs x _ _ _ _ rfl rfl rfl rfl

theorem SyncCommittee.deserialize_slice (bs : ByteArray) (off : Nat)
    (h : off + SyncCommittee.size ≤ bs.size) :
    deserialize syncCommitteeDesc (bs.data.extract off (off + SyncCommittee.size)) =
      .ok (SyncCommittee.read (slice bs off SyncCommittee.size)).toValue := by
  rw [← slice_data_of_le bs off SyncCommittee.size h]
  generalize hr : read (slice bs off SyncCommittee.size) = c₀
  refine (decode_iff (slice bs off SyncCommittee.size) c₀).mp ?_
  unfold decode
  split
  · exact congrArg some hr
  · rename_i hne; exact absurd (slice_size bs off SyncCommittee.size h) hne

theorem SyncCommittee.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize syncCommitteeDesc bs.data).isOk := by
  by_cases hsz : bs.size = SyncCommittee.size
  · generalize hr : read bs = c₀
    have hd : decode bs = some c₀ := by
      unfold decode
      split
      · exact congrArg some hr
      · rename_i hne; exact absurd hsz hne
    rw [hd, (decode_iff bs c₀).mp hd]; rfl
  · have hd : decode bs = none := by
      unfold decode
      split
      · rename_i heq; exact absurd heq hsz
      · rfl
    rw [hd, syncCommitteeDesc, deserialize_container_fixed_reject fieldsFixedSize_eq hsz]; rfl

theorem SyncCommittee.decode_canonical {bs : ByteArray} {c : SyncCommittee}
    (hd : decode bs = some c) : serialize syncCommitteeDesc c.toValue = .ok bs.data :=
  decode_canonical_of_iff syncCommitteeDesc_wellFormed decode_iff hd

theorem SyncCommittee.decode_injective_bytes {bs₁ bs₂ : ByteArray} {c : SyncCommittee}
    (h₁ : decode bs₁ = some c) (h₂ : decode bs₂ = some c) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff syncCommitteeDesc_wellFormed decode_iff h₁ h₂

theorem SyncCommittee.decode_serialize {c : SyncCommittee} {data : Bytes}
    (hs : serialize syncCommitteeDesc c.toValue = .ok data) : decode ⟨data⟩ = some c :=
  decode_serialize_of_iff syncCommitteeDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

theorem SyncAggregate.decode_iff (bs : ByteArray) (x : SyncAggregate) :
    decode bs = some x ↔ deserialize syncAggregateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  have hslots : bs.size = 160 →
      readSlots [.bitVector 512, .byteVector 96] bs.data 0 =
        .ok ([.inline (bs.data.extract 0 64), .inline (bs.data.extract 64 160)], 160) :=
    fun hsz => by
      have : bs.data.size = 160 := by simpa using hsz
      rw [readSlots_fixed_cons rfl (by omega), readSlots_fixed_cons rfl (by omega)]
      rfl
  have hdf : bs.size = 160 →
      deserializeFields [.bitVector 512, .byteVector 96]
        [bs.data.extract 0 64, bs.data.extract 64 160] =
        .ok [.bits (unpackBits (slice bs 0 64).data 512), .bytes (slice bs 64 96).data] :=
    fun hsz => by
      have hv := deserialize_bitVector_512_slice bs 0 (by omega)
      have hb := deserialize_byteVector_slice bs 64 96 (by decide) (by omega)
      simp only [Nat.zero_add] at hv
      simp only [deserializeFields, hv, hb, Bind.bind, Except.bind, pure, Except.pure]
  have hfix := (deserialize_container_fixed
    (names := ["sync_committee_bits", "sync_committee_signature"])
    (bs := bs) rfl (by decide) hslots (fun _ => rfl) (fun _ => rfl) hdf).1 x.toValue
  rw [syncAggregateDesc, hfix]
  by_cases hsz : bs.size = 160
  · have hd : decode bs = some (read bs) := by simp [decode, size, syncCommitteeSize, hsz]
    rw [hd]
    simp only [hsz, Option.some.injEq, true_and]
    refine ⟨fun h => ⟨h ▸ rfl, h ▸ read_fits bs (by omega)⟩, fun ⟨hv, hfx⟩ => ?_⟩
    exact toValue_inj (read_fits bs (by omega)) hfx hv.symm
  · have hd : decode bs = none := by simp [decode, size, syncCommitteeSize, hsz]
    simp [hd, hsz]

theorem SyncAggregate.deserialize_eq_of_fits (bs : ByteArray) {x : SyncAggregate} (hx : x.Fits) :
    (decode bs = some x ↔ deserialize syncAggregateDesc bs.data = .ok x.toValue) := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem SyncAggregate.deserialize_slice (bs : ByteArray) (off : Nat) (h : off + 160 ≤ bs.size) :
    deserialize syncAggregateDesc (bs.data.extract off (off + 160)) =
      .ok (SyncAggregate.read (slice bs off 160)).toValue := by
  rw [← slice_data_of_le bs off 160 h]
  exact ((decode_iff (slice bs off 160) (read (slice bs off 160))).mp
    (by simp [decode, size, syncCommitteeSize, slice_size bs off 160 h])).1

theorem SyncAggregate.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize syncAggregateDesc bs.data).isOk := by
  by_cases hsz : bs.size = 160
  · have hd : decode bs = some (read bs) := by simp [decode, size, syncCommitteeSize, hsz]
    rw [hd, ((decode_iff bs (read bs)).mp hd).1]; rfl
  · have hd : decode bs = none := by simp [decode, size, syncCommitteeSize, hsz]
    have hslots : bs.size = 160 →
        readSlots [.bitVector 512, .byteVector 96] bs.data 0 = .ok ([], 160) :=
      fun h => absurd h hsz
    have hdf : bs.size = 160 →
        deserializeFields [.bitVector 512, .byteVector 96] [] = .ok [] :=
      fun h => absurd h hsz
    have herr := (deserialize_container_fixed
      (names := ["sync_committee_bits", "sync_committee_signature"])
      (bs := bs) rfl (by decide) hslots (fun _ => rfl) (fun _ => rfl) hdf).2 hsz
    rw [hd, syncAggregateDesc, herr]; rfl

theorem SyncAggregate.decode_canonical {bs : ByteArray} {a : SyncAggregate}
    (hd : decode bs = some a) : serialize syncAggregateDesc a.toValue = .ok bs.data :=
  _root_.Ssz.serialize_of_deserialize syncAggregateDesc syncAggregateDesc_wellFormed
    bs.data a.toValue ((decode_iff bs a).mp hd).1

theorem SyncAggregate.decode_injective_bytes {bs₁ bs₂ : ByteArray} {a : SyncAggregate}
    (h₁ : decode bs₁ = some a) (h₂ : decode bs₂ = some a) : bs₁ = bs₂ :=
  ByteArray.ext (_root_.Ssz.deserialize_injective syncAggregateDesc_wellFormed
    ((decode_iff bs₁ a).mp h₁).1 ((decode_iff bs₂ a).mp h₂).1)

theorem SyncAggregate.decode_serialize {a : SyncAggregate} (ha : a.Fits) {data : Bytes}
    (hs : serialize syncAggregateDesc a.toValue = .ok data) : decode ⟨data⟩ = some a := by
  have hd : deserialize syncAggregateDesc (⟨data⟩ : ByteArray).data = .ok a.toValue :=
    _root_.Ssz.roundTrip_of_encoding syncAggregateDesc_wellFormed hs
  exact (decode_iff ⟨data⟩ a).mpr ⟨hd, ha⟩

/-! ## Gloas fixed-size containers -/

theorem Gloas.Header.decode_iff (bs : ByteArray) (x : Gloas.Header) :
    decode bs = some x ↔ deserialize gloasHeaderDesc bs.data = .ok x.toValue := by
  let w₁ : Nat := BeaconBlockHeader.size
  let w₂ : Nat := w₁ + 32
  let w : Nat := w₂ + 32 * Gloas.executionBranchLength
  have hbh : beaconBlockHeaderDesc.fixedSize = some w₁ := by
    simp [Desc.fixedSize, beaconBlockHeaderDesc, Desc.fieldsFixedSize, bytes32,
      w₁, BeaconBlockHeader.size]
  have hbr : (branchDesc Gloas.executionBranchLength).fixedSize =
      some (32 * Gloas.executionBranchLength) := by
    simp [Desc.fixedSize, branchDesc, bytes32]
  have hfw : Desc.fieldsFixedSize
      [beaconBlockHeaderDesc, bytes32, branchDesc Gloas.executionBranchLength] = some w :=
    fieldsFixedSize_cons_some hbh
      (fieldsFixedSize_cons_some (f := bytes32) (w₁ := 32) rfl
        (fieldsFixedSize_cons_some hbr fieldsFixedSize_nil (Nat.add_zero _)) rfl)
      (by omega)
  have hw_lt : w < 2 ^ (8 * bytesPerOffset) := by
    show 112 + 32 + 32 * 11 < 2 ^ 32; omega
  have hslots : bs.size = w →
      readSlots [beaconBlockHeaderDesc, bytes32, branchDesc Gloas.executionBranchLength] bs.data 0 =
        .ok ([.inline (bs.data.extract 0 w₁), .inline (bs.data.extract w₁ w₂),
          .inline (bs.data.extract w₂ w)], w) := fun hsz => by
    have hbs : bs.data.size = 112 + 32 + 32 * 11 := by
      simpa [w, w₁, w₂, BeaconBlockHeader.size, Gloas.executionBranchLength] using hsz
    rw [readSlots_fixed_cons hbh (by show 0 + 112 ≤ bs.data.size; omega), Nat.zero_add,
      readSlots_fixed_cons (w := 32) rfl (by show 112 + 32 ≤ bs.data.size; omega),
      readSlots_fixed_cons hbr (by show 112 + 32 + 32 * 11 ≤ bs.data.size; omega),
      readSlots_nil]
    rfl
  let v₁ : Value := (BeaconBlockHeader.read (slice bs 0 w₁)).toValue
  let v₂ : Value := .bytes (slice bs w₁ 32).data
  let v₃ : Value := branchValue (roots bs w₂ Gloas.executionBranchLength)
  have hdf : bs.size = w →
      deserializeFields [beaconBlockHeaderDesc, bytes32, branchDesc Gloas.executionBranchLength]
        [bs.data.extract 0 w₁, bs.data.extract w₁ w₂, bs.data.extract w₂ w] =
        .ok [v₁, v₂, v₃] := fun hsz => by
    have : bs.size = 112 + 32 + 32 * 11 := hsz
    have h1 : deserialize beaconBlockHeaderDesc (bs.data.extract 0 w₁) = .ok v₁ := by
      have h := BeaconBlockHeader.deserialize_slice bs 0 (by omega)
      rw [Nat.zero_add] at h
      exact h
    have h2 : deserialize bytes32 (bs.data.extract w₁ w₂) = .ok v₂ :=
      deserialize_byteVector_slice bs w₁ 32 (by show 32 < 2 ^ 32; omega)
        (by show 112 + 32 ≤ bs.size; omega)
    have h3 : deserialize (branchDesc Gloas.executionBranchLength) (bs.data.extract w₂ w) = .ok v₃ :=
      deserialize_branch_slice bs w₂ Gloas.executionBranchLength
        (by show 32 * 11 < 2 ^ 32; omega) (by show 112 + 32 + 32 * 11 ≤ bs.size; omega)
    exact deserializeFields_cons_ok h1 (deserializeFields_cons_ok h2
      (deserializeFields_cons_ok h3 deserializeFields_nil))
  have hfix := (deserialize_container_fixed
    (names := ["beacon", "execution_block_hash", "execution_branch"])
    (bs := bs) hfw hw_lt hslots
    (fun _ => by rw [bodyStarts_inline, bodyStarts_inline, bodyStarts_inline, bodyStarts_nil])
    (fun _ => by simp only [List.map_cons, List.map_nil, slotHeld_inline]) hdf).1 x.toValue
  rw [gloasHeaderDesc, hfix]
  by_cases hsz : bs.size = w
  · have hd : decode bs = some (read bs) := by
      rw [decode, show Gloas.Header.size = w from rfl, ite_eq_left hsz]
    rw [hd]
    have htv : (read bs).toValue = .seq [v₁, v₂, v₃] := rfl
    rw [← htv]
    refine ⟨fun h => ?_, fun ⟨_, h⟩ => congrArg some (toValue_inj h.symm)⟩
    injection h with h'
    exact ⟨hsz, h' ▸ rfl⟩
  · have hd : decode bs = none := by
      rw [decode, show Gloas.Header.size = w from rfl, ite_eq_right hsz]
    rw [hd]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact absurd h hsz

theorem Gloas.Header.deserialize_slice (bs : ByteArray) (off : Nat)
    (h : off + Gloas.Header.size ≤ bs.size) :
    deserialize gloasHeaderDesc (bs.data.extract off (off + Gloas.Header.size)) =
      .ok (Gloas.Header.read (slice bs off Gloas.Header.size)).toValue := by
  rw [← slice_data_of_le bs off Gloas.Header.size h]
  exact (decode_iff (slice bs off Gloas.Header.size) (read (slice bs off Gloas.Header.size))).mp
    (by rw [decode, ite_eq_left (slice_size bs off Gloas.Header.size h)])

theorem Gloas.Header.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize gloasHeaderDesc bs.data).isOk := by
  by_cases hsz : bs.size = Gloas.Header.size
  · have hd : decode bs = some (read bs) := by rw [decode, ite_eq_left hsz]
    rw [hd, (decode_iff bs (read bs)).mp hd]; rfl
  · have hd : decode bs = none := by rw [decode, ite_eq_right hsz]
    have hfw : Desc.fieldsFixedSize
        [beaconBlockHeaderDesc, bytes32, branchDesc Gloas.executionBranchLength] =
        some Gloas.Header.size := by
      simp [Desc.fieldsFixedSize, Desc.fixedSize, beaconBlockHeaderDesc, bytes32, branchDesc,
        size, BeaconBlockHeader.size, Gloas.executionBranchLength]
    rw [hd, gloasHeaderDesc, deserialize_container_fixed_reject hfw hsz]; rfl

theorem Gloas.Header.decode_canonical {bs : ByteArray} {h : Gloas.Header}
    (hd : decode bs = some h) : serialize gloasHeaderDesc h.toValue = .ok bs.data :=
  decode_canonical_of_iff gloasHeaderDesc_wellFormed decode_iff hd

theorem Gloas.Header.decode_injective_bytes {bs₁ bs₂ : ByteArray} {h : Gloas.Header}
    (h₁ : decode bs₁ = some h) (h₂ : decode bs₂ = some h) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff gloasHeaderDesc_wellFormed decode_iff h₁ h₂

theorem Gloas.Header.decode_serialize {h : Gloas.Header} {data : Bytes}
    (hs : serialize gloasHeaderDesc h.toValue = .ok data) : decode ⟨data⟩ = some h :=
  decode_serialize_of_iff gloasHeaderDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

theorem Gloas.Bootstrap.decode_eq_some {bs : ByteArray} {hdr : Gloas.Header}
    {sc : SyncCommittee} {br : Array ByteArray}
    (hsz : bs.size = Gloas.Bootstrap.size)
    (hh : Header.read (slice bs 0 Header.size) = hdr)
    (hsc : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc)
    (hbr : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = br) :
    Gloas.Bootstrap.decode bs = some {
      header := hdr, currentSyncCommittee := sc, currentSyncCommitteeBranch := br } := by
  unfold decode
  split
  · rw [hh, hsc, hbr]
  · rename_i hne; exact absurd hsz hne

theorem Gloas.Bootstrap.decode_eq_none {bs : ByteArray} (hsz : bs.size ≠ Gloas.Bootstrap.size) :
    Gloas.Bootstrap.decode bs = none := by
  unfold decode
  split
  · rename_i heq; exact absurd heq hsz
  · rfl

theorem Gloas.Bootstrap.size_eq : Gloas.Bootstrap.size = 25472 := rfl
theorem Gloas.Bootstrap.fieldsFixedSize_eq :
    Desc.fieldsFixedSize
      [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength] =
      some Gloas.Bootstrap.size := rfl
theorem Gloas.Bootstrap.size_lt_offset : Gloas.Bootstrap.size < 2 ^ (8 * bytesPerOffset) :=
  nat_lt_of_ble rfl

theorem Gloas.Bootstrap.readSlots_ok (bs : ByteArray) (s1 s2 s3 : Bytes)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) Gloas.Bootstrap.size = s3) :
    bs.size = Gloas.Bootstrap.size →
      readSlots [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength]
        bs.data 0 = .ok ([.inline s1, .inline s2, .inline s3], Gloas.Bootstrap.size) := fun hsz => by
  have hbs : bs.data.size = Gloas.Bootstrap.size := hsz
  have hgh : gloasHeaderDesc.fixedSize = some Gloas.Header.size := rfl
  have hsc : syncCommitteeDesc.fixedSize = some SyncCommittee.size := rfl
  have hbr : (branchDesc Gloas.syncCommitteeBranchLength).fixedSize =
      some (32 * Gloas.syncCommitteeBranchLength) := rfl
  have hw1 : 0 + Gloas.Header.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw2 : Gloas.Header.size + SyncCommittee.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw3 : (Gloas.Header.size + SyncCommittee.size) + 32 * Gloas.syncCommitteeBranchLength ≤
      bs.data.size := by
    rw [hbs]; exact Nat.le_refl _
  rw [← hs1, ← hs2, ← hs3, readSlots_fixed_cons hgh hw1, Nat.zero_add,
    readSlots_fixed_cons hsc hw2,
    readSlots_fixed_cons hbr hw3,
    readSlots_nil]
  rfl

theorem Gloas.Bootstrap.deserializeFields_ok (bs : ByteArray) (s1 s2 s3 : Bytes)
    (hdr : Gloas.Header) (sc0 : SyncCommittee) (br0 : Array ByteArray)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) Gloas.Bootstrap.size = s3)
    (hhdr : Header.read (slice bs 0 Header.size) = hdr)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hbr0 : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = br0) :
    bs.size = Gloas.Bootstrap.size →
      deserializeFields
        [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength]
        [s1, s2, s3] = .ok [hdr.toValue, sc0.toValue, branchValue br0] := fun hsz => by
  have h1 : deserialize gloasHeaderDesc s1 = .ok hdr.toValue := by
    have hle : 0 + Gloas.Header.size ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := Header.deserialize_slice bs 0 hle
    rw [Nat.zero_add, hhdr, hs1] at h
    exact h
  have h2 : deserialize syncCommitteeDesc s2 = .ok sc0.toValue := by
    have hle : Gloas.Header.size + SyncCommittee.size ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := SyncCommittee.deserialize_slice bs Header.size hle
    rw [hsc0, hs2] at h
    exact h
  have h3 : deserialize (branchDesc Gloas.syncCommitteeBranchLength) s3 =
      .ok (branchValue br0) := by
    have hle : (Gloas.Header.size + SyncCommittee.size) + 32 * Gloas.syncCommitteeBranchLength ≤
        bs.size := by
      rw [hsz]; exact Nat.le_refl _
    have h := deserialize_branch_slice bs (Gloas.Header.size + SyncCommittee.size)
      Gloas.syncCommitteeBranchLength (nat_lt_of_ble rfl) hle
    change deserialize (branchDesc Gloas.syncCommitteeBranchLength)
      (bs.data.extract (Gloas.Header.size + SyncCommittee.size) Gloas.Bootstrap.size) =
      .ok (branchValue _) at h
    rw [hbr0, hs3] at h
    exact h
  exact deserializeFields_cons_ok h1 (deserializeFields_cons_ok h2
    (deserializeFields_cons_ok h3 deserializeFields_nil))

theorem Gloas.Bootstrap.deserialize_iff_aux (bs : ByteArray) (v : Value) (s1 s2 s3 : Bytes)
    (hdr : Gloas.Header) (sc0 : SyncCommittee) (br0 : Array ByteArray)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) Gloas.Bootstrap.size = s3)
    (hhdr : Header.read (slice bs 0 Header.size) = hdr)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hbr0 : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = br0) :
    (deserialize gloasBootstrapDesc bs.data = .ok v) ↔
      bs.size = Gloas.Bootstrap.size ∧ v = .seq [hdr.toValue, sc0.toValue, branchValue br0] :=
  (deserialize_container_fixed
    (names := ["header", "current_sync_committee", "current_sync_committee_branch"])
    (bs := bs) fieldsFixedSize_eq size_lt_offset
    (readSlots_ok bs s1 s2 s3 hs1 hs2 hs3)
    (fun _ => rfl) (fun _ => rfl)
    (deserializeFields_ok bs s1 s2 s3 hdr sc0 br0 hs1 hs2 hs3 hhdr hsc0 hbr0)).1 v

theorem Gloas.Bootstrap.decode_iff_core (bs : ByteArray) (x : Gloas.Bootstrap) (s1 s2 s3 : Bytes)
    (hdr : Gloas.Header) (sc0 : SyncCommittee) (br0 : Array ByteArray)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) Gloas.Bootstrap.size = s3)
    (hhdr : Header.read (slice bs 0 Header.size) = hdr)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hbr0 : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = br0) :
    decode bs = some x ↔ deserialize gloasBootstrapDesc bs.data = .ok x.toValue := by
  rw [deserialize_iff_aux bs x.toValue s1 s2 s3 hdr sc0 br0 hs1 hs2 hs3 hhdr hsc0 hbr0]
  by_cases hsz : bs.size = Gloas.Bootstrap.size
  · let b₀ : Gloas.Bootstrap := {
      header := hdr, currentSyncCommittee := sc0, currentSyncCommitteeBranch := br0 }
    have hd : decode bs = some b₀ := decode_eq_some hsz hhdr hsc0 hbr0
    rw [hd]
    have htv : b₀.toValue = .seq [hdr.toValue, sc0.toValue, branchValue br0] := rfl
    rw [← htv]
    refine ⟨fun h => ?_, fun ⟨_, h⟩ => congrArg some (toValue_inj h.symm)⟩
    injection h with h'
    exact ⟨hsz, h' ▸ rfl⟩
  · rw [decode_eq_none hsz]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact absurd h hsz

theorem Gloas.Bootstrap.decode_iff (bs : ByteArray) (x : Gloas.Bootstrap) :
    decode bs = some x ↔ deserialize gloasBootstrapDesc bs.data = .ok x.toValue :=
  decode_iff_core bs x _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

theorem Gloas.Bootstrap.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize gloasBootstrapDesc bs.data).isOk := by
  by_cases hsz : bs.size = Gloas.Bootstrap.size
  · generalize hhdr : Header.read (slice bs 0 Header.size) = hdr
    generalize hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0
    generalize hbr0 : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = br0
    have hd := decode_eq_some hsz hhdr hsc0 hbr0
    rw [hd, (decode_iff bs _).mp hd]; rfl
  · rw [decode_eq_none hsz, gloasBootstrapDesc,
      deserialize_container_fixed_reject fieldsFixedSize_eq hsz]; rfl

theorem Gloas.Bootstrap.decode_canonical {bs : ByteArray} {b : Gloas.Bootstrap}
    (hd : decode bs = some b) : serialize gloasBootstrapDesc b.toValue = .ok bs.data :=
  decode_canonical_of_iff gloasBootstrapDesc_wellFormed decode_iff hd

theorem Gloas.Bootstrap.decode_injective_bytes {bs₁ bs₂ : ByteArray} {b : Gloas.Bootstrap}
    (h₁ : decode bs₁ = some b) (h₂ : decode bs₂ = some b) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff gloasBootstrapDesc_wellFormed decode_iff h₁ h₂

theorem Gloas.Bootstrap.decode_serialize {b : Gloas.Bootstrap} {data : Bytes}
    (hs : serialize gloasBootstrapDesc b.toValue = .ok data) : decode ⟨data⟩ = some b :=
  decode_serialize_of_iff gloasBootstrapDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

theorem Gloas.Update.fieldsFixedSize_eq :
    Desc.fieldsFixedSize
      [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength,
        gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc, .uint 8] =
      some Gloas.Update.size := rfl

theorem Gloas.Update.size_lt_offset : Gloas.Update.size < 2 ^ (8 * bytesPerOffset) :=
  nat_lt_of_ble rfl

theorem Gloas.Update.decode_eq_some {bs : ByteArray}
    {att : Gloas.Header} {sc0 : SyncCommittee} {cbr : Array ByteArray}
    {fin : Gloas.Header} {fbr : Array ByteArray} {agg : SyncAggregate} {sig : Nat}
    (hsz : bs.size = Gloas.Update.size)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hcbr : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = cbr)
    (hfin : Header.read (slice bs finalizedAt Header.size) = fin)
    (hfbr : roots bs (finalizedAt + Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    Gloas.Update.decode bs = some {
      attestedHeader := att, nextSyncCommittee := sc0, nextSyncCommitteeBranch := cbr,
      finalizedHeader := fin, finalityBranch := fbr, syncAggregate := agg,
      signatureSlot := sig } := by
  unfold decode
  split
  · rw [hatt, hsc0, hcbr, hfin, hfbr, hagg, hsig]
  · rename_i hne; exact absurd hsz hne

theorem Gloas.Update.decode_eq_none {bs : ByteArray} (hsz : bs.size ≠ Gloas.Update.size) :
    Gloas.Update.decode bs = none := by
  unfold decode
  split
  · rename_i heq; exact absurd heq hsz
  · rfl

theorem Gloas.Update.readSlots_ok (bs : ByteArray) (s1 s2 s3 s4 s5 s6 s7 : Bytes)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) finalizedAt = s3)
    (hs4 : bs.data.extract finalizedAt (finalizedAt + Gloas.Header.size) = s4)
    (hs5 : bs.data.extract (finalizedAt + Gloas.Header.size) aggregateAt = s5)
    (hs6 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.Update.size = s7) :
    bs.size = Gloas.Update.size →
      readSlots [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength,
        gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc, .uint 8]
        bs.data 0 = .ok ([.inline s1, .inline s2, .inline s3, .inline s4, .inline s5,
          .inline s6, .inline s7], Gloas.Update.size) := fun hsz => by
  have hbs : bs.data.size = Gloas.Update.size := hsz
  have hgh : gloasHeaderDesc.fixedSize = some Gloas.Header.size := rfl
  have hsc : syncCommitteeDesc.fixedSize = some SyncCommittee.size := rfl
  have hcbr : (branchDesc Gloas.syncCommitteeBranchLength).fixedSize =
      some (32 * Gloas.syncCommitteeBranchLength) := rfl
  have hfbr : (branchDesc Gloas.finalityBranchLength).fixedSize =
      some (32 * Gloas.finalityBranchLength) := rfl
  have hagg : syncAggregateDesc.fixedSize = some SyncAggregate.size := rfl
  have hw1 : 0 + Gloas.Header.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw2 : Gloas.Header.size + SyncCommittee.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw3 : (Gloas.Header.size + SyncCommittee.size) + 32 * Gloas.syncCommitteeBranchLength ≤
      bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw4 : finalizedAt + Gloas.Header.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw5 : (finalizedAt + Gloas.Header.size) + 32 * Gloas.finalityBranchLength ≤
      bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw6 : aggregateAt + SyncAggregate.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw7 : (aggregateAt + SyncAggregate.size) + 8 ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_refl _
  have he1 : Gloas.Header.size + SyncCommittee.size + 32 * Gloas.syncCommitteeBranchLength =
      finalizedAt := rfl
  have he2 : finalizedAt + Gloas.Header.size + 32 * Gloas.finalityBranchLength =
      aggregateAt := rfl
  rw [← hs1, ← hs2, ← hs3, ← hs4, ← hs5, ← hs6, ← hs7,
    readSlots_fixed_cons hgh hw1, Nat.zero_add,
    readSlots_fixed_cons hsc hw2,
    readSlots_fixed_cons hcbr hw3, he1,
    readSlots_fixed_cons hgh hw4,
    readSlots_fixed_cons hfbr hw5, he2,
    readSlots_fixed_cons hagg hw6,
    readSlots_fixed_cons (w := 8) rfl hw7,
    readSlots_nil]
  rfl

theorem Gloas.Update.deserializeFields_ok (bs : ByteArray) (s1 s2 s3 s4 s5 s6 s7 : Bytes)
    (att : Gloas.Header) (sc0 : SyncCommittee) (cbr : Array ByteArray)
    (fin : Gloas.Header) (fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) finalizedAt = s3)
    (hs4 : bs.data.extract finalizedAt (finalizedAt + Gloas.Header.size) = s4)
    (hs5 : bs.data.extract (finalizedAt + Gloas.Header.size) aggregateAt = s5)
    (hs6 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.Update.size = s7)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hcbr : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = cbr)
    (hfin : Header.read (slice bs finalizedAt Header.size) = fin)
    (hfbr : roots bs (finalizedAt + Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    bs.size = Gloas.Update.size →
      deserializeFields
        [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength,
          gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc, .uint 8]
        [s1, s2, s3, s4, s5, s6, s7] =
        .ok [att.toValue, sc0.toValue, branchValue cbr, fin.toValue, branchValue fbr,
          agg.toValue, .uint sig] := fun hsz => by
  have h1 : deserialize gloasHeaderDesc s1 = .ok att.toValue := by
    have hle : 0 + Gloas.Header.size ≤ bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := Header.deserialize_slice bs 0 hle
    rw [Nat.zero_add, hatt, hs1] at h; exact h
  have h2 : deserialize syncCommitteeDesc s2 = .ok sc0.toValue := by
    have hle : Gloas.Header.size + SyncCommittee.size ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := SyncCommittee.deserialize_slice bs Header.size hle
    rw [hsc0, hs2] at h; exact h
  have h3 : deserialize (branchDesc Gloas.syncCommitteeBranchLength) s3 = .ok (branchValue cbr) := by
    have hle : (Gloas.Header.size + SyncCommittee.size) + 32 * Gloas.syncCommitteeBranchLength ≤
        bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := deserialize_branch_slice bs (Gloas.Header.size + SyncCommittee.size)
      Gloas.syncCommitteeBranchLength (nat_lt_of_ble rfl) hle
    change deserialize (branchDesc Gloas.syncCommitteeBranchLength)
      (bs.data.extract (Gloas.Header.size + SyncCommittee.size) finalizedAt) =
      .ok (branchValue _) at h
    rw [hcbr, hs3] at h; exact h
  have h4 : deserialize gloasHeaderDesc s4 = .ok fin.toValue := by
    have hle : finalizedAt + Gloas.Header.size ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := Header.deserialize_slice bs finalizedAt hle
    rw [hfin, hs4] at h; exact h
  have h5 : deserialize (branchDesc Gloas.finalityBranchLength) s5 = .ok (branchValue fbr) := by
    have hle : (finalizedAt + Gloas.Header.size) + 32 * Gloas.finalityBranchLength ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := deserialize_branch_slice bs (finalizedAt + Gloas.Header.size)
      Gloas.finalityBranchLength (nat_lt_of_ble rfl) hle
    change deserialize (branchDesc Gloas.finalityBranchLength)
      (bs.data.extract (finalizedAt + Gloas.Header.size) aggregateAt) =
      .ok (branchValue _) at h
    rw [hfbr, hs5] at h; exact h
  have h6 : deserialize syncAggregateDesc s6 = .ok agg.toValue := by
    have hle : aggregateAt + 160 ≤ bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := SyncAggregate.deserialize_slice bs aggregateAt hle
    change deserialize syncAggregateDesc
      (bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size)) =
      .ok (SyncAggregate.read (slice bs aggregateAt SyncAggregate.size)).toValue at h
    rw [hagg, hs6] at h; exact h
  have h7 : deserialize (.uint 8) s7 = .ok (.uint sig) := by
    have hle : (aggregateAt + SyncAggregate.size) + 8 ≤ bs.size := by
      rw [hsz]; exact Nat.le_refl _
    have h := deserialize_uint_slice bs (aggregateAt + SyncAggregate.size) 8 hle
    change deserialize (.uint 8)
      (bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.Update.size) =
      .ok (.uint (u64 bs (aggregateAt + SyncAggregate.size))) at h
    rw [hsig, hs7] at h; exact h
  exact deserializeFields_cons_ok h1 (deserializeFields_cons_ok h2
    (deserializeFields_cons_ok h3 (deserializeFields_cons_ok h4
      (deserializeFields_cons_ok h5 (deserializeFields_cons_ok h6
        (deserializeFields_cons_ok h7 deserializeFields_nil))))))

theorem Gloas.Update.deserialize_iff_aux (bs : ByteArray) (v : Value) (s1 s2 s3 s4 s5 s6 s7 : Bytes)
    (att : Gloas.Header) (sc0 : SyncCommittee) (cbr : Array ByteArray)
    (fin : Gloas.Header) (fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) finalizedAt = s3)
    (hs4 : bs.data.extract finalizedAt (finalizedAt + Gloas.Header.size) = s4)
    (hs5 : bs.data.extract (finalizedAt + Gloas.Header.size) aggregateAt = s5)
    (hs6 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.Update.size = s7)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hcbr : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = cbr)
    (hfin : Header.read (slice bs finalizedAt Header.size) = fin)
    (hfbr : roots bs (finalizedAt + Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    (deserialize gloasUpdateDesc bs.data = .ok v) ↔
      bs.size = Gloas.Update.size ∧ v = .seq [att.toValue, sc0.toValue, branchValue cbr,
        fin.toValue, branchValue fbr, agg.toValue, .uint sig] :=
  (deserialize_container_fixed
    (names := ["attested_header", "next_sync_committee", "next_sync_committee_branch",
      "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"])
    (bs := bs) fieldsFixedSize_eq size_lt_offset
    (readSlots_ok bs s1 s2 s3 s4 s5 s6 s7 hs1 hs2 hs3 hs4 hs5 hs6 hs7)
    (fun _ => rfl) (fun _ => rfl)
    (deserializeFields_ok bs s1 s2 s3 s4 s5 s6 s7 att sc0 cbr fin fbr agg sig
      hs1 hs2 hs3 hs4 hs5 hs6 hs7 hatt hsc0 hcbr hfin hfbr hagg hsig)).1 v

theorem Gloas.Update.decode_iff_core (bs : ByteArray) (x : Gloas.Update)
    (s1 s2 s3 s4 s5 s6 s7 : Bytes)
    (att : Gloas.Header) (sc0 : SyncCommittee) (cbr : Array ByteArray)
    (fin : Gloas.Header) (fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncCommittee.size) finalizedAt = s3)
    (hs4 : bs.data.extract finalizedAt (finalizedAt + Gloas.Header.size) = s4)
    (hs5 : bs.data.extract (finalizedAt + Gloas.Header.size) aggregateAt = s5)
    (hs6 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.Update.size = s7)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0)
    (hcbr : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = cbr)
    (hfin : Header.read (slice bs finalizedAt Header.size) = fin)
    (hfbr : roots bs (finalizedAt + Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    decode bs = some x ↔ deserialize gloasUpdateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  rw [deserialize_iff_aux bs x.toValue s1 s2 s3 s4 s5 s6 s7 att sc0 cbr fin fbr agg sig
    hs1 hs2 hs3 hs4 hs5 hs6 hs7 hatt hsc0 hcbr hfin hfbr hagg hsig]
  by_cases hsz : bs.size = Gloas.Update.size
  · let u₀ : Gloas.Update := {
      attestedHeader := att, nextSyncCommittee := sc0, nextSyncCommitteeBranch := cbr,
      finalizedHeader := fin, finalityBranch := fbr, syncAggregate := agg,
      signatureSlot := sig }
    have hd : decode bs = some u₀ := decode_eq_some hsz hatt hsc0 hcbr hfin hfbr hagg hsig
    have hfu₀ : u₀.Fits := decode_fits hd
    rw [hd]
    have htv : u₀.toValue = .seq [att.toValue, sc0.toValue, branchValue cbr, fin.toValue,
      branchValue fbr, agg.toValue, .uint sig] := rfl
    rw [← htv]
    refine ⟨fun h => ?_, fun ⟨⟨_, hv⟩, hfx⟩ => congrArg some (toValue_inj hfu₀ hfx hv.symm)⟩
    injection h with h'
    exact ⟨⟨hsz, h' ▸ rfl⟩, h' ▸ hfu₀⟩
  · rw [decode_eq_none hsz]
    refine ⟨fun h => ?_, fun ⟨⟨h, _⟩, _⟩ => absurd h hsz⟩
    cases h

theorem Gloas.Update.decode_iff (bs : ByteArray) (x : Gloas.Update) :
    decode bs = some x ↔ deserialize gloasUpdateDesc bs.data = .ok x.toValue ∧ x.Fits :=
  decode_iff_core bs x _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl

theorem Gloas.Update.deserialize_eq_of_fits (bs : ByteArray) {x : Gloas.Update} (hx : x.Fits) :
    decode bs = some x ↔ deserialize gloasUpdateDesc bs.data = .ok x.toValue := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem Gloas.Update.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize gloasUpdateDesc bs.data).isOk := by
  by_cases hsz : bs.size = Gloas.Update.size
  · generalize hatt : Header.read (slice bs 0 Header.size) = att
    generalize hsc0 : SyncCommittee.read (slice bs Header.size SyncCommittee.size) = sc0
    generalize hcbr : roots bs (Header.size + SyncCommittee.size) Gloas.syncCommitteeBranchLength = cbr
    generalize hfin : Header.read (slice bs finalizedAt Header.size) = fin
    generalize hfbr : roots bs (finalizedAt + Header.size) Gloas.finalityBranchLength = fbr
    generalize hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg
    generalize hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig
    have hd := decode_eq_some hsz hatt hsc0 hcbr hfin hfbr hagg hsig
    rw [hd, ((decode_iff bs _).mp hd).1]; rfl
  · rw [decode_eq_none hsz, gloasUpdateDesc,
      deserialize_container_fixed_reject fieldsFixedSize_eq hsz]; rfl

theorem Gloas.Update.decode_canonical {bs : ByteArray} {u : Gloas.Update}
    (hd : decode bs = some u) : serialize gloasUpdateDesc u.toValue = .ok bs.data :=
  decode_canonical_of_iff_fits gloasUpdateDesc_wellFormed decode_iff hd

theorem Gloas.Update.decode_injective_bytes {bs₁ bs₂ : ByteArray} {u : Gloas.Update}
    (h₁ : decode bs₁ = some u) (h₂ : decode bs₂ = some u) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff_fits gloasUpdateDesc_wellFormed decode_iff h₁ h₂

theorem Gloas.Update.decode_serialize {u : Gloas.Update} {data : Bytes}
    (hu : u.Fits) (hs : serialize gloasUpdateDesc u.toValue = .ok data) : decode ⟨data⟩ = some u :=
  decode_serialize_of_iff_fits gloasUpdateDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ ha hb hv => toValue_inj ha hb hv) hu hs

theorem Gloas.FinalityUpdate.fieldsFixedSize_eq :
    Desc.fieldsFixedSize
      [gloasHeaderDesc, gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc,
        .uint 8] = some Gloas.FinalityUpdate.size := rfl

theorem Gloas.FinalityUpdate.size_lt_offset : Gloas.FinalityUpdate.size < 2 ^ (8 * bytesPerOffset) :=
  nat_lt_of_ble rfl

theorem Gloas.FinalityUpdate.decode_eq_some {bs : ByteArray}
    {att fin : Gloas.Header} {fbr : Array ByteArray} {agg : SyncAggregate} {sig : Nat}
    (hsz : bs.size = Gloas.FinalityUpdate.size)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hfin : Header.read (slice bs Header.size Header.size) = fin)
    (hfbr : roots bs (2 * Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    Gloas.FinalityUpdate.decode bs = some {
      attestedHeader := att, finalizedHeader := fin, finalityBranch := fbr,
      syncAggregate := agg, signatureSlot := sig } := by
  unfold decode
  split
  · rw [hatt, hfin, hfbr, hagg, hsig]
  · rename_i hne; exact absurd hsz hne

theorem Gloas.FinalityUpdate.decode_eq_none {bs : ByteArray}
    (hsz : bs.size ≠ Gloas.FinalityUpdate.size) :
    Gloas.FinalityUpdate.decode bs = none := by
  unfold decode
  split
  · rename_i heq; exact absurd heq hsz
  · rfl

theorem Gloas.FinalityUpdate.readSlots_ok (bs : ByteArray) (s1 s2 s3 s4 s5 : Bytes)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (2 * Gloas.Header.size) = s2)
    (hs3 : bs.data.extract (2 * Gloas.Header.size) aggregateAt = s3)
    (hs4 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s4)
    (hs5 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.FinalityUpdate.size = s5) :
    bs.size = Gloas.FinalityUpdate.size →
      readSlots [gloasHeaderDesc, gloasHeaderDesc, branchDesc Gloas.finalityBranchLength,
        syncAggregateDesc, .uint 8] bs.data 0 =
        .ok ([.inline s1, .inline s2, .inline s3, .inline s4, .inline s5],
          Gloas.FinalityUpdate.size) := fun hsz => by
  have hbs : bs.data.size = Gloas.FinalityUpdate.size := hsz
  have hgh : gloasHeaderDesc.fixedSize = some Gloas.Header.size := rfl
  have hfbr : (branchDesc Gloas.finalityBranchLength).fixedSize =
      some (32 * Gloas.finalityBranchLength) := rfl
  have hagg : syncAggregateDesc.fixedSize = some SyncAggregate.size := rfl
  have hw1 : 0 + Gloas.Header.size ≤ bs.data.size := by rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw2 : Gloas.Header.size + Gloas.Header.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw3 : 2 * Gloas.Header.size + 32 * Gloas.finalityBranchLength ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw4 : aggregateAt + SyncAggregate.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw5 : (aggregateAt + SyncAggregate.size) + 8 ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_refl _
  have h2h : Gloas.Header.size + Gloas.Header.size = 2 * Gloas.Header.size := rfl
  have he1 : 2 * Gloas.Header.size + 32 * Gloas.finalityBranchLength = aggregateAt := rfl
  rw [← hs1, ← hs2, ← hs3, ← hs4, ← hs5,
    readSlots_fixed_cons hgh hw1, Nat.zero_add,
    readSlots_fixed_cons hgh hw2, h2h,
    readSlots_fixed_cons hfbr hw3, he1,
    readSlots_fixed_cons hagg hw4,
    readSlots_fixed_cons (w := 8) rfl hw5,
    readSlots_nil]
  rfl

theorem Gloas.FinalityUpdate.deserializeFields_ok (bs : ByteArray) (s1 s2 s3 s4 s5 : Bytes)
    (att fin : Gloas.Header) (fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (2 * Gloas.Header.size) = s2)
    (hs3 : bs.data.extract (2 * Gloas.Header.size) aggregateAt = s3)
    (hs4 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s4)
    (hs5 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.FinalityUpdate.size = s5)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hfin : Header.read (slice bs Header.size Header.size) = fin)
    (hfbr : roots bs (2 * Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    bs.size = Gloas.FinalityUpdate.size →
      deserializeFields
        [gloasHeaderDesc, gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc,
          .uint 8]
        [s1, s2, s3, s4, s5] =
        .ok [att.toValue, fin.toValue, branchValue fbr, agg.toValue, .uint sig] := fun hsz => by
  have h1 : deserialize gloasHeaderDesc s1 = .ok att.toValue := by
    have hle : 0 + Gloas.Header.size ≤ bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := Header.deserialize_slice bs 0 hle
    rw [Nat.zero_add, hatt, hs1] at h; exact h
  have h2 : deserialize gloasHeaderDesc s2 = .ok fin.toValue := by
    have hle : Gloas.Header.size + Gloas.Header.size ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := Header.deserialize_slice bs Header.size hle
    change deserialize gloasHeaderDesc
      (bs.data.extract Gloas.Header.size (2 * Gloas.Header.size)) = _ at h
    rw [hfin, hs2] at h; exact h
  have h3 : deserialize (branchDesc Gloas.finalityBranchLength) s3 = .ok (branchValue fbr) := by
    have hle : 2 * Gloas.Header.size + 32 * Gloas.finalityBranchLength ≤ bs.size := by
      rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := deserialize_branch_slice bs (2 * Gloas.Header.size)
      Gloas.finalityBranchLength (nat_lt_of_ble rfl) hle
    change deserialize (branchDesc Gloas.finalityBranchLength)
      (bs.data.extract (2 * Gloas.Header.size) aggregateAt) = .ok (branchValue _) at h
    rw [hfbr, hs3] at h; exact h
  have h4 : deserialize syncAggregateDesc s4 = .ok agg.toValue := by
    have hle : aggregateAt + 160 ≤ bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := SyncAggregate.deserialize_slice bs aggregateAt hle
    change deserialize syncAggregateDesc
      (bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size)) =
      .ok (SyncAggregate.read (slice bs aggregateAt SyncAggregate.size)).toValue at h
    rw [hagg, hs4] at h; exact h
  have h5 : deserialize (.uint 8) s5 = .ok (.uint sig) := by
    have hle : (aggregateAt + SyncAggregate.size) + 8 ≤ bs.size := by rw [hsz]; exact Nat.le_refl _
    have h := deserialize_uint_slice bs (aggregateAt + SyncAggregate.size) 8 hle
    change deserialize (.uint 8)
      (bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.FinalityUpdate.size) =
      .ok (.uint (u64 bs (aggregateAt + SyncAggregate.size))) at h
    rw [hsig, hs5] at h; exact h
  exact deserializeFields_cons_ok h1 (deserializeFields_cons_ok h2
    (deserializeFields_cons_ok h3 (deserializeFields_cons_ok h4
      (deserializeFields_cons_ok h5 deserializeFields_nil))))

theorem Gloas.FinalityUpdate.deserialize_iff_aux (bs : ByteArray) (v : Value)
    (s1 s2 s3 s4 s5 : Bytes)
    (att fin : Gloas.Header) (fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (2 * Gloas.Header.size) = s2)
    (hs3 : bs.data.extract (2 * Gloas.Header.size) aggregateAt = s3)
    (hs4 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s4)
    (hs5 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.FinalityUpdate.size = s5)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hfin : Header.read (slice bs Header.size Header.size) = fin)
    (hfbr : roots bs (2 * Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    (deserialize gloasFinalityUpdateDesc bs.data = .ok v) ↔
      bs.size = Gloas.FinalityUpdate.size ∧
        v = .seq [att.toValue, fin.toValue, branchValue fbr, agg.toValue, .uint sig] :=
  (deserialize_container_fixed
    (names := ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
      "signature_slot"])
    (bs := bs) fieldsFixedSize_eq size_lt_offset
    (readSlots_ok bs s1 s2 s3 s4 s5 hs1 hs2 hs3 hs4 hs5)
    (fun _ => rfl) (fun _ => rfl)
    (deserializeFields_ok bs s1 s2 s3 s4 s5 att fin fbr agg sig
      hs1 hs2 hs3 hs4 hs5 hatt hfin hfbr hagg hsig)).1 v

theorem Gloas.FinalityUpdate.decode_iff_core (bs : ByteArray) (x : Gloas.FinalityUpdate)
    (s1 s2 s3 s4 s5 : Bytes)
    (att fin : Gloas.Header) (fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (2 * Gloas.Header.size) = s2)
    (hs3 : bs.data.extract (2 * Gloas.Header.size) aggregateAt = s3)
    (hs4 : bs.data.extract aggregateAt (aggregateAt + SyncAggregate.size) = s4)
    (hs5 : bs.data.extract (aggregateAt + SyncAggregate.size) Gloas.FinalityUpdate.size = s5)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hfin : Header.read (slice bs Header.size Header.size) = fin)
    (hfbr : roots bs (2 * Header.size) Gloas.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg)
    (hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig) :
    decode bs = some x ↔ deserialize gloasFinalityUpdateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  rw [deserialize_iff_aux bs x.toValue s1 s2 s3 s4 s5 att fin fbr agg sig
    hs1 hs2 hs3 hs4 hs5 hatt hfin hfbr hagg hsig]
  by_cases hsz : bs.size = Gloas.FinalityUpdate.size
  · let u₀ : Gloas.FinalityUpdate := {
      attestedHeader := att, finalizedHeader := fin, finalityBranch := fbr,
      syncAggregate := agg, signatureSlot := sig }
    have hd : decode bs = some u₀ := decode_eq_some hsz hatt hfin hfbr hagg hsig
    have hfu₀ : u₀.Fits := decode_fits hd
    rw [hd]
    have htv : u₀.toValue =
      .seq [att.toValue, fin.toValue, branchValue fbr, agg.toValue, .uint sig] := rfl
    rw [← htv]
    refine ⟨fun h => ?_, fun ⟨⟨_, hv⟩, hfx⟩ => congrArg some (toValue_inj hfu₀ hfx hv.symm)⟩
    injection h with h'
    exact ⟨⟨hsz, h' ▸ rfl⟩, h' ▸ hfu₀⟩
  · rw [decode_eq_none hsz]
    refine ⟨fun h => ?_, fun ⟨⟨h, _⟩, _⟩ => absurd h hsz⟩
    cases h

theorem Gloas.FinalityUpdate.decode_iff (bs : ByteArray) (x : Gloas.FinalityUpdate) :
    decode bs = some x ↔ deserialize gloasFinalityUpdateDesc bs.data = .ok x.toValue ∧ x.Fits :=
  decode_iff_core bs x _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem Gloas.FinalityUpdate.deserialize_eq_of_fits (bs : ByteArray) {x : Gloas.FinalityUpdate}
    (hx : x.Fits) :
    decode bs = some x ↔ deserialize gloasFinalityUpdateDesc bs.data = .ok x.toValue := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem Gloas.FinalityUpdate.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize gloasFinalityUpdateDesc bs.data).isOk := by
  by_cases hsz : bs.size = Gloas.FinalityUpdate.size
  · generalize hatt : Header.read (slice bs 0 Header.size) = att
    generalize hfin : Header.read (slice bs Header.size Header.size) = fin
    generalize hfbr : roots bs (2 * Header.size) Gloas.finalityBranchLength = fbr
    generalize hagg : SyncAggregate.read (slice bs aggregateAt SyncAggregate.size) = agg
    generalize hsig : u64 bs (aggregateAt + SyncAggregate.size) = sig
    have hd := decode_eq_some hsz hatt hfin hfbr hagg hsig
    rw [hd, ((decode_iff bs _).mp hd).1]; rfl
  · rw [decode_eq_none hsz, gloasFinalityUpdateDesc,
      deserialize_container_fixed_reject fieldsFixedSize_eq hsz]; rfl

theorem Gloas.FinalityUpdate.decode_canonical {bs : ByteArray} {u : Gloas.FinalityUpdate}
    (hd : decode bs = some u) : serialize gloasFinalityUpdateDesc u.toValue = .ok bs.data :=
  decode_canonical_of_iff_fits gloasFinalityUpdateDesc_wellFormed decode_iff hd

theorem Gloas.FinalityUpdate.decode_injective_bytes {bs₁ bs₂ : ByteArray}
    {u : Gloas.FinalityUpdate}
    (h₁ : decode bs₁ = some u) (h₂ : decode bs₂ = some u) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff_fits gloasFinalityUpdateDesc_wellFormed decode_iff h₁ h₂

theorem Gloas.FinalityUpdate.decode_serialize {u : Gloas.FinalityUpdate} {data : Bytes}
    (hu : u.Fits) (hs : serialize gloasFinalityUpdateDesc u.toValue = .ok data) :
    decode ⟨data⟩ = some u :=
  decode_serialize_of_iff_fits gloasFinalityUpdateDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ ha hb hv => toValue_inj ha hb hv) hu hs

theorem Gloas.OptimisticUpdate.fieldsFixedSize_eq :
    Desc.fieldsFixedSize [gloasHeaderDesc, syncAggregateDesc, .uint 8] =
      some Gloas.OptimisticUpdate.size := rfl

theorem Gloas.OptimisticUpdate.size_lt_offset :
    Gloas.OptimisticUpdate.size < 2 ^ (8 * bytesPerOffset) :=
  nat_lt_of_ble rfl

theorem Gloas.OptimisticUpdate.decode_eq_some {bs : ByteArray}
    {att : Gloas.Header} {agg : SyncAggregate} {sig : Nat}
    (hsz : bs.size = Gloas.OptimisticUpdate.size)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hagg : SyncAggregate.read (slice bs Header.size SyncAggregate.size) = agg)
    (hsig : u64 bs (Header.size + SyncAggregate.size) = sig) :
    Gloas.OptimisticUpdate.decode bs = some {
      attestedHeader := att, syncAggregate := agg, signatureSlot := sig } := by
  unfold decode
  split
  · rw [hatt, hagg, hsig]
  · rename_i hne; exact absurd hsz hne

theorem Gloas.OptimisticUpdate.decode_eq_none {bs : ByteArray}
    (hsz : bs.size ≠ Gloas.OptimisticUpdate.size) :
    Gloas.OptimisticUpdate.decode bs = none := by
  unfold decode
  split
  · rename_i heq; exact absurd heq hsz
  · rfl

theorem Gloas.OptimisticUpdate.readSlots_ok (bs : ByteArray) (s1 s2 s3 : Bytes)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncAggregate.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncAggregate.size)
      Gloas.OptimisticUpdate.size = s3) :
    bs.size = Gloas.OptimisticUpdate.size →
      readSlots [gloasHeaderDesc, syncAggregateDesc, .uint 8] bs.data 0 =
        .ok ([.inline s1, .inline s2, .inline s3], Gloas.OptimisticUpdate.size) := fun hsz => by
  have hbs : bs.data.size = Gloas.OptimisticUpdate.size := hsz
  have hgh : gloasHeaderDesc.fixedSize = some Gloas.Header.size := rfl
  have hagg : syncAggregateDesc.fixedSize = some SyncAggregate.size := rfl
  have hw1 : 0 + Gloas.Header.size ≤ bs.data.size := by rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw2 : Gloas.Header.size + SyncAggregate.size ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_of_ble_eq_true rfl
  have hw3 : (Gloas.Header.size + SyncAggregate.size) + 8 ≤ bs.data.size := by
    rw [hbs]; exact Nat.le_refl _
  rw [← hs1, ← hs2, ← hs3,
    readSlots_fixed_cons hgh hw1, Nat.zero_add,
    readSlots_fixed_cons hagg hw2,
    readSlots_fixed_cons (w := 8) rfl hw3,
    readSlots_nil]
  rfl

theorem Gloas.OptimisticUpdate.deserializeFields_ok (bs : ByteArray) (s1 s2 s3 : Bytes)
    (att : Gloas.Header) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncAggregate.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncAggregate.size)
      Gloas.OptimisticUpdate.size = s3)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hagg : SyncAggregate.read (slice bs Header.size SyncAggregate.size) = agg)
    (hsig : u64 bs (Header.size + SyncAggregate.size) = sig) :
    bs.size = Gloas.OptimisticUpdate.size →
      deserializeFields [gloasHeaderDesc, syncAggregateDesc, .uint 8] [s1, s2, s3] =
        .ok [att.toValue, agg.toValue, .uint sig] := fun hsz => by
  have h1 : deserialize gloasHeaderDesc s1 = .ok att.toValue := by
    have hle : 0 + Gloas.Header.size ≤ bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := Header.deserialize_slice bs 0 hle
    rw [Nat.zero_add, hatt, hs1] at h; exact h
  have h2 : deserialize syncAggregateDesc s2 = .ok agg.toValue := by
    have hle : Gloas.Header.size + 160 ≤ bs.size := by rw [hsz]; exact Nat.le_of_ble_eq_true rfl
    have h := SyncAggregate.deserialize_slice bs Header.size hle
    change deserialize syncAggregateDesc
      (bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncAggregate.size)) =
      .ok (SyncAggregate.read (slice bs Header.size SyncAggregate.size)).toValue at h
    rw [hagg, hs2] at h; exact h
  have h3 : deserialize (.uint 8) s3 = .ok (.uint sig) := by
    have hle : (Gloas.Header.size + SyncAggregate.size) + 8 ≤ bs.size := by
      rw [hsz]; exact Nat.le_refl _
    have h := deserialize_uint_slice bs (Gloas.Header.size + SyncAggregate.size) 8 hle
    change deserialize (.uint 8)
      (bs.data.extract (Gloas.Header.size + SyncAggregate.size) Gloas.OptimisticUpdate.size) =
      .ok (.uint (u64 bs (Gloas.Header.size + SyncAggregate.size))) at h
    rw [hsig, hs3] at h; exact h
  exact deserializeFields_cons_ok h1 (deserializeFields_cons_ok h2
    (deserializeFields_cons_ok h3 deserializeFields_nil))

theorem Gloas.OptimisticUpdate.deserialize_iff_aux (bs : ByteArray) (v : Value)
    (s1 s2 s3 : Bytes) (att : Gloas.Header) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncAggregate.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncAggregate.size)
      Gloas.OptimisticUpdate.size = s3)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hagg : SyncAggregate.read (slice bs Header.size SyncAggregate.size) = agg)
    (hsig : u64 bs (Header.size + SyncAggregate.size) = sig) :
    (deserialize gloasOptimisticUpdateDesc bs.data = .ok v) ↔
      bs.size = Gloas.OptimisticUpdate.size ∧ v = .seq [att.toValue, agg.toValue, .uint sig] :=
  (deserialize_container_fixed
    (names := ["attested_header", "sync_aggregate", "signature_slot"])
    (bs := bs) fieldsFixedSize_eq size_lt_offset
    (readSlots_ok bs s1 s2 s3 hs1 hs2 hs3)
    (fun _ => rfl) (fun _ => rfl)
    (deserializeFields_ok bs s1 s2 s3 att agg sig hs1 hs2 hs3 hatt hagg hsig)).1 v

theorem Gloas.OptimisticUpdate.decode_iff_core (bs : ByteArray) (x : Gloas.OptimisticUpdate)
    (s1 s2 s3 : Bytes) (att : Gloas.Header) (agg : SyncAggregate) (sig : Nat)
    (hs1 : bs.data.extract 0 Gloas.Header.size = s1)
    (hs2 : bs.data.extract Gloas.Header.size (Gloas.Header.size + SyncAggregate.size) = s2)
    (hs3 : bs.data.extract (Gloas.Header.size + SyncAggregate.size)
      Gloas.OptimisticUpdate.size = s3)
    (hatt : Header.read (slice bs 0 Header.size) = att)
    (hagg : SyncAggregate.read (slice bs Header.size SyncAggregate.size) = agg)
    (hsig : u64 bs (Header.size + SyncAggregate.size) = sig) :
    decode bs = some x ↔
      deserialize gloasOptimisticUpdateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  rw [deserialize_iff_aux bs x.toValue s1 s2 s3 att agg sig hs1 hs2 hs3 hatt hagg hsig]
  by_cases hsz : bs.size = Gloas.OptimisticUpdate.size
  · let u₀ : Gloas.OptimisticUpdate := {
      attestedHeader := att, syncAggregate := agg, signatureSlot := sig }
    have hd : decode bs = some u₀ := decode_eq_some hsz hatt hagg hsig
    have hfu₀ : u₀.Fits := decode_fits hd
    rw [hd]
    have htv : u₀.toValue = .seq [att.toValue, agg.toValue, .uint sig] := rfl
    rw [← htv]
    refine ⟨fun h => ?_, fun ⟨⟨_, hv⟩, hfx⟩ => congrArg some (toValue_inj hfu₀ hfx hv.symm)⟩
    injection h with h'
    exact ⟨⟨hsz, h' ▸ rfl⟩, h' ▸ hfu₀⟩
  · rw [decode_eq_none hsz]
    refine ⟨fun h => ?_, fun ⟨⟨h, _⟩, _⟩ => absurd h hsz⟩
    cases h

theorem Gloas.OptimisticUpdate.decode_iff (bs : ByteArray) (x : Gloas.OptimisticUpdate) :
    decode bs = some x ↔
      deserialize gloasOptimisticUpdateDesc bs.data = .ok x.toValue ∧ x.Fits :=
  decode_iff_core bs x _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

theorem Gloas.OptimisticUpdate.deserialize_eq_of_fits (bs : ByteArray)
    {x : Gloas.OptimisticUpdate} (hx : x.Fits) :
    decode bs = some x ↔ deserialize gloasOptimisticUpdateDesc bs.data = .ok x.toValue := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem Gloas.OptimisticUpdate.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize gloasOptimisticUpdateDesc bs.data).isOk := by
  by_cases hsz : bs.size = Gloas.OptimisticUpdate.size
  · generalize hatt : Header.read (slice bs 0 Header.size) = att
    generalize hagg : SyncAggregate.read (slice bs Header.size SyncAggregate.size) = agg
    generalize hsig : u64 bs (Header.size + SyncAggregate.size) = sig
    have hd := decode_eq_some hsz hatt hagg hsig
    rw [hd, ((decode_iff bs _).mp hd).1]; rfl
  · rw [decode_eq_none hsz, gloasOptimisticUpdateDesc,
      deserialize_container_fixed_reject fieldsFixedSize_eq hsz]; rfl

theorem Gloas.OptimisticUpdate.decode_canonical {bs : ByteArray} {u : Gloas.OptimisticUpdate}
    (hd : decode bs = some u) : serialize gloasOptimisticUpdateDesc u.toValue = .ok bs.data :=
  decode_canonical_of_iff_fits gloasOptimisticUpdateDesc_wellFormed decode_iff hd

theorem Gloas.OptimisticUpdate.decode_injective_bytes {bs₁ bs₂ : ByteArray}
    {u : Gloas.OptimisticUpdate}
    (h₁ : decode bs₁ = some u) (h₂ : decode bs₂ = some u) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff_fits gloasOptimisticUpdateDesc_wellFormed decode_iff h₁ h₂

theorem Gloas.OptimisticUpdate.decode_serialize {u : Gloas.OptimisticUpdate} {data : Bytes}
    (hu : u.Fits) (hs : serialize gloasOptimisticUpdateDesc u.toValue = .ok data) :
    decode ⟨data⟩ = some u :=
  decode_serialize_of_iff_fits gloasOptimisticUpdateDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ ha hb hv => toValue_inj ha hb hv) hu hs

end LeanLight.Lc.Ssz
