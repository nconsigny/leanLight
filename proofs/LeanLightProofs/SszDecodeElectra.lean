import LeanLightProofs.SszDecode

/-!
# Variable-size light-client decoders: `ExecutionPayloadHeader` and Electra / Fulu

Every variable-size decoder in `LeanLight.Ssz` (`ExecutionPayloadHeader` and the five `Electra.*`
light-client containers) accepts iff ssz-specs' `deserialize` accepts at its `Desc`, producing
the typed value denoting what `deserialize` returns (`decode_iff`, alongside `Fits` on updates
holding a `SyncAggregate`, and `deserialize_isSome`), so an offset out of order, past the end,
or other than the fixed part's position, or an `extra_data` over 32 bytes, is rejected alike.
Each inherits canonicality (`decode_canonical`), byte-level non-malleability
(`decode_injective_bytes`), and round-trip recovery (`decode_serialize`).
-/

namespace LeanLight.Lc.Ssz

open LeanLight.Lc.Bytes (byteAt)
open _root_.Ssz (Bytes Desc Value Err hashTreeRoot deserialize serialize readUint unpackBits
  readSlots structBudget structSlices vectorSlices deserializeEach deserializeFields offsetSpans
  takeSlots bodyStarts Slot bytesPerOffset)

/-! ## Generic variable-size container helpers -/

theorem takeSlots_nil (data : Bytes) (spans : List Nat) :
    takeSlots data [] spans = .ok [] := rfl

theorem takeSlots_inline {data : Bytes} {b : Bytes} {rest : List Slot} {spans : List Nat}
    {ps : List Bytes} (hr : takeSlots data rest spans = .ok ps) :
    takeSlots data (.inline b :: rest) spans = .ok (b :: ps) := by
  simp [takeSlots, hr, Bind.bind, Except.bind, pure, Except.pure]

theorem takeSlots_body {data : Bytes} {o span endPos : Nat} {rest : List Slot} {spans : List Nat}
    {s : Bytes} {ps : List Bytes} (hend : o + span = endPos)
    (hs : data.extract o endPos = s)
    (hr : takeSlots data rest spans = .ok ps) :
    takeSlots data (.body o :: rest) (span :: spans) = .ok (s :: ps) := by
  simp [takeSlots, hend, hs, hr, Bind.bind, Except.bind, pure, Except.pure]

theorem deserializeFields_isOk_false_head {f : Desc} {fs : List Desc} {p : Bytes} {ps : List Bytes}
    (hf : (deserialize f p).isOk = false) :
    (deserializeFields (f :: fs) (p :: ps)).isOk = false := by
  rw [deserializeFields]
  cases h : deserialize f p with
  | error e => rfl
  | ok v => rw [h] at hf; cases hf

theorem deserializeFields_isOk_false_tail {f : Desc} {fs : List Desc} {p : Bytes} {ps : List Bytes}
    {v : Value} (hf : deserialize f p = .ok v)
    (hfs : (deserializeFields fs ps).isOk = false) :
    (deserializeFields (f :: fs) (p :: ps)).isOk = false := by
  rw [deserializeFields, hf]
  change (do let tail ← deserializeFields fs ps; pure (v :: tail)).isOk = false
  cases h : deserializeFields fs ps with
  | error e => rfl
  | ok vs => rw [h] at hfs; cases hfs

theorem deserialize_container_isOk_false_of_slices {names : List String} {fs : List Desc}
    {data : Bytes} (hs : (structSlices fs data).isOk = false) :
    (deserialize (.container names fs) data).isOk = false := by
  rw [deserialize]
  cases h : structSlices fs data with
  | error e => rfl
  | ok ps => rw [h] at hs; cases hs

theorem deserialize_container_isOk_false_of_fields {names : List String} {fs : List Desc}
    {data : Bytes} {parts : List Bytes}
    (hs : structSlices fs data = .ok parts)
    (hdf : (deserializeFields fs parts).isOk = false) :
    (deserialize (.container names fs) data).isOk = false := by
  rw [deserialize, hs]
  change (do let vs ← deserializeFields fs parts; pure (Value.seq vs)).isOk = false
  cases h : deserializeFields fs parts with
  | error e => rfl
  | ok vs => rw [h] at hdf; cases hdf

theorem deserialize_container_var1_reject {names : List String} {fs : List Desc} {lead : Nat}
    {data : Bytes} {slots : List Slot} {o₁ : Nat} {parts : List Bytes}
    (hfw : Desc.fieldsFixedSize fs = none)
    (hlw : Desc.leadingWidth fs = lead)
    (hr : lead ≤ data.size → readSlots fs data 0 = .ok (slots, lead))
    (hb : lead ≤ data.size → bodyStarts slots = [o₁])
    (ht : lead ≤ data.size → o₁ = lead → takeSlots data slots [data.size - o₁] = .ok parts)
    (hbad : ¬ (data.size < 2 ^ (8 * bytesPerOffset) ∧ lead ≤ data.size ∧ o₁ = lead)) :
    (deserialize (.container names fs) data).isOk = false := by
  by_cases hov : data.size < 2 ^ (8 * bytesPerOffset)
  · have hbad' : ¬ (lead ≤ data.size ∧ o₁ = lead) := fun h => hbad ⟨hov, h⟩
    have hs := (structSlices_of_var1 hfw hlw hov hr hb ht).2 hbad'
    exact deserialize_container_isOk_false_of_slices hs
  · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl

theorem deserialize_container_var1_slices {fs : List Desc} {lead : Nat}
    {data : Bytes} {slots : List Slot} {o₁ : Nat} {parts : List Bytes}
    (hfw : Desc.fieldsFixedSize fs = none)
    (hlw : Desc.leadingWidth fs = lead)
    (hov : data.size < 2 ^ (8 * bytesPerOffset))
    (hle : lead ≤ data.size)
    (ho : o₁ = lead)
    (hr : lead ≤ data.size → readSlots fs data 0 = .ok (slots, lead))
    (hb : lead ≤ data.size → bodyStarts slots = [o₁])
    (ht : lead ≤ data.size → o₁ = lead → takeSlots data slots [data.size - o₁] = .ok parts) :
    structSlices fs data = .ok parts :=
  ((structSlices_of_var1 hfw hlw hov hr hb ht).1 parts).mpr ⟨⟨hle, ho⟩, rfl⟩

theorem deserialize_container_var2_reject {names : List String} {fs : List Desc} {lead : Nat}
    {data : Bytes} {slots : List Slot} {o₁ o₂ : Nat} {parts : List Bytes}
    (hfw : Desc.fieldsFixedSize fs = none)
    (hlw : Desc.leadingWidth fs = lead)
    (hr : lead ≤ data.size → readSlots fs data 0 = .ok (slots, lead))
    (hb : lead ≤ data.size → bodyStarts slots = [o₁, o₂])
    (ht : lead ≤ data.size → o₁ = lead → lead ≤ o₂ → o₂ ≤ data.size →
      takeSlots data slots [o₂ - o₁, data.size - o₂] = .ok parts)
    (hbad : ¬ (data.size < 2 ^ (8 * bytesPerOffset) ∧
      lead ≤ data.size ∧ o₁ = lead ∧ lead ≤ o₂ ∧ o₂ ≤ data.size)) :
    (deserialize (.container names fs) data).isOk = false := by
  by_cases hov : data.size < 2 ^ (8 * bytesPerOffset)
  · have hbad' : ¬ (lead ≤ data.size ∧ o₁ = lead ∧ lead ≤ o₂ ∧ o₂ ≤ data.size) :=
      fun h => hbad ⟨hov, h⟩
    have hs := (structSlices_of_var2 hfw hlw hov hr hb ht).2 hbad'
    exact deserialize_container_isOk_false_of_slices hs
  · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl

theorem deserialize_container_var2_slices {fs : List Desc} {lead : Nat}
    {data : Bytes} {slots : List Slot} {o₁ o₂ : Nat} {parts : List Bytes}
    (hfw : Desc.fieldsFixedSize fs = none)
    (hlw : Desc.leadingWidth fs = lead)
    (hov : data.size < 2 ^ (8 * bytesPerOffset))
    (hle : lead ≤ data.size)
    (ho1 : o₁ = lead)
    (ho2 : lead ≤ o₂)
    (ho3 : o₂ ≤ data.size)
    (hr : lead ≤ data.size → readSlots fs data 0 = .ok (slots, lead))
    (hb : lead ≤ data.size → bodyStarts slots = [o₁, o₂])
    (ht : lead ≤ data.size → o₁ = lead → lead ≤ o₂ → o₂ ≤ data.size →
      takeSlots data slots [o₂ - o₁, data.size - o₂] = .ok parts) :
    structSlices fs data = .ok parts :=
  ((structSlices_of_var2 hfw hlw hov hr hb ht).1 parts).mpr ⟨⟨hle, ho1, ho2, ho3⟩, rfl⟩

/-! ## `ExecutionPayloadHeader` -/

theorem ExecutionPayloadHeader.decode_size_le {bs : ByteArray} {e : ExecutionPayloadHeader}
    (hd : decode bs = some e) : bs.size ≤ 616 := by
  unfold decode at hd
  split at hd
  · rename_i hc; exact hc.2.1
  · cases hd

def ExecutionPayloadHeader.fieldDescs : List Desc :=
  [bytes32, .byteVector 20, bytes32, bytes32, .byteVector 256, bytes32, .uint 8, .uint 8, .uint 8,
    .uint 8, .byteList 32, .uint 32, bytes32, bytes32, bytes32, .uint 8, .uint 8]

theorem ExecutionPayloadHeader.fieldsFixedSize_eq :
    Desc.fieldsFixedSize fieldDescs = none := rfl

theorem ExecutionPayloadHeader.leadingWidth_eq :
    Desc.leadingWidth fieldDescs = ExecutionPayloadHeader.fixedSize := rfl

theorem ExecutionPayloadHeader.readSlots_ok (bs : ByteArray) (hle : fixedSize ≤ bs.data.size) :
    readSlots fieldDescs bs.data 0 =
      .ok ([.inline (bs.data.extract 0 32), .inline (bs.data.extract 32 52),
        .inline (bs.data.extract 52 84), .inline (bs.data.extract 84 116),
        .inline (bs.data.extract 116 372), .inline (bs.data.extract 372 404),
        .inline (bs.data.extract 404 412), .inline (bs.data.extract 412 420),
        .inline (bs.data.extract 420 428), .inline (bs.data.extract 428 436),
        .body (readUint bs.data 436 4),
        .inline (bs.data.extract 440 472), .inline (bs.data.extract 472 504),
        .inline (bs.data.extract 504 536), .inline (bs.data.extract 536 568),
        .inline (bs.data.extract 568 576), .inline (bs.data.extract 576 584)],
        fixedSize) := by
  have h584 : 584 ≤ bs.data.size := hle
  unfold fieldDescs fixedSize
  rw [readSlots_fixed_cons (w := 32) rfl (by omega), Nat.zero_add,
    readSlots_fixed_cons (w := 20) rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 256) rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_var_cons rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 32) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_nil]
  rfl

theorem ExecutionPayloadHeader.takeSlots_ok (bs : ByteArray)
    (hle : fixedSize ≤ bs.data.size) (ho : readUint bs.data 436 4 = fixedSize) :
    takeSlots bs.data
      [.inline (bs.data.extract 0 32), .inline (bs.data.extract 32 52),
        .inline (bs.data.extract 52 84), .inline (bs.data.extract 84 116),
        .inline (bs.data.extract 116 372), .inline (bs.data.extract 372 404),
        .inline (bs.data.extract 404 412), .inline (bs.data.extract 412 420),
        .inline (bs.data.extract 420 428), .inline (bs.data.extract 428 436),
        .body (readUint bs.data 436 4),
        .inline (bs.data.extract 440 472), .inline (bs.data.extract 472 504),
        .inline (bs.data.extract 504 536), .inline (bs.data.extract 536 568),
        .inline (bs.data.extract 568 576), .inline (bs.data.extract 576 584)]
      [bs.data.size - readUint bs.data 436 4] =
      .ok [bs.data.extract 0 32, bs.data.extract 32 52,
        bs.data.extract 52 84, bs.data.extract 84 116,
        bs.data.extract 116 372, bs.data.extract 372 404,
        bs.data.extract 404 412, bs.data.extract 412 420,
        bs.data.extract 420 428, bs.data.extract 428 436,
        bs.data.extract fixedSize bs.data.size,
        bs.data.extract 440 472, bs.data.extract 472 504,
        bs.data.extract 504 536, bs.data.extract 536 568,
        bs.data.extract 568 576, bs.data.extract 576 584] := by
  rw [ho]
  have hend : fixedSize + (bs.data.size - fixedSize) = bs.data.size := Nat.add_sub_of_le hle
  exact takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_inline
    (takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_inline
    (takeSlots_body hend rfl (takeSlots_inline (takeSlots_inline (takeSlots_inline
    (takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_nil _ _)))))))))))))))))

theorem ExecutionPayloadHeader.deserialize_iff_aux (bs : ByteArray) :
    (∀ v, deserialize executionPayloadHeaderDesc bs.data = .ok v ↔
      (fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧ offsetAt bs 436 = fixedSize) ∧
        v = ({
          parentHash := slice bs 0 32, feeRecipient := slice bs 32 20,
          stateRoot := slice bs 52 32, receiptsRoot := slice bs 84 32,
          logsBloom := slice bs 116 256, prevRandao := slice bs 372 32,
          blockNumber := u64 bs 404, gasLimit := u64 bs 412,
          gasUsed := u64 bs 420, timestamp := u64 bs 428,
          extraData := Bytes.extract bs fixedSize bs.size,
          baseFeePerGas := readLE bs 440 32, blockHash := slice bs 472 32,
          transactionsRoot := slice bs 504 32, withdrawalsRoot := slice bs 536 32,
          blobGasUsed := u64 bs 568, excessBlobGas := u64 bs 576 } :
            ExecutionPayloadHeader).toValue) ∧
      (¬ (fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧ offsetAt bs 436 = fixedSize) →
        (deserialize executionPayloadHeaderDesc bs.data).isOk = false) := by
  have heq : executionPayloadHeaderDesc = .container
      ["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom",
        "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp", "extra_data",
        "base_fee_per_gas", "block_hash", "transactions_root", "withdrawals_root", "blob_gas_used",
        "excess_blob_gas"] fieldDescs := rfl
  have hoff : offsetAt bs 436 = readUint bs.data 436 4 := offsetAt_eq_readUint bs 436
  have hf_pre : ∀ (hle : fixedSize ≤ bs.size) {p11 : Bytes} {v11 : Value},
      deserialize (.byteList 32) p11 = .ok v11 →
      deserializeFields fieldDescs
        [bs.data.extract 0 32, bs.data.extract 32 52,
          bs.data.extract 52 84, bs.data.extract 84 116,
          bs.data.extract 116 372, bs.data.extract 372 404,
          bs.data.extract 404 412, bs.data.extract 412 420,
          bs.data.extract 420 428, bs.data.extract 428 436,
          p11,
          bs.data.extract 440 472, bs.data.extract 472 504,
          bs.data.extract 504 536, bs.data.extract 536 568,
          bs.data.extract 568 576, bs.data.extract 576 584] =
        .ok [.bytes (slice bs 0 32).data, .bytes (slice bs 32 20).data,
          .bytes (slice bs 52 32).data, .bytes (slice bs 84 32).data,
          .bytes (slice bs 116 256).data, .bytes (slice bs 372 32).data,
          .uint (u64 bs 404), .uint (u64 bs 412),
          .uint (u64 bs 420), .uint (u64 bs 428),
          v11,
          .uint (readLE bs 440 32), .bytes (slice bs 472 32).data,
          .bytes (slice bs 504 32).data, .bytes (slice bs 536 32).data,
          .uint (u64 bs 568), .uint (u64 bs 576)] := by
    intro hle p11 v11 hp11
    have h584 : 584 ≤ bs.size := hle
    exact deserializeFields_cons_ok (deserialize_byteVector_slice bs 0 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 32 20 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 52 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 84 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 116 256 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 372 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_uint_slice bs 404 8 (by omega))
      (deserializeFields_cons_ok (deserialize_uint_slice bs 412 8 (by omega))
      (deserializeFields_cons_ok (deserialize_uint_slice bs 420 8 (by omega))
      (deserializeFields_cons_ok (deserialize_uint_slice bs 428 8 (by omega))
      (deserializeFields_cons_ok hp11
      (deserializeFields_cons_ok (deserialize_uint_slice bs 440 32 (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 472 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 504 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_byteVector_slice bs 536 32 (by decide) (by omega))
      (deserializeFields_cons_ok (deserialize_uint_slice bs 568 8 (by omega))
      (deserializeFields_cons_ok (deserialize_uint_slice bs 576 8 (by omega))
      deserializeFields_nil))))))))))))))))
  have hf_err : ∀ (hle : fixedSize ≤ bs.size) {p11 : Bytes},
      (deserialize (.byteList 32) p11).isOk = false →
      (deserializeFields fieldDescs
        [bs.data.extract 0 32, bs.data.extract 32 52,
          bs.data.extract 52 84, bs.data.extract 84 116,
          bs.data.extract 116 372, bs.data.extract 372 404,
          bs.data.extract 404 412, bs.data.extract 412 420,
          bs.data.extract 420 428, bs.data.extract 428 436,
          p11,
          bs.data.extract 440 472, bs.data.extract 472 504,
          bs.data.extract 504 536, bs.data.extract 536 568,
          bs.data.extract 568 576, bs.data.extract 576 584]).isOk = false := by
    intro hle p11 hp11
    have h584 : 584 ≤ bs.size := hle
    exact deserializeFields_isOk_false_tail (deserialize_byteVector_slice bs 0 32 (by decide) (by omega))
      (deserializeFields_isOk_false_tail (deserialize_byteVector_slice bs 32 20 (by decide) (by omega))
      (deserializeFields_isOk_false_tail (deserialize_byteVector_slice bs 52 32 (by decide) (by omega))
      (deserializeFields_isOk_false_tail (deserialize_byteVector_slice bs 84 32 (by decide) (by omega))
      (deserializeFields_isOk_false_tail (deserialize_byteVector_slice bs 116 256 (by decide) (by omega))
      (deserializeFields_isOk_false_tail (deserialize_byteVector_slice bs 372 32 (by decide) (by omega))
      (deserializeFields_isOk_false_tail (deserialize_uint_slice bs 404 8 (by omega))
      (deserializeFields_isOk_false_tail (deserialize_uint_slice bs 412 8 (by omega))
      (deserializeFields_isOk_false_tail (deserialize_uint_slice bs 420 8 (by omega))
      (deserializeFields_isOk_false_tail (deserialize_uint_slice bs 428 8 (by omega))
      (deserializeFields_isOk_false_head hp11))))))))))
  have hrej : ¬ (fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧
      offsetAt bs 436 = fixedSize) →
      (deserialize executionPayloadHeaderDesc bs.data).isOk = false := by
    intro hbad
    rw [heq]
    by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
    · by_cases htab : fixedSize ≤ bs.data.size ∧ readUint bs.data 436 4 = fixedSize
      · have hsl : structSlices fieldDescs bs.data = .ok _ :=
          deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq hov htab.1 htab.2
            (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have hlim : ¬ bs.size ≤ fixedSize + maxExtraData := fun h =>
          hbad ⟨htab.1, h, hoff.trans htab.2⟩
        have hover : ¬ bs.size - fixedSize ≤ 32 := by
          change ¬ bs.size ≤ 616 at hlim
          change ¬ bs.size - 584 ≤ 32
          omega
        have hbl : (deserialize (.byteList 32) (bs.data.extract fixedSize bs.data.size)).isOk = false := by
          have hb := deserialize_byteList_slice bs fixedSize bs.size 32 htab.1 (Nat.le_refl _) hov
          change (deserialize (.byteList 32) (bs.data.extract fixedSize bs.size)).isOk = false
          rw [hb, ite_eq_right hover]; rfl
        exact deserialize_container_isOk_false_of_fields hsl (hf_err htab.1 hbl)
      · exact deserialize_container_var1_reject fieldsFixedSize_eq leadingWidth_eq
          (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) (fun ⟨_, h1, h2⟩ => htab ⟨h1, h2⟩)
    · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
  refine ⟨fun v => ?_, hrej⟩
  by_cases hc : fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧ offsetAt bs 436 = fixedSize
  · have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := by
      have : bs.size ≤ 616 := hc.2.1
      have : bs.data.size < 4294967296 := by change bs.size < 4294967296; omega
      exact nat_lt_pow_offset this
    have ho : readUint bs.data 436 4 = fixedSize := hoff.symm.trans hc.2.2
    have hsl : structSlices fieldDescs bs.data = .ok _ :=
      deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq hov hc.1 ho
        (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
    have hlim : bs.size - fixedSize ≤ 32 := by
      have h616 : bs.size ≤ 616 := hc.2.1
      change bs.size - 584 ≤ 32
      omega
    have hbl : deserialize (.byteList 32) (bs.data.extract fixedSize bs.data.size) =
        .ok (.bytes (Bytes.extract bs fixedSize bs.size).data) := by
      have hb := deserialize_byteList_slice bs fixedSize bs.size 32 hc.1 (Nat.le_refl _) hov
      rw [ite_eq_left hlim] at hb
      exact hb
    have hdf := hf_pre hc.1 hbl
    rw [heq, deserialize_container_ok_of_slices hsl hdf v]
    exact ⟨fun h => ⟨hc, h⟩, fun ⟨_, hv⟩ => hv⟩
  · have hr := hrej hc
    refine ⟨fun h => ?_, fun ⟨h, _⟩ => absurd h hc⟩
    rw [h] at hr; cases hr

theorem ExecutionPayloadHeader.decode_iff (bs : ByteArray) (x : ExecutionPayloadHeader) :
    decode bs = some x ↔ deserialize executionPayloadHeaderDesc bs.data = .ok x.toValue := by
  rw [(deserialize_iff_aux bs).1 x.toValue]
  unfold decode
  by_cases hc : fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧ offsetAt bs 436 = fixedSize
  · rw [ite_eq_left hc]
    refine ⟨fun h => ?_, fun ⟨_, hv⟩ => congrArg some (toValue_inj hv.symm)⟩
    injection h with h'
    exact ⟨hc, h' ▸ rfl⟩
  · rw [ite_eq_right hc]
    refine ⟨fun h => ?_, fun ⟨h, _⟩ => absurd h hc⟩
    cases h

theorem ExecutionPayloadHeader.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize executionPayloadHeaderDesc bs.data).isOk := by
  by_cases hc : fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧ offsetAt bs 436 = fixedSize
  · have hd : ∃ e, decode bs = some e := by
      unfold decode; rw [ite_eq_left hc]; exact ⟨_, rfl⟩
    obtain ⟨e, he⟩ := hd
    rw [he, (decode_iff bs e).mp he]; rfl
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    rw [hd, (deserialize_iff_aux bs).2 hc]; rfl

theorem ExecutionPayloadHeader.decode_canonical {bs : ByteArray} {e : ExecutionPayloadHeader}
    (hd : decode bs = some e) : serialize executionPayloadHeaderDesc e.toValue = .ok bs.data :=
  decode_canonical_of_iff executionPayloadHeaderDesc_wellFormed decode_iff hd

theorem ExecutionPayloadHeader.decode_injective_bytes {bs₁ bs₂ : ByteArray}
    {e : ExecutionPayloadHeader}
    (h₁ : decode bs₁ = some e) (h₂ : decode bs₂ = some e) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff executionPayloadHeaderDesc_wellFormed decode_iff h₁ h₂

theorem ExecutionPayloadHeader.decode_serialize {e : ExecutionPayloadHeader} {data : Bytes}
    (hs : serialize executionPayloadHeaderDesc e.toValue = .ok data) : decode ⟨data⟩ = some e :=
  decode_serialize_of_iff executionPayloadHeaderDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

/-! ## `Electra.Header` -/

theorem Electra.Header.decode_size_le {bs : ByteArray} {h : Electra.Header}
    (hd : decode bs = some h) : bs.size ≤ 860 := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 112 = fixedSize
  · rw [ite_eq_left hc] at hd
    have h244 : 244 ≤ bs.size := hc.1
    cases he : ExecutionPayloadHeader.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [he] at hd; cases hd
    | some e =>
      have hle := ExecutionPayloadHeader.decode_size_le he
      rw [extract_size bs fixedSize bs.size hc.1 (Nat.le_refl _)] at hle
      change bs.size - 244 ≤ 616 at hle
      omega
  · rw [ite_eq_right hc] at hd; cases hd

def Electra.Header.fieldDescs : List Desc :=
  [beaconBlockHeaderDesc, executionPayloadHeaderDesc, branchDesc Electra.executionBranchLength]

theorem Electra.Header.fieldsFixedSize_eq :
    Desc.fieldsFixedSize fieldDescs = none := rfl

theorem Electra.Header.leadingWidth_eq :
    Desc.leadingWidth fieldDescs = Electra.Header.fixedSize := rfl

theorem Electra.Header.readSlots_ok (bs : ByteArray) (hle : fixedSize ≤ bs.data.size) :
    readSlots fieldDescs bs.data 0 =
      .ok ([.inline (bs.data.extract 0 112), .body (readUint bs.data 112 4),
        .inline (bs.data.extract 116 fixedSize)], fixedSize) := by
  have h244 : 244 ≤ bs.data.size := hle
  unfold fieldDescs fixedSize
  rw [readSlots_fixed_cons (w := 112) rfl (by omega), Nat.zero_add,
    readSlots_var_cons rfl (by omega),
    readSlots_fixed_cons (w := 128) rfl (by omega),
    readSlots_nil]
  rfl

theorem Electra.Header.takeSlots_ok (bs : ByteArray)
    (hle : fixedSize ≤ bs.data.size) (ho : readUint bs.data 112 4 = fixedSize) :
    takeSlots bs.data
      [.inline (bs.data.extract 0 112), .body (readUint bs.data 112 4),
        .inline (bs.data.extract 116 fixedSize)]
      [bs.data.size - readUint bs.data 112 4] =
      .ok [bs.data.extract 0 112, bs.data.extract fixedSize bs.data.size,
        bs.data.extract 116 fixedSize] := by
  rw [ho]
  exact takeSlots_inline (takeSlots_body (Nat.add_sub_of_le hle) rfl
    (takeSlots_inline (takeSlots_nil _ _)))

theorem Electra.Header.decode_iff (bs : ByteArray) (x : Electra.Header) :
    decode bs = some x ↔ deserialize electraHeaderDesc bs.data = .ok x.toValue := by
  have heq : electraHeaderDesc =
      .container ["beacon", "execution", "execution_branch"] fieldDescs := rfl
  have hoff : offsetAt bs 112 = readUint bs.data 112 4 := offsetAt_eq_readUint bs 112
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 112 = fixedSize
  · have h244 : 244 ≤ bs.size := hc.1
    have ho : readUint bs.data 112 4 = fixedSize := hoff.symm.trans hc.2
    have hbh : deserialize beaconBlockHeaderDesc (bs.data.extract 0 112) =
        .ok (BeaconBlockHeader.read (slice bs 0 112)).toValue := by
      have h := BeaconBlockHeader.deserialize_slice bs 0 (by omega)
      rwa [Nat.zero_add] at h
    have hbr : deserialize (branchDesc Electra.executionBranchLength)
        (bs.data.extract 116 fixedSize) =
        .ok (branchValue (roots bs 116 Electra.executionBranchLength)) :=
      deserialize_branch_slice bs 116 Electra.executionBranchLength
        (by decide) (by change 116 + 32 * 4 ≤ bs.size; omega)
    cases hex : ExecutionPayloadHeader.decode (Bytes.extract bs fixedSize bs.size) with
    | some e =>
      have hd : decode bs = some {
          beacon := BeaconBlockHeader.read (slice bs 0 112), execution := e,
          executionBranch := roots bs 116 Electra.executionBranchLength } := by
        unfold decode; rw [ite_eq_left hc, hex]
      have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := by
        have h860 := decode_size_le hd
        have : bs.data.size < 4294967296 := by change bs.size < 4294967296; omega
        exact nat_lt_pow_offset this
      have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
        hov hc.1 ho (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
      have hex_des : deserialize executionPayloadHeaderDesc
          (bs.data.extract fixedSize bs.data.size) = .ok e.toValue := by
        have h := (ExecutionPayloadHeader.decode_iff (Bytes.extract bs fixedSize bs.size) e).mp hex
        rwa [extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at h
      have hdf := deserializeFields_cons_ok hbh
        (deserializeFields_cons_ok hex_des (deserializeFields_cons_ok hbr deserializeFields_nil))
      rw [hd, heq, deserialize_container_ok_of_slices hsl hdf x.toValue]
      exact ⟨fun h => by injection h with h'; exact h' ▸ rfl,
        fun hv => congrArg some (toValue_inj hv.symm)⟩
    | none =>
      have hd : decode bs = none := by unfold decode; rw [ite_eq_left hc, hex]
      rw [hd, heq]
      constructor
      · intro h; cases h
      · intro hdes
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
        have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have hex_err : (deserialize executionPayloadHeaderDesc
            (bs.data.extract fixedSize bs.data.size)).isOk = false := by
          have his := ExecutionPayloadHeader.deserialize_isSome (Bytes.extract bs fixedSize bs.size)
          rw [hex, extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at his
          exact his.symm
        have hbad := deserialize_container_isOk_false_of_fields
          (names := ["beacon", "execution", "execution_branch"]) hsl
          (deserializeFields_isOk_false_tail hbh (deserializeFields_isOk_false_head hex_err))
        rw [hdes] at hbad; cases hbad
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 112 4 = fixedSize) :=
      fun ⟨_, h1, h2⟩ => hc ⟨h1, hoff.trans h2⟩
    have herr := deserialize_container_var1_reject
      (names := ["beacon", "execution", "execution_branch"])
      fieldsFixedSize_eq leadingWidth_eq (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) hbad
    rw [hd, heq]
    constructor
    · intro h; cases h
    · intro hdes; rw [hdes] at herr; cases herr

theorem Electra.Header.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize electraHeaderDesc bs.data).isOk := by
  have heq : electraHeaderDesc =
      .container ["beacon", "execution", "execution_branch"] fieldDescs := rfl
  have hoff : offsetAt bs 112 = readUint bs.data 112 4 := offsetAt_eq_readUint bs 112
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 112 = fixedSize
  · have h244 : 244 ≤ bs.size := hc.1
    have ho : readUint bs.data 112 4 = fixedSize := hoff.symm.trans hc.2
    cases hex : ExecutionPayloadHeader.decode (Bytes.extract bs fixedSize bs.size) with
    | some e =>
      have hd : decode bs = some {
          beacon := BeaconBlockHeader.read (slice bs 0 112), execution := e,
          executionBranch := roots bs 116 Electra.executionBranchLength } := by
        unfold decode; rw [ite_eq_left hc, hex]
      rw [hd, (decode_iff bs _).mp hd]; rfl
    | none =>
      have hd : decode bs = none := by unfold decode; rw [ite_eq_left hc, hex]
      rw [hd, heq]
      by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
      · have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have hbh : deserialize beaconBlockHeaderDesc (bs.data.extract 0 112) =
            .ok (BeaconBlockHeader.read (slice bs 0 112)).toValue := by
          have h := BeaconBlockHeader.deserialize_slice bs 0 (by omega)
          rwa [Nat.zero_add] at h
        have hex_err : (deserialize executionPayloadHeaderDesc
            (bs.data.extract fixedSize bs.data.size)).isOk = false := by
          have his := ExecutionPayloadHeader.deserialize_isSome (Bytes.extract bs fixedSize bs.size)
          rw [hex, extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at his
          exact his.symm
        rw [deserialize_container_isOk_false_of_fields hsl
          (deserializeFields_isOk_false_tail hbh (deserializeFields_isOk_false_head hex_err))]
        rfl
      · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 112 4 = fixedSize) :=
      fun ⟨_, h1, h2⟩ => hc ⟨h1, hoff.trans h2⟩
    rw [hd, heq, deserialize_container_var1_reject fieldsFixedSize_eq leadingWidth_eq
      (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) hbad]; rfl

theorem Electra.Header.decode_canonical {bs : ByteArray} {h : Electra.Header}
    (hd : decode bs = some h) : serialize electraHeaderDesc h.toValue = .ok bs.data :=
  decode_canonical_of_iff electraHeaderDesc_wellFormed decode_iff hd

theorem Electra.Header.decode_injective_bytes {bs₁ bs₂ : ByteArray} {h : Electra.Header}
    (h₁ : decode bs₁ = some h) (h₂ : decode bs₂ = some h) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff electraHeaderDesc_wellFormed decode_iff h₁ h₂

theorem Electra.Header.decode_serialize {h : Electra.Header} {data : Bytes}
    (hs : serialize electraHeaderDesc h.toValue = .ok data) : decode ⟨data⟩ = some h :=
  decode_serialize_of_iff electraHeaderDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

/-! ## `Electra.OptimisticUpdate` -/

theorem Electra.OptimisticUpdate.decode_size_le {bs : ByteArray} {u : Electra.OptimisticUpdate}
    (hd : decode bs = some u) : bs.size ≤ 1032 := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · rw [ite_eq_left hc] at hd
    have h172 : 172 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [ha] at hd; cases hd
    | some a =>
      have hle := Header.decode_size_le ha
      rw [extract_size bs fixedSize bs.size hc.1 (Nat.le_refl _)] at hle
      change bs.size - 172 ≤ 860 at hle
      omega
  · rw [ite_eq_right hc] at hd; cases hd

def Electra.OptimisticUpdate.fieldDescs : List Desc :=
  [electraHeaderDesc, syncAggregateDesc, .uint 8]

theorem Electra.OptimisticUpdate.fieldsFixedSize_eq :
    Desc.fieldsFixedSize fieldDescs = none := rfl

theorem Electra.OptimisticUpdate.leadingWidth_eq :
    Desc.leadingWidth fieldDescs = Electra.OptimisticUpdate.fixedSize := rfl

theorem Electra.OptimisticUpdate.readSlots_ok (bs : ByteArray) (hle : fixedSize ≤ bs.data.size) :
    readSlots fieldDescs bs.data 0 =
      .ok ([.body (readUint bs.data 0 4), .inline (bs.data.extract 4 164),
        .inline (bs.data.extract 164 fixedSize)], fixedSize) := by
  have h172 : 172 ≤ bs.data.size := hle
  unfold fieldDescs fixedSize
  rw [readSlots_var_cons rfl (by omega), Nat.zero_add,
    readSlots_fixed_cons (w := 160) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_nil]
  rfl

theorem Electra.OptimisticUpdate.takeSlots_ok (bs : ByteArray)
    (hle : fixedSize ≤ bs.data.size) (ho : readUint bs.data 0 4 = fixedSize) :
    takeSlots bs.data
      [.body (readUint bs.data 0 4), .inline (bs.data.extract 4 164),
        .inline (bs.data.extract 164 fixedSize)]
      [bs.data.size - readUint bs.data 0 4] =
      .ok [bs.data.extract fixedSize bs.data.size, bs.data.extract 4 164,
        bs.data.extract 164 fixedSize] := by
  rw [ho]
  exact takeSlots_body (Nat.add_sub_of_le hle) rfl
    (takeSlots_inline (takeSlots_inline (takeSlots_nil _ _)))

theorem Electra.OptimisticUpdate.decode_iff (bs : ByteArray) (x : Electra.OptimisticUpdate) :
    decode bs = some x ↔
      deserialize electraOptimisticUpdateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  have heq : electraOptimisticUpdateDesc =
      .container ["attested_header", "sync_aggregate", "signature_slot"] fieldDescs := rfl
  have hoff : offsetAt bs 0 = readUint bs.data 0 4 := offsetAt_eq_readUint bs 0
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · have h172 : 172 ≤ bs.size := hc.1
    have ho : readUint bs.data 0 4 = fixedSize := hoff.symm.trans hc.2
    have hagg : deserialize syncAggregateDesc (bs.data.extract 4 164) =
        .ok (SyncAggregate.read (slice bs 4 SyncAggregate.size)).toValue :=
      SyncAggregate.deserialize_slice bs 4 (by omega)
    have hsig : deserialize (.uint 8) (bs.data.extract 164 fixedSize) =
        .ok (.uint (u64 bs (4 + SyncAggregate.size))) :=
      deserialize_uint_slice bs 164 8 (by change 164 + 8 ≤ bs.size; omega)
    cases hatt : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | some a =>
      let u₀ : Electra.OptimisticUpdate := {
        attestedHeader := a,
        syncAggregate := SyncAggregate.read (slice bs 4 SyncAggregate.size),
        signatureSlot := u64 bs (4 + SyncAggregate.size) }
      have hd : decode bs = some u₀ := by unfold decode; rw [ite_eq_left hc, hatt]
      have hfu₀ : u₀.Fits := decode_fits hd
      have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := by
        have h1032 := decode_size_le hd
        have : bs.data.size < 4294967296 := by change bs.size < 4294967296; omega
        exact nat_lt_pow_offset this
      have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
        hov hc.1 ho (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
      have ha_des : deserialize electraHeaderDesc
          (bs.data.extract fixedSize bs.data.size) = .ok a.toValue := by
        have h := (Header.decode_iff (Bytes.extract bs fixedSize bs.size) a).mp hatt
        rwa [extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at h
      have hdf := deserializeFields_cons_ok ha_des
        (deserializeFields_cons_ok hagg (deserializeFields_cons_ok hsig deserializeFields_nil))
      rw [hd, heq, deserialize_container_ok_of_slices hsl hdf x.toValue]
      have htv : u₀.toValue = .seq [a.toValue,
          (SyncAggregate.read (slice bs 4 SyncAggregate.size)).toValue,
          .uint (u64 bs (4 + SyncAggregate.size))] := rfl
      rw [← htv]
      refine ⟨fun h => ?_, fun ⟨hv, hfx⟩ => congrArg some (toValue_inj hfu₀ hfx hv.symm)⟩
      injection h with h'
      exact ⟨h' ▸ rfl, h' ▸ hfu₀⟩
    | none =>
      have hd : decode bs = none := by unfold decode; rw [ite_eq_left hc, hatt]
      rw [hd, heq]
      constructor
      · intro h; cases h
      · rintro ⟨hdes, _⟩
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
        have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have ha_err : (deserialize electraHeaderDesc
            (bs.data.extract fixedSize bs.data.size)).isOk = false := by
          have his := Header.deserialize_isSome (Bytes.extract bs fixedSize bs.size)
          rw [hatt, extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at his
          exact his.symm
        have hbad := deserialize_container_isOk_false_of_fields
          (names := ["attested_header", "sync_aggregate", "signature_slot"]) hsl
          (deserializeFields_isOk_false_head ha_err)
        rw [hdes] at hbad; cases hbad
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 0 4 = fixedSize) :=
      fun ⟨_, h1, h2⟩ => hc ⟨h1, hoff.trans h2⟩
    have herr := deserialize_container_var1_reject
      (names := ["attested_header", "sync_aggregate", "signature_slot"])
      fieldsFixedSize_eq leadingWidth_eq (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) hbad
    rw [hd, heq]
    constructor
    · intro h; cases h
    · rintro ⟨hdes, _⟩; rw [hdes] at herr; cases herr

theorem Electra.OptimisticUpdate.deserialize_eq_of_fits (bs : ByteArray)
    {x : Electra.OptimisticUpdate} (hx : x.Fits) :
    decode bs = some x ↔ deserialize electraOptimisticUpdateDesc bs.data = .ok x.toValue := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem Electra.OptimisticUpdate.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize electraOptimisticUpdateDesc bs.data).isOk := by
  have heq : electraOptimisticUpdateDesc =
      .container ["attested_header", "sync_aggregate", "signature_slot"] fieldDescs := rfl
  have hoff : offsetAt bs 0 = readUint bs.data 0 4 := offsetAt_eq_readUint bs 0
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · have h172 : 172 ≤ bs.size := hc.1
    have ho : readUint bs.data 0 4 = fixedSize := hoff.symm.trans hc.2
    cases hatt : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | some a =>
      have hd : decode bs = some {
          attestedHeader := a,
          syncAggregate := SyncAggregate.read (slice bs 4 SyncAggregate.size),
          signatureSlot := u64 bs (4 + SyncAggregate.size) } := by
        unfold decode; rw [ite_eq_left hc, hatt]
      rw [hd, ((decode_iff bs _).mp hd).1]; rfl
    | none =>
      have hd : decode bs = none := by unfold decode; rw [ite_eq_left hc, hatt]
      rw [hd, heq]
      by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
      · have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have ha_err : (deserialize electraHeaderDesc
            (bs.data.extract fixedSize bs.data.size)).isOk = false := by
          have his := Header.deserialize_isSome (Bytes.extract bs fixedSize bs.size)
          rw [hatt, extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at his
          exact his.symm
        rw [deserialize_container_isOk_false_of_fields hsl
          (deserializeFields_isOk_false_head ha_err)]; rfl
      · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 0 4 = fixedSize) :=
      fun ⟨_, h1, h2⟩ => hc ⟨h1, hoff.trans h2⟩
    rw [hd, heq, deserialize_container_var1_reject fieldsFixedSize_eq leadingWidth_eq
      (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) hbad]; rfl

theorem Electra.OptimisticUpdate.decode_canonical {bs : ByteArray} {u : Electra.OptimisticUpdate}
    (hd : decode bs = some u) : serialize electraOptimisticUpdateDesc u.toValue = .ok bs.data :=
  decode_canonical_of_iff_fits electraOptimisticUpdateDesc_wellFormed decode_iff hd

theorem Electra.OptimisticUpdate.decode_injective_bytes {bs₁ bs₂ : ByteArray}
    {u : Electra.OptimisticUpdate}
    (h₁ : decode bs₁ = some u) (h₂ : decode bs₂ = some u) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff_fits electraOptimisticUpdateDesc_wellFormed decode_iff h₁ h₂

theorem Electra.OptimisticUpdate.decode_serialize {u : Electra.OptimisticUpdate} {data : Bytes}
    (hu : u.Fits) (hs : serialize electraOptimisticUpdateDesc u.toValue = .ok data) :
    decode ⟨data⟩ = some u :=
  decode_serialize_of_iff_fits electraOptimisticUpdateDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ ha hb hv => toValue_inj ha hb hv) hu hs

/-! ## `Electra.FinalityUpdate` -/

theorem Electra.FinalityUpdate.decode_size_le {bs : ByteArray} {u : Electra.FinalityUpdate}
    (hd : decode bs = some u) : bs.size ≤ 2120 := by
  unfold decode at hd
  dsimp only at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs 4 ∧ offsetAt bs 4 ≤ bs.size
  · rw [ite_eq_left hc] at hd
    have h400 : 400 ≤ bs.size := hc.1
    have ho2a : 400 ≤ offsetAt bs 4 := hc.2.2.1
    have ho2b : offsetAt bs 4 ≤ bs.size := hc.2.2.2
    cases ha : Header.decode (Bytes.extract bs fixedSize (offsetAt bs 4)) with
    | none => rw [ha] at hd; cases hd
    | some a =>
      cases hf : Header.decode (Bytes.extract bs (offsetAt bs 4) bs.size) with
      | none => rw [ha, hf] at hd; cases hd
      | some f =>
        have hlea := Header.decode_size_le ha
        have hlef := Header.decode_size_le hf
        rw [extract_size bs fixedSize (offsetAt bs 4) hc.2.2.1 hc.2.2.2] at hlea
        rw [extract_size bs (offsetAt bs 4) bs.size hc.2.2.2 (Nat.le_refl _)] at hlef
        change offsetAt bs 4 - 400 ≤ 860 at hlea
        omega
  · rw [ite_eq_right hc] at hd; cases hd

def Electra.FinalityUpdate.fieldDescs : List Desc :=
  [electraHeaderDesc, electraHeaderDesc, branchDesc Electra.finalityBranchLength,
    syncAggregateDesc, .uint 8]

theorem Electra.FinalityUpdate.fieldsFixedSize_eq :
    Desc.fieldsFixedSize fieldDescs = none := rfl

theorem Electra.FinalityUpdate.leadingWidth_eq :
    Desc.leadingWidth fieldDescs = Electra.FinalityUpdate.fixedSize := rfl

theorem Electra.FinalityUpdate.readSlots_ok (bs : ByteArray) (hle : fixedSize ≤ bs.data.size) :
    readSlots fieldDescs bs.data 0 =
      .ok ([.body (readUint bs.data 0 4), .body (readUint bs.data 4 4),
        .inline (bs.data.extract 8 232), .inline (bs.data.extract 232 392),
        .inline (bs.data.extract 392 fixedSize)], fixedSize) := by
  have h400 : 400 ≤ bs.data.size := hle
  unfold fieldDescs fixedSize
  rw [readSlots_var_cons rfl (by omega), Nat.zero_add,
    readSlots_var_cons rfl (by omega),
    readSlots_fixed_cons (w := 224) rfl (by omega),
    readSlots_fixed_cons (w := 160) rfl (by omega),
    readSlots_fixed_cons (w := 8) rfl (by omega),
    readSlots_nil]
  rfl

theorem Electra.FinalityUpdate.takeSlots_ok (bs : ByteArray)
    (_hle : fixedSize ≤ bs.data.size) (ho1 : readUint bs.data 0 4 = fixedSize)
    (ho2 : fixedSize ≤ readUint bs.data 4 4) (ho3 : readUint bs.data 4 4 ≤ bs.data.size) :
    takeSlots bs.data
      [.body (readUint bs.data 0 4), .body (readUint bs.data 4 4),
        .inline (bs.data.extract 8 232), .inline (bs.data.extract 232 392),
        .inline (bs.data.extract 392 fixedSize)]
      [readUint bs.data 4 4 - readUint bs.data 0 4, bs.data.size - readUint bs.data 4 4] =
      .ok [bs.data.extract fixedSize (readUint bs.data 4 4),
        bs.data.extract (readUint bs.data 4 4) bs.data.size,
        bs.data.extract 8 232, bs.data.extract 232 392,
        bs.data.extract 392 fixedSize] := by
  rw [ho1]
  exact takeSlots_body (Nat.add_sub_of_le ho2) rfl
    (takeSlots_body (Nat.add_sub_of_le ho3) rfl
      (takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_nil _ _)))))

theorem Electra.FinalityUpdate.decode_iff (bs : ByteArray) (x : Electra.FinalityUpdate) :
    decode bs = some x ↔
      deserialize electraFinalityUpdateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  have heq : electraFinalityUpdateDesc =
      .container ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
        "signature_slot"] fieldDescs := rfl
  have hoff0 : offsetAt bs 0 = readUint bs.data 0 4 := offsetAt_eq_readUint bs 0
  have hoff4 : offsetAt bs 4 = readUint bs.data 4 4 := offsetAt_eq_readUint bs 4
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs 4 ∧ offsetAt bs 4 ≤ bs.size
  · have h400 : 400 ≤ bs.size := hc.1
    have ho1 : readUint bs.data 0 4 = fixedSize := hoff0.symm.trans hc.2.1
    have ho2 : fixedSize ≤ readUint bs.data 4 4 := hoff4 ▸ hc.2.2.1
    have ho3 : readUint bs.data 4 4 ≤ bs.data.size := hoff4 ▸ hc.2.2.2
    have hfbr : deserialize (branchDesc Electra.finalityBranchLength) (bs.data.extract 8 232) =
        .ok (branchValue (roots bs 8 Electra.finalityBranchLength)) :=
      deserialize_branch_slice bs 8 Electra.finalityBranchLength (nat_lt_of_ble rfl)
        (by change 8 + 224 ≤ bs.size; omega)
    have hagg : deserialize syncAggregateDesc (bs.data.extract 232 392) =
        .ok (SyncAggregate.read (slice bs (8 + 32 * Electra.finalityBranchLength)
          SyncAggregate.size)).toValue :=
      SyncAggregate.deserialize_slice bs 232 (by omega)
    have hsig : deserialize (.uint 8) (bs.data.extract 392 fixedSize) =
        .ok (.uint (u64 bs (8 + 32 * Electra.finalityBranchLength + SyncAggregate.size))) :=
      deserialize_uint_slice bs 392 8 (by change 392 + 8 ≤ bs.size; omega)
    cases hatt : Header.decode (Bytes.extract bs fixedSize (offsetAt bs 4)) with
    | some a =>
      have ha_des : deserialize electraHeaderDesc
          (bs.data.extract fixedSize (readUint bs.data 4 4)) = .ok a.toValue := by
        have h := (Header.decode_iff (Bytes.extract bs fixedSize (offsetAt bs 4)) a).mp hatt
        rwa [extract_data_of_le bs fixedSize (offsetAt bs 4) hc.2.2.1 hc.2.2.2, hoff4] at h
      cases hfin : Header.decode (Bytes.extract bs (offsetAt bs 4) bs.size) with
      | some f =>
        let u₀ : Electra.FinalityUpdate := {
          attestedHeader := a, finalizedHeader := f,
          finalityBranch := roots bs 8 Electra.finalityBranchLength,
          syncAggregate := SyncAggregate.read (slice bs (8 + 32 * Electra.finalityBranchLength)
            SyncAggregate.size),
          signatureSlot := u64 bs (8 + 32 * Electra.finalityBranchLength + SyncAggregate.size) }
        have hd : decode bs = some u₀ := by
          unfold decode; dsimp only; rw [ite_eq_left hc, hatt, hfin]
        have hfu₀ : u₀.Fits := decode_fits hd
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := by
          have h2120 := decode_size_le hd
          have : bs.data.size < 4294967296 := by change bs.size < 4294967296; omega
          exact nat_lt_pow_offset this
        have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho1 ho2 ho3 (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have hf_des : deserialize electraHeaderDesc
            (bs.data.extract (readUint bs.data 4 4) bs.data.size) = .ok f.toValue := by
          have h := (Header.decode_iff (Bytes.extract bs (offsetAt bs 4) bs.size) f).mp hfin
          rwa [extract_data_of_le bs (offsetAt bs 4) bs.size hc.2.2.2 (Nat.le_refl _), hoff4] at h
        have hdf := deserializeFields_cons_ok ha_des
          (deserializeFields_cons_ok hf_des
            (deserializeFields_cons_ok hfbr
              (deserializeFields_cons_ok hagg
                (deserializeFields_cons_ok hsig deserializeFields_nil))))
        rw [hd, heq, deserialize_container_ok_of_slices hsl hdf x.toValue]
        have htv : u₀.toValue = .seq [a.toValue, f.toValue,
            branchValue (roots bs 8 Electra.finalityBranchLength),
            (SyncAggregate.read (slice bs (8 + 32 * Electra.finalityBranchLength)
              SyncAggregate.size)).toValue,
            .uint (u64 bs (8 + 32 * Electra.finalityBranchLength + SyncAggregate.size))] := rfl
        rw [← htv]
        refine ⟨fun h => ?_, fun ⟨hv, hfx⟩ => congrArg some (toValue_inj hfu₀ hfx hv.symm)⟩
        injection h with h'
        exact ⟨h' ▸ rfl, h' ▸ hfu₀⟩
      | none =>
        have hd : decode bs = none := by
          unfold decode; dsimp only; rw [ite_eq_left hc, hatt, hfin]
        rw [hd, heq]
        constructor
        · intro h; cases h
        · rintro ⟨hdes, _⟩
          have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
          have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
            hov hc.1 ho1 ho2 ho3 (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
          have hf_err : (deserialize electraHeaderDesc
              (bs.data.extract (readUint bs.data 4 4) bs.data.size)).isOk = false := by
            have his := Header.deserialize_isSome (Bytes.extract bs (offsetAt bs 4) bs.size)
            rw [hfin, extract_data_of_le bs (offsetAt bs 4) bs.size hc.2.2.2 (Nat.le_refl _),
              hoff4] at his
            exact his.symm
          have hbad := deserialize_container_isOk_false_of_fields
            (names := ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
              "signature_slot"]) hsl
            (deserializeFields_isOk_false_tail ha_des (deserializeFields_isOk_false_head hf_err))
          rw [hdes] at hbad; cases hbad
    | none =>
      have hd : decode bs = none := by
        unfold decode; dsimp only; rw [ite_eq_left hc, hatt]
      rw [hd, heq]
      constructor
      · intro h; cases h
      · rintro ⟨hdes, _⟩
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
        have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho1 ho2 ho3 (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have ha_err : (deserialize electraHeaderDesc
            (bs.data.extract fixedSize (readUint bs.data 4 4))).isOk = false := by
          have his := Header.deserialize_isSome (Bytes.extract bs fixedSize (offsetAt bs 4))
          rw [hatt, extract_data_of_le bs fixedSize (offsetAt bs 4) hc.2.2.1 hc.2.2.2,
            hoff4] at his
          exact his.symm
        have hbad := deserialize_container_isOk_false_of_fields
          (names := ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
            "signature_slot"]) hsl
          (deserializeFields_isOk_false_head ha_err)
        rw [hdes] at hbad; cases hbad
  · have hd : decode bs = none := by unfold decode; dsimp only; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 0 4 = fixedSize ∧
        fixedSize ≤ readUint bs.data 4 4 ∧ readUint bs.data 4 4 ≤ bs.data.size) :=
      fun ⟨_, h1, h2, h3, h4⟩ => hc ⟨h1, hoff0.trans h2, hoff4.symm ▸ h3, hoff4.symm ▸ h4⟩
    have herr := deserialize_container_var2_reject
      (names := ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
        "signature_slot"])
      fieldsFixedSize_eq leadingWidth_eq (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) hbad
    rw [hd, heq]
    constructor
    · intro h; cases h
    · rintro ⟨hdes, _⟩; rw [hdes] at herr; cases herr

theorem Electra.FinalityUpdate.deserialize_eq_of_fits (bs : ByteArray)
    {x : Electra.FinalityUpdate} (hx : x.Fits) :
    decode bs = some x ↔ deserialize electraFinalityUpdateDesc bs.data = .ok x.toValue := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem Electra.FinalityUpdate.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize electraFinalityUpdateDesc bs.data).isOk := by
  have heq : electraFinalityUpdateDesc =
      .container ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
        "signature_slot"] fieldDescs := rfl
  have hoff0 : offsetAt bs 0 = readUint bs.data 0 4 := offsetAt_eq_readUint bs 0
  have hoff4 : offsetAt bs 4 = readUint bs.data 4 4 := offsetAt_eq_readUint bs 4
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs 4 ∧ offsetAt bs 4 ≤ bs.size
  · have ho1 : readUint bs.data 0 4 = fixedSize := hoff0.symm.trans hc.2.1
    have ho2 : fixedSize ≤ readUint bs.data 4 4 := hoff4 ▸ hc.2.2.1
    have ho3 : readUint bs.data 4 4 ≤ bs.data.size := hoff4 ▸ hc.2.2.2
    cases hatt : Header.decode (Bytes.extract bs fixedSize (offsetAt bs 4)) with
    | some a =>
      cases hfin : Header.decode (Bytes.extract bs (offsetAt bs 4) bs.size) with
      | some f =>
        have hd : decode bs = some {
            attestedHeader := a, finalizedHeader := f,
            finalityBranch := roots bs 8 Electra.finalityBranchLength,
            syncAggregate := SyncAggregate.read (slice bs (8 + 32 * Electra.finalityBranchLength)
              SyncAggregate.size),
            signatureSlot := u64 bs (8 + 32 * Electra.finalityBranchLength + SyncAggregate.size) } := by
          unfold decode; dsimp only; rw [ite_eq_left hc, hatt, hfin]
        rw [hd, ((decode_iff bs _).mp hd).1]; rfl
      | none =>
        have hd : decode bs = none := by
          unfold decode; dsimp only; rw [ite_eq_left hc, hatt, hfin]
        rw [hd, heq]
        by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
        · have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
            hov hc.1 ho1 ho2 ho3 (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
          have ha_des : deserialize electraHeaderDesc
              (bs.data.extract fixedSize (readUint bs.data 4 4)) = .ok a.toValue := by
            have h := (Header.decode_iff (Bytes.extract bs fixedSize (offsetAt bs 4)) a).mp hatt
            rwa [extract_data_of_le bs fixedSize (offsetAt bs 4) hc.2.2.1 hc.2.2.2, hoff4] at h
          have hf_err : (deserialize electraHeaderDesc
              (bs.data.extract (readUint bs.data 4 4) bs.data.size)).isOk = false := by
            have his := Header.deserialize_isSome (Bytes.extract bs (offsetAt bs 4) bs.size)
            rw [hfin, extract_data_of_le bs (offsetAt bs 4) bs.size hc.2.2.2 (Nat.le_refl _),
              hoff4] at his
            exact his.symm
          rw [deserialize_container_isOk_false_of_fields hsl
            (deserializeFields_isOk_false_tail ha_des (deserializeFields_isOk_false_head hf_err))]
          rfl
        · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
    | none =>
      have hd : decode bs = none := by
        unfold decode; dsimp only; rw [ite_eq_left hc, hatt]
      rw [hd, heq]
      by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
      · have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho1 ho2 ho3 (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs)
        have ha_err : (deserialize electraHeaderDesc
            (bs.data.extract fixedSize (readUint bs.data 4 4))).isOk = false := by
          have his := Header.deserialize_isSome (Bytes.extract bs fixedSize (offsetAt bs 4))
          rw [hatt, extract_data_of_le bs fixedSize (offsetAt bs 4) hc.2.2.1 hc.2.2.2,
            hoff4] at his
          exact his.symm
        rw [deserialize_container_isOk_false_of_fields hsl
          (deserializeFields_isOk_false_head ha_err)]; rfl
      · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
  · have hd : decode bs = none := by unfold decode; dsimp only; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 0 4 = fixedSize ∧
        fixedSize ≤ readUint bs.data 4 4 ∧ readUint bs.data 4 4 ≤ bs.data.size) :=
      fun ⟨_, h1, h2, h3, h4⟩ => hc ⟨h1, hoff0.trans h2, hoff4.symm ▸ h3, hoff4.symm ▸ h4⟩
    rw [hd, heq, deserialize_container_var2_reject fieldsFixedSize_eq leadingWidth_eq
      (readSlots_ok bs) (fun _ => rfl) (takeSlots_ok bs) hbad]; rfl

theorem Electra.FinalityUpdate.decode_canonical {bs : ByteArray} {u : Electra.FinalityUpdate}
    (hd : decode bs = some u) : serialize electraFinalityUpdateDesc u.toValue = .ok bs.data :=
  decode_canonical_of_iff_fits electraFinalityUpdateDesc_wellFormed decode_iff hd

theorem Electra.FinalityUpdate.decode_injective_bytes {bs₁ bs₂ : ByteArray}
    {u : Electra.FinalityUpdate}
    (h₁ : decode bs₁ = some u) (h₂ : decode bs₂ = some u) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff_fits electraFinalityUpdateDesc_wellFormed decode_iff h₁ h₂

theorem Electra.FinalityUpdate.decode_serialize {u : Electra.FinalityUpdate} {data : Bytes}
    (hu : u.Fits) (hs : serialize electraFinalityUpdateDesc u.toValue = .ok data) :
    decode ⟨data⟩ = some u :=
  decode_serialize_of_iff_fits electraFinalityUpdateDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ ha hb hv => toValue_inj ha hb hv) hu hs

/-! ## `Electra.Bootstrap` -/

theorem size_lt_of_sub_le {n f b : Nat} (hf : f ≤ n) (hsub : n - f ≤ b)
    (hsum : f + b < 4294967296) : n < 2 ^ (8 * bytesPerOffset) := by
  have hle : n ≤ f + b := by
    rw [← Nat.add_sub_of_le hf]
    exact Nat.add_le_add_left hsub f
  exact nat_lt_pow_offset (Nat.lt_of_le_of_lt hle hsum)

def Electra.Bootstrap.fieldDescs : List Desc :=
  [electraHeaderDesc, syncCommitteeDesc, branchDesc Electra.syncCommitteeBranchLength]

theorem Electra.Bootstrap.fieldsFixedSize_eq :
    Desc.fieldsFixedSize fieldDescs = none := rfl

theorem Electra.Bootstrap.leadingWidth_eq :
    Desc.leadingWidth fieldDescs = Electra.Bootstrap.fixedSize := rfl

theorem Electra.Bootstrap.readSlots_ok (bs : ByteArray) (s2 s3 : Bytes)
    (hs2 : bs.data.extract 4 (4 + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (4 + SyncCommittee.size) fixedSize = s3)
    (hle : fixedSize ≤ bs.data.size) :
    readSlots fieldDescs bs.data 0 =
      .ok ([.body (readUint bs.data 0 4), .inline s2, .inline s3], fixedSize) := by
  have heh : electraHeaderDesc.fixedSize = none := rfl
  have hsc : syncCommitteeDesc.fixedSize = some SyncCommittee.size := rfl
  have hcbr : (branchDesc Electra.syncCommitteeBranchLength).fixedSize =
      some (32 * Electra.syncCommitteeBranchLength) := rfl
  have hw1 : 0 + 4 ≤ bs.data.size :=
    Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw2 : 4 + SyncCommittee.size ≤ bs.data.size :=
    Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw3 : (4 + SyncCommittee.size) + 32 * Electra.syncCommitteeBranchLength ≤ bs.data.size :=
    hle
  unfold fieldDescs
  rw [← hs2, ← hs3,
    readSlots_var_cons heh hw1, Nat.zero_add,
    readSlots_fixed_cons hsc hw2,
    readSlots_fixed_cons hcbr hw3,
    readSlots_nil]
  rfl

theorem Electra.Bootstrap.takeSlots_ok (bs : ByteArray) (s1 s2 s3 : Bytes)
    (hs1 : bs.data.extract fixedSize bs.data.size = s1)
    (hle : fixedSize ≤ bs.data.size) (ho : readUint bs.data 0 4 = fixedSize) :
    takeSlots bs.data
      [.body (readUint bs.data 0 4), .inline s2, .inline s3]
      [bs.data.size - readUint bs.data 0 4] =
      .ok [s1, s2, s3] := by
  rw [ho]
  exact takeSlots_body (Nat.add_sub_of_le hle) hs1
    (takeSlots_inline (takeSlots_inline (takeSlots_nil _ _)))

theorem Electra.Bootstrap.decode_iff_core (bs : ByteArray) (x : Electra.Bootstrap)
    (s1 s2 s3 : Bytes) (sc0 : SyncCommittee) (cbr : Array ByteArray)
    (hs1 : bs.data.extract fixedSize bs.data.size = s1)
    (hs2 : bs.data.extract 4 (4 + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (4 + SyncCommittee.size) fixedSize = s3)
    (hsc0 : SyncCommittee.read (slice bs 4 SyncCommittee.size) = sc0)
    (hcbr : roots bs (4 + SyncCommittee.size) Electra.syncCommitteeBranchLength = cbr) :
    decode bs = some x ↔ deserialize electraBootstrapDesc bs.data = .ok x.toValue := by
  have heq : electraBootstrapDesc =
      .container ["header", "current_sync_committee", "current_sync_committee_branch"]
        fieldDescs := rfl
  have hoff : offsetAt bs 0 = readUint bs.data 0 4 := offsetAt_eq_readUint bs 0
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · have ho : readUint bs.data 0 4 = fixedSize := hoff.symm.trans hc.2
    have hsc_des : deserialize syncCommitteeDesc s2 = .ok sc0.toValue := by
      have hle : 4 + SyncCommittee.size ≤ bs.size :=
        Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
      have h := SyncCommittee.deserialize_slice bs 4 hle
      rwa [hsc0, hs2] at h
    have hcbr_des : deserialize (branchDesc Electra.syncCommitteeBranchLength) s3 =
        .ok (branchValue cbr) := by
      have h := deserialize_branch_slice bs (4 + SyncCommittee.size)
        Electra.syncCommitteeBranchLength (nat_lt_of_ble rfl) hc.1
      change deserialize (branchDesc Electra.syncCommitteeBranchLength)
        (bs.data.extract (4 + SyncCommittee.size) fixedSize) = .ok (branchValue _) at h
      rwa [hcbr, hs3] at h
    cases hhdr : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | some h =>
      let b₀ : Electra.Bootstrap := {
        header := h, currentSyncCommittee := sc0, currentSyncCommitteeBranch := cbr }
      have hd : decode bs = some b₀ := by
        unfold decode; rw [ite_eq_left hc, hhdr, hsc0, hcbr]
      have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := by
        have hle := Header.decode_size_le hhdr
        rw [extract_size bs fixedSize bs.size hc.1 (Nat.le_refl _)] at hle
        exact size_lt_of_sub_le hc.1 hle (nat_lt_of_ble rfl)
      have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
        hov hc.1 ho (readSlots_ok bs s2 s3 hs2 hs3) (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 hs1)
      have hh_des : deserialize electraHeaderDesc s1 = .ok h.toValue := by
        have hdes := (Header.decode_iff (Bytes.extract bs fixedSize bs.size) h).mp hhdr
        rw [extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at hdes
        rwa [← hs1]
      have hdf := deserializeFields_cons_ok hh_des
        (deserializeFields_cons_ok hsc_des (deserializeFields_cons_ok hcbr_des deserializeFields_nil))
      rw [hd, heq, deserialize_container_ok_of_slices hsl hdf x.toValue]
      have htv : b₀.toValue = .seq [h.toValue, sc0.toValue, branchValue cbr] := rfl
      rw [← htv]
      exact ⟨fun h' => congrArg toValue (Option.some.inj h').symm,
        fun hv => congrArg some (toValue_inj hv.symm)⟩
    | none =>
      have hd : decode bs = none := by unfold decode; rw [ite_eq_left hc, hhdr]
      rw [hd, heq]
      constructor
      · intro h; cases h
      · intro hdes
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
        have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho (readSlots_ok bs s2 s3 hs2 hs3) (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 hs1)
        have hh_err : (deserialize electraHeaderDesc s1).isOk = false := by
          have his := Header.deserialize_isSome (Bytes.extract bs fixedSize bs.size)
          rw [hhdr, extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at his
          rw [← hs1]; exact his.symm
        have hbad := deserialize_container_isOk_false_of_fields
          (names := ["header", "current_sync_committee", "current_sync_committee_branch"]) hsl
          (deserializeFields_isOk_false_head hh_err)
        rw [hdes] at hbad; cases hbad
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 0 4 = fixedSize) :=
      fun ⟨_, h1, h2⟩ => hc ⟨h1, hoff.trans h2⟩
    have herr := deserialize_container_var1_reject
      (names := ["header", "current_sync_committee", "current_sync_committee_branch"])
      fieldsFixedSize_eq leadingWidth_eq (readSlots_ok bs s2 s3 hs2 hs3) (fun _ => rfl)
      (takeSlots_ok bs s1 s2 s3 hs1) hbad
    rw [hd, heq]
    constructor
    · intro h; cases h
    · intro hdes; rw [hdes] at herr; cases herr

theorem Electra.Bootstrap.decode_iff (bs : ByteArray) (x : Electra.Bootstrap) :
    decode bs = some x ↔ deserialize electraBootstrapDesc bs.data = .ok x.toValue :=
  decode_iff_core bs x _ _ _ _ _ rfl rfl rfl rfl rfl

theorem Electra.Bootstrap.deserialize_isSome_core (bs : ByteArray)
    (s1 s2 s3 : Bytes) (sc0 : SyncCommittee) (cbr : Array ByteArray)
    (hs1 : bs.data.extract fixedSize bs.data.size = s1)
    (hs2 : bs.data.extract 4 (4 + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (4 + SyncCommittee.size) fixedSize = s3)
    (hsc0 : SyncCommittee.read (slice bs 4 SyncCommittee.size) = sc0)
    (hcbr : roots bs (4 + SyncCommittee.size) Electra.syncCommitteeBranchLength = cbr) :
    (decode bs).isSome = (deserialize electraBootstrapDesc bs.data).isOk := by
  have heq : electraBootstrapDesc =
      .container ["header", "current_sync_committee", "current_sync_committee_branch"]
        fieldDescs := rfl
  have hoff : offsetAt bs 0 = readUint bs.data 0 4 := offsetAt_eq_readUint bs 0
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · have ho : readUint bs.data 0 4 = fixedSize := hoff.symm.trans hc.2
    cases hhdr : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | some h =>
      have hd : decode bs = some {
          header := h, currentSyncCommittee := sc0, currentSyncCommitteeBranch := cbr } := by
        unfold decode; rw [ite_eq_left hc, hhdr, hsc0, hcbr]
      rw [hd, (decode_iff bs _).mp hd]; rfl
    | none =>
      have hd : decode bs = none := by unfold decode; rw [ite_eq_left hc, hhdr]
      rw [hd, heq]
      by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
      · have hsl := deserialize_container_var1_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho (readSlots_ok bs s2 s3 hs2 hs3) (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 hs1)
        have hh_err : (deserialize electraHeaderDesc s1).isOk = false := by
          have his := Header.deserialize_isSome (Bytes.extract bs fixedSize bs.size)
          rw [hhdr, extract_data_of_le bs fixedSize bs.size hc.1 (Nat.le_refl _)] at his
          rw [← hs1]; exact his.symm
        rw [deserialize_container_isOk_false_of_fields hsl
          (deserializeFields_isOk_false_head hh_err)]; rfl
      · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
  · have hd : decode bs = none := by unfold decode; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ readUint bs.data 0 4 = fixedSize) :=
      fun ⟨_, h1, h2⟩ => hc ⟨h1, hoff.trans h2⟩
    rw [hd, heq, deserialize_container_var1_reject fieldsFixedSize_eq leadingWidth_eq
      (readSlots_ok bs s2 s3 hs2 hs3) (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 hs1) hbad]; rfl

theorem Electra.Bootstrap.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize electraBootstrapDesc bs.data).isOk :=
  deserialize_isSome_core bs _ _ _ _ _ rfl rfl rfl rfl rfl

theorem Electra.Bootstrap.decode_canonical {bs : ByteArray} {b : Electra.Bootstrap}
    (hd : decode bs = some b) : serialize electraBootstrapDesc b.toValue = .ok bs.data :=
  decode_canonical_of_iff electraBootstrapDesc_wellFormed decode_iff hd

theorem Electra.Bootstrap.decode_injective_bytes {bs₁ bs₂ : ByteArray} {b : Electra.Bootstrap}
    (h₁ : decode bs₁ = some b) (h₂ : decode bs₂ = some b) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff electraBootstrapDesc_wellFormed decode_iff h₁ h₂

theorem Electra.Bootstrap.decode_serialize {b : Electra.Bootstrap} {data : Bytes}
    (hs : serialize electraBootstrapDesc b.toValue = .ok data) : decode ⟨data⟩ = some b :=
  decode_serialize_of_iff electraBootstrapDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ _ _ hv => toValue_inj hv) hs

/-! ## `Electra.Update` -/

theorem size_lt_of_two_sub_le {n f o b₁ b₂ : Nat} (hf : f ≤ o) (ho : o ≤ n)
    (hs1 : o - f ≤ b₁) (hs2 : n - o ≤ b₂)
    (hsum : f + b₁ + b₂ < 4294967296) : n < 2 ^ (8 * bytesPerOffset) := by
  have h1 : o ≤ f + b₁ := by
    rw [← Nat.add_sub_of_le hf]
    exact Nat.add_le_add_left hs1 f
  have h2 : n ≤ f + b₁ + b₂ := by
    rw [← Nat.add_sub_of_le ho]
    exact Nat.add_le_add h1 hs2
  exact nat_lt_pow_offset (Nat.lt_of_le_of_lt h2 hsum)

def Electra.Update.fieldDescs : List Desc :=
  [electraHeaderDesc, syncCommitteeDesc, branchDesc Electra.syncCommitteeBranchLength,
    electraHeaderDesc, branchDesc Electra.finalityBranchLength, syncAggregateDesc, .uint 8]

theorem Electra.Update.fieldsFixedSize_eq :
    Desc.fieldsFixedSize fieldDescs = none := rfl

theorem Electra.Update.leadingWidth_eq :
    Desc.leadingWidth fieldDescs = Electra.Update.fixedSize := rfl

theorem Electra.Update.readSlots_ok (bs : ByteArray) (s2 s3 s5 s6 s7 : Bytes) (o₁ o₂ : Nat)
    (ho1 : readUint bs.data 0 4 = o₁)
    (ho2 : readUint bs.data finalizedOffsetAt 4 = o₂)
    (hs2 : bs.data.extract 4 (4 + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (4 + SyncCommittee.size) finalizedOffsetAt = s3)
    (hs5 : bs.data.extract (finalizedOffsetAt + 4)
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) = s5)
    (hs6 : bs.data.extract (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength)
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size)
      fixedSize = s7)
    (hle : fixedSize ≤ bs.data.size) :
    readSlots fieldDescs bs.data 0 =
      .ok ([.body o₁, .inline s2, .inline s3, .body o₂,
        .inline s5, .inline s6, .inline s7], fixedSize) := by
  have heh : electraHeaderDesc.fixedSize = none := rfl
  have hsc : syncCommitteeDesc.fixedSize = some SyncCommittee.size := rfl
  have hcbr : (branchDesc Electra.syncCommitteeBranchLength).fixedSize =
      some (32 * Electra.syncCommitteeBranchLength) := rfl
  have hfbr : (branchDesc Electra.finalityBranchLength).fixedSize =
      some (32 * Electra.finalityBranchLength) := rfl
  have hagg : syncAggregateDesc.fixedSize = some SyncAggregate.size := rfl
  have hw1 : 0 + 4 ≤ bs.data.size := Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw2 : 4 + SyncCommittee.size ≤ bs.data.size := Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw3 : (4 + SyncCommittee.size) + 32 * Electra.syncCommitteeBranchLength ≤ bs.data.size :=
    Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw4 : finalizedOffsetAt + 4 ≤ bs.data.size := Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw5 : (finalizedOffsetAt + 4) + 32 * Electra.finalityBranchLength ≤ bs.data.size :=
    Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw6 : (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) + SyncAggregate.size ≤
      bs.data.size :=
    Nat.le_trans (Nat.le_of_ble_eq_true rfl) hle
  have hw7 : (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) + 8 ≤
      bs.data.size := hle
  have he1 : 4 + SyncCommittee.size + 32 * Electra.syncCommitteeBranchLength =
      finalizedOffsetAt := rfl
  unfold fieldDescs
  rw [← ho1, ← ho2, ← hs2, ← hs3, ← hs5, ← hs6, ← hs7,
    readSlots_var_cons heh hw1, Nat.zero_add,
    readSlots_fixed_cons hsc hw2,
    readSlots_fixed_cons hcbr hw3, he1,
    readSlots_var_cons heh hw4,
    readSlots_fixed_cons hfbr hw5,
    readSlots_fixed_cons hagg hw6,
    readSlots_fixed_cons (w := 8) rfl hw7,
    readSlots_nil]
  rfl

theorem Electra.Update.takeSlots_ok (bs : ByteArray) (s1 s2 s3 s4 s5 s6 s7 : Bytes) (o₁ o₂ : Nat)
    (hs1 : bs.data.extract fixedSize o₂ = s1)
    (hs4 : bs.data.extract o₂ bs.data.size = s4)
    (_hle : fixedSize ≤ bs.data.size) (ho1 : o₁ = fixedSize)
    (ho2 : fixedSize ≤ o₂) (ho3 : o₂ ≤ bs.data.size) :
    takeSlots bs.data
      [.body o₁, .inline s2, .inline s3, .body o₂, .inline s5, .inline s6, .inline s7]
      [o₂ - o₁, bs.data.size - o₂] =
      .ok [s1, s2, s3, s4, s5, s6, s7] := by
  rw [ho1]
  exact takeSlots_body (Nat.add_sub_of_le ho2) hs1
    (takeSlots_inline (takeSlots_inline
      (takeSlots_body (Nat.add_sub_of_le ho3) hs4
        (takeSlots_inline (takeSlots_inline (takeSlots_inline (takeSlots_nil _ _)))))))

theorem Electra.Update.decode_iff_core (bs : ByteArray) (x : Electra.Update)
    (s1 s2 s3 s4 s5 s6 s7 : Bytes) (o₁ o₂ : Nat)
    (sc0 : SyncCommittee) (cbr fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (ho1_eq : readUint bs.data 0 4 = o₁)
    (ho2_eq : readUint bs.data finalizedOffsetAt 4 = o₂)
    (hs1 : bs.data.extract fixedSize o₂ = s1)
    (hs2 : bs.data.extract 4 (4 + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (4 + SyncCommittee.size) finalizedOffsetAt = s3)
    (hs4 : bs.data.extract o₂ bs.data.size = s4)
    (hs5 : bs.data.extract (finalizedOffsetAt + 4)
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) = s5)
    (hs6 : bs.data.extract (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength)
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size)
      fixedSize = s7)
    (hsc0 : SyncCommittee.read (slice bs 4 SyncCommittee.size) = sc0)
    (hcbr : roots bs (4 + SyncCommittee.size) Electra.syncCommitteeBranchLength = cbr)
    (hfbr : roots bs (finalizedOffsetAt + 4) Electra.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read
      (slice bs (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) SyncAggregate.size) = agg)
    (hsig : u64 bs
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) = sig) :
    decode bs = some x ↔ deserialize electraUpdateDesc bs.data = .ok x.toValue ∧ x.Fits := by
  have heq : electraUpdateDesc =
      .container ["attested_header", "next_sync_committee", "next_sync_committee_branch",
        "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]
        fieldDescs := rfl
  have hoff0 : offsetAt bs 0 = o₁ := (offsetAt_eq_readUint bs 0).trans ho1_eq
  have hoff2 : offsetAt bs finalizedOffsetAt = o₂ :=
    (offsetAt_eq_readUint bs finalizedOffsetAt).trans ho2_eq
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs finalizedOffsetAt ∧ offsetAt bs finalizedOffsetAt ≤ bs.size
  · have ho1 : o₁ = fixedSize := hoff0.symm.trans hc.2.1
    have ho2 : fixedSize ≤ o₂ := hoff2 ▸ hc.2.2.1
    have ho3 : o₂ ≤ bs.data.size := hoff2 ▸ hc.2.2.2
    have hsc_des : deserialize syncCommitteeDesc s2 = .ok sc0.toValue := by
      have hle : 4 + SyncCommittee.size ≤ bs.size :=
        Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
      have h := SyncCommittee.deserialize_slice bs 4 hle
      rwa [hsc0, hs2] at h
    have hcbr_des : deserialize (branchDesc Electra.syncCommitteeBranchLength) s3 =
        .ok (branchValue cbr) := by
      have hle : (4 + SyncCommittee.size) + 32 * Electra.syncCommitteeBranchLength ≤ bs.size :=
        Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
      have h := deserialize_branch_slice bs (4 + SyncCommittee.size)
        Electra.syncCommitteeBranchLength (nat_lt_of_ble rfl) hle
      change deserialize (branchDesc Electra.syncCommitteeBranchLength)
        (bs.data.extract (4 + SyncCommittee.size) finalizedOffsetAt) = .ok (branchValue _) at h
      rwa [hcbr, hs3] at h
    have hfbr_des : deserialize (branchDesc Electra.finalityBranchLength) s5 =
        .ok (branchValue fbr) := by
      have hle : (finalizedOffsetAt + 4) + 32 * Electra.finalityBranchLength ≤ bs.size :=
        Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
      have h := deserialize_branch_slice bs (finalizedOffsetAt + 4)
        Electra.finalityBranchLength (nat_lt_of_ble rfl) hle
      rwa [hfbr, hs5] at h
    have hagg_des : deserialize syncAggregateDesc s6 = .ok agg.toValue := by
      have hle : (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) +
          SyncAggregate.size ≤ bs.size :=
        Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
      have h := SyncAggregate.deserialize_slice bs
        (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) hle
      rw [← hs6, ← hagg]; exact h
    have hsig_des : deserialize (.uint 8) s7 = .ok (.uint sig) := by
      have h := deserialize_uint_slice bs
        (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) 8 hc.1
      rw [← hs7, ← hsig]; exact h
    cases hatt : Header.decode (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt)) with
    | some a =>
      have ha_des : deserialize electraHeaderDesc s1 = .ok a.toValue := by
        have h := (Header.decode_iff
          (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt)) a).mp hatt
        rw [extract_data_of_le bs fixedSize (offsetAt bs finalizedOffsetAt) hc.2.2.1 hc.2.2.2,
          hoff2] at h
        rwa [← hs1]
      cases hfin : Header.decode (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size) with
      | some f =>
        let u₀ : Electra.Update := {
          attestedHeader := a, nextSyncCommittee := sc0, nextSyncCommitteeBranch := cbr,
          finalizedHeader := f, finalityBranch := fbr, syncAggregate := agg,
          signatureSlot := sig }
        have hd : decode bs = some u₀ := by
          unfold decode; dsimp only
          rw [ite_eq_left hc, hatt, hfin]
          dsimp only
          rw [hsc0, hcbr, hfbr, hagg, hsig]
        have hfu₀ : u₀.Fits := decode_fits hd
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := by
          have hlea := Header.decode_size_le hatt
          have hlef := Header.decode_size_le hfin
          rw [extract_size bs fixedSize (offsetAt bs finalizedOffsetAt) hc.2.2.1 hc.2.2.2,
            hoff2] at hlea
          rw [extract_size bs (offsetAt bs finalizedOffsetAt) bs.size hc.2.2.2 (Nat.le_refl _),
            hoff2] at hlef
          exact size_lt_of_two_sub_le ho2 ho3 hlea hlef (nat_lt_of_ble rfl)
        have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho1 ho2 ho3
          (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
          (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4)
        have hf_des : deserialize electraHeaderDesc s4 = .ok f.toValue := by
          have h := (Header.decode_iff
            (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size) f).mp hfin
          rw [extract_data_of_le bs (offsetAt bs finalizedOffsetAt) bs.size hc.2.2.2 (Nat.le_refl _),
            hoff2] at h
          rwa [← hs4]
        have hdf := deserializeFields_cons_ok ha_des
          (deserializeFields_cons_ok hsc_des
            (deserializeFields_cons_ok hcbr_des
              (deserializeFields_cons_ok hf_des
                (deserializeFields_cons_ok hfbr_des
                  (deserializeFields_cons_ok hagg_des
                    (deserializeFields_cons_ok hsig_des deserializeFields_nil))))))
        rw [hd, heq, deserialize_container_ok_of_slices hsl hdf x.toValue]
        have htv : u₀.toValue = .seq [a.toValue, sc0.toValue, branchValue cbr, f.toValue,
            branchValue fbr, agg.toValue, .uint sig] := rfl
        rw [← htv]
        refine ⟨fun h => ?_, fun ⟨hv, hfx⟩ => congrArg some (toValue_inj hfu₀ hfx hv.symm)⟩
        have h' : x = u₀ := (Option.some.inj h).symm
        exact ⟨congrArg toValue h', h' ▸ hfu₀⟩
      | none =>
        have hd : decode bs = none := by
          unfold decode; dsimp only; rw [ite_eq_left hc, hatt, hfin]
        rw [hd, heq]
        constructor
        · intro h; cases h
        · rintro ⟨hdes, _⟩
          have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
          have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
            hov hc.1 ho1 ho2 ho3
            (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
            (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4)
          have hf_err : (deserialize electraHeaderDesc s4).isOk = false := by
            have his := Header.deserialize_isSome
              (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size)
            rw [hfin, extract_data_of_le bs (offsetAt bs finalizedOffsetAt) bs.size
              hc.2.2.2 (Nat.le_refl _), hoff2] at his
            rw [← hs4]; exact his.symm
          have hbad := deserialize_container_isOk_false_of_fields
            (names := ["attested_header", "next_sync_committee", "next_sync_committee_branch",
              "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]) hsl
            (deserializeFields_isOk_false_tail ha_des
              (deserializeFields_isOk_false_tail hsc_des
                (deserializeFields_isOk_false_tail hcbr_des
                  (deserializeFields_isOk_false_head hf_err))))
          rw [hdes] at hbad; cases hbad
    | none =>
      have hd : decode bs = none := by
        unfold decode; dsimp only; rw [ite_eq_left hc, hatt]
      rw [hd, heq]
      constructor
      · intro h; cases h
      · rintro ⟨hdes, _⟩
        have hov : bs.data.size < 2 ^ (8 * bytesPerOffset) := deserialize_size_lt hdes
        have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho1 ho2 ho3
          (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
          (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4)
        have ha_err : (deserialize electraHeaderDesc s1).isOk = false := by
          have his := Header.deserialize_isSome
            (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt))
          rw [hatt, extract_data_of_le bs fixedSize (offsetAt bs finalizedOffsetAt)
            hc.2.2.1 hc.2.2.2, hoff2] at his
          rw [← hs1]; exact his.symm
        have hbad := deserialize_container_isOk_false_of_fields
          (names := ["attested_header", "next_sync_committee", "next_sync_committee_branch",
            "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]) hsl
          (deserializeFields_isOk_false_head ha_err)
        rw [hdes] at hbad; cases hbad
  · have hd : decode bs = none := by unfold decode; dsimp only; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ o₁ = fixedSize ∧ fixedSize ≤ o₂ ∧ o₂ ≤ bs.data.size) :=
      fun ⟨_, h1, h2, h3, h4⟩ => hc ⟨h1, hoff0.trans h2, hoff2.symm ▸ h3, hoff2.symm ▸ h4⟩
    have herr := deserialize_container_var2_reject
      (names := ["attested_header", "next_sync_committee", "next_sync_committee_branch",
        "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"])
      fieldsFixedSize_eq leadingWidth_eq
      (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
      (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4) hbad
    rw [hd, heq]
    constructor
    · intro h; cases h
    · rintro ⟨hdes, _⟩; rw [hdes] at herr; cases herr

theorem Electra.Update.decode_iff (bs : ByteArray) (x : Electra.Update) :
    decode bs = some x ↔ deserialize electraUpdateDesc bs.data = .ok x.toValue ∧ x.Fits :=
  decode_iff_core bs x _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem Electra.Update.deserialize_eq_of_fits (bs : ByteArray)
    {x : Electra.Update} (hx : x.Fits) :
    decode bs = some x ↔ deserialize electraUpdateDesc bs.data = .ok x.toValue := by
  rw [decode_iff]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

theorem Electra.Update.deserialize_isSome_core (bs : ByteArray)
    (s1 s2 s3 s4 s5 s6 s7 : Bytes) (o₁ o₂ : Nat)
    (sc0 : SyncCommittee) (cbr fbr : Array ByteArray) (agg : SyncAggregate) (sig : Nat)
    (ho1_eq : readUint bs.data 0 4 = o₁)
    (ho2_eq : readUint bs.data finalizedOffsetAt 4 = o₂)
    (hs1 : bs.data.extract fixedSize o₂ = s1)
    (hs2 : bs.data.extract 4 (4 + SyncCommittee.size) = s2)
    (hs3 : bs.data.extract (4 + SyncCommittee.size) finalizedOffsetAt = s3)
    (hs4 : bs.data.extract o₂ bs.data.size = s4)
    (hs5 : bs.data.extract (finalizedOffsetAt + 4)
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) = s5)
    (hs6 : bs.data.extract (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength)
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) = s6)
    (hs7 : bs.data.extract
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size)
      fixedSize = s7)
    (hsc0 : SyncCommittee.read (slice bs 4 SyncCommittee.size) = sc0)
    (hcbr : roots bs (4 + SyncCommittee.size) Electra.syncCommitteeBranchLength = cbr)
    (hfbr : roots bs (finalizedOffsetAt + 4) Electra.finalityBranchLength = fbr)
    (hagg : SyncAggregate.read
      (slice bs (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength) SyncAggregate.size) = agg)
    (hsig : u64 bs
      (finalizedOffsetAt + 4 + 32 * Electra.finalityBranchLength + SyncAggregate.size) = sig) :
    (decode bs).isSome = (deserialize electraUpdateDesc bs.data).isOk := by
  have heq : electraUpdateDesc =
      .container ["attested_header", "next_sync_committee", "next_sync_committee_branch",
        "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]
        fieldDescs := rfl
  have hoff0 : offsetAt bs 0 = o₁ := (offsetAt_eq_readUint bs 0).trans ho1_eq
  have hoff2 : offsetAt bs finalizedOffsetAt = o₂ :=
    (offsetAt_eq_readUint bs finalizedOffsetAt).trans ho2_eq
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs finalizedOffsetAt ∧ offsetAt bs finalizedOffsetAt ≤ bs.size
  · have ho1 : o₁ = fixedSize := hoff0.symm.trans hc.2.1
    have ho2 : fixedSize ≤ o₂ := hoff2 ▸ hc.2.2.1
    have ho3 : o₂ ≤ bs.data.size := hoff2 ▸ hc.2.2.2
    cases hatt : Header.decode (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt)) with
    | some a =>
      cases hfin : Header.decode (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size) with
      | some f =>
        have hd : decode bs = some {
            attestedHeader := a, nextSyncCommittee := sc0, nextSyncCommitteeBranch := cbr,
            finalizedHeader := f, finalityBranch := fbr, syncAggregate := agg,
            signatureSlot := sig } := by
          unfold decode; dsimp only
          rw [ite_eq_left hc, hatt, hfin]
          dsimp only
          rw [hsc0, hcbr, hfbr, hagg, hsig]
        rw [hd, ((decode_iff bs _).mp hd).1]; rfl
      | none =>
        have hd : decode bs = none := by
          unfold decode; dsimp only; rw [ite_eq_left hc, hatt, hfin]
        rw [hd, heq]
        by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
        · have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
            hov hc.1 ho1 ho2 ho3
            (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
            (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4)
          have ha_des : deserialize electraHeaderDesc s1 = .ok a.toValue := by
            have h := (Header.decode_iff
              (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt)) a).mp hatt
            rw [extract_data_of_le bs fixedSize (offsetAt bs finalizedOffsetAt) hc.2.2.1 hc.2.2.2,
              hoff2] at h
            rwa [← hs1]
          have hsc_des : deserialize syncCommitteeDesc s2 = .ok sc0.toValue := by
            have hle : 4 + SyncCommittee.size ≤ bs.size :=
              Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
            have h := SyncCommittee.deserialize_slice bs 4 hle
            rwa [hsc0, hs2] at h
          have hcbr_des : deserialize (branchDesc Electra.syncCommitteeBranchLength) s3 =
              .ok (branchValue cbr) := by
            have hle : (4 + SyncCommittee.size) + 32 * Electra.syncCommitteeBranchLength ≤
                bs.size :=
              Nat.le_trans (Nat.le_of_ble_eq_true rfl) hc.1
            have h := deserialize_branch_slice bs (4 + SyncCommittee.size)
              Electra.syncCommitteeBranchLength (nat_lt_of_ble rfl) hle
            change deserialize (branchDesc Electra.syncCommitteeBranchLength)
              (bs.data.extract (4 + SyncCommittee.size) finalizedOffsetAt) = .ok (branchValue _) at h
            rwa [hcbr, hs3] at h
          have hf_err : (deserialize electraHeaderDesc s4).isOk = false := by
            have his := Header.deserialize_isSome
              (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size)
            rw [hfin, extract_data_of_le bs (offsetAt bs finalizedOffsetAt) bs.size
              hc.2.2.2 (Nat.le_refl _), hoff2] at his
            rw [← hs4]; exact his.symm
          rw [deserialize_container_isOk_false_of_fields hsl
            (deserializeFields_isOk_false_tail ha_des
              (deserializeFields_isOk_false_tail hsc_des
                (deserializeFields_isOk_false_tail hcbr_des
                  (deserializeFields_isOk_false_head hf_err))))]
          rfl
        · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
    | none =>
      have hd : decode bs = none := by
        unfold decode; dsimp only; rw [ite_eq_left hc, hatt]
      rw [hd, heq]
      by_cases hov : bs.data.size < 2 ^ (8 * bytesPerOffset)
      · have hsl := deserialize_container_var2_slices fieldsFixedSize_eq leadingWidth_eq
          hov hc.1 ho1 ho2 ho3
          (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
          (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4)
        have ha_err : (deserialize electraHeaderDesc s1).isOk = false := by
          have his := Header.deserialize_isSome
            (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt))
          rw [hatt, extract_data_of_le bs fixedSize (offsetAt bs finalizedOffsetAt)
            hc.2.2.1 hc.2.2.2, hoff2] at his
          rw [← hs1]; exact his.symm
        rw [deserialize_container_isOk_false_of_fields hsl
          (deserializeFields_isOk_false_head ha_err)]; rfl
      · rw [deserialize_overflow (Nat.not_lt.mp hov)]; rfl
  · have hd : decode bs = none := by unfold decode; dsimp only; rw [ite_eq_right hc]
    have hbad : ¬ (bs.data.size < 2 ^ (8 * bytesPerOffset) ∧
        fixedSize ≤ bs.data.size ∧ o₁ = fixedSize ∧ fixedSize ≤ o₂ ∧ o₂ ≤ bs.data.size) :=
      fun ⟨_, h1, h2, h3, h4⟩ => hc ⟨h1, hoff0.trans h2, hoff2.symm ▸ h3, hoff2.symm ▸ h4⟩
    rw [hd, heq, deserialize_container_var2_reject fieldsFixedSize_eq leadingWidth_eq
      (readSlots_ok bs s2 s3 s5 s6 s7 o₁ o₂ ho1_eq ho2_eq hs2 hs3 hs5 hs6 hs7)
      (fun _ => rfl) (takeSlots_ok bs s1 s2 s3 s4 s5 s6 s7 o₁ o₂ hs1 hs4) hbad]; rfl

theorem Electra.Update.deserialize_isSome (bs : ByteArray) :
    (decode bs).isSome = (deserialize electraUpdateDesc bs.data).isOk :=
  deserialize_isSome_core bs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem Electra.Update.decode_canonical {bs : ByteArray} {u : Electra.Update}
    (hd : decode bs = some u) : serialize electraUpdateDesc u.toValue = .ok bs.data :=
  decode_canonical_of_iff_fits electraUpdateDesc_wellFormed decode_iff hd

theorem Electra.Update.decode_injective_bytes {bs₁ bs₂ : ByteArray} {u : Electra.Update}
    (h₁ : decode bs₁ = some u) (h₂ : decode bs₂ = some u) : bs₁ = bs₂ :=
  decode_injective_bytes_of_iff_fits electraUpdateDesc_wellFormed decode_iff h₁ h₂

theorem Electra.Update.decode_serialize {u : Electra.Update} {data : Bytes}
    (hu : u.Fits) (hs : serialize electraUpdateDesc u.toValue = .ok data) :
    decode ⟨data⟩ = some u :=
  decode_serialize_of_iff_fits electraUpdateDesc_wellFormed deserialize_isSome decode_iff
    (fun _ _ ha hb hv => toValue_inj ha hb hv) hu hs

end LeanLight.Lc.Ssz
