import LeanLightProofs.Bls.Decompress

/-!
# BLS12-381: decoding is canonical and complete (25c)

`LeanLightProofs.Bls.Decompress` proved decoding sound (a decoded point is a reduced point of its
curve, not the identity) and unique (two encodings of one point are the same bytes). Here:

* **Completeness** (`g1Decompress?_compress`, `g2Decompress?_compress`): every reduced point of
  `E` or `E'` (affine, so not the identity) has its compression decode back to it; with
  `[r]P = O`, KeyValidate and the signature's checks accept it (`keyValidate?_compress`,
  `sigValidate?_compress`).
* **Canonicity** (`g1Decompress?_canonical`, `g2Decompress?_canonical`, and for KeyValidate and
  the signature's checks): the one encoding a decoder accepts for a point is its compression,
  `compress p`, by completeness and uniqueness.

The bytes: `natBe a n f` writes `a` big-endian in `n` bytes, `f` OR-ed into the first
(`natBe_getD`), and `beNat` reads them back (`beNat_natBe`); a coordinate below `P < 2³⁸¹` leaves
the first byte's top three bits to the flags (`flags_byte`). The root: `fsqrt?` and
`Fp2.sqrt?` find one of `±y` (the curve's equation says the argument is a square), and the sign
flag, `y`'s `fLarge` or `Fp2.large`, picks `y` (no point has `y = 0`).
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

/-! ## Bytes -/

theorem foldl_push_ofFn (f : ℕ → UInt8) : ∀ n,
    (List.range n).foldl (fun x j => x.push (f j)) ByteArray.empty =
      ⟨Array.ofFn (n := n) fun j => f j.val⟩
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_push_ofFn f n,
      Array.ofFn_succ]
    rfl

/-- `natBe a n f`: byte `i` of `a`, big-endian, `f` OR-ed into the first. -/
theorem natBe_eq (a n : ℕ) (f : UInt8) : natBe a n f =
    ⟨Array.ofFn (n := n) fun i => if i.val = 0 then (a >>> (8 * (n - 1 - i.val))).toUInt8 ||| f
      else (a >>> (8 * (n - 1 - i.val))).toUInt8⟩ := by
  unfold natBe
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  exact foldl_push_ofFn (fun i => if i = 0 then (a >>> (8 * (n - 1 - i))).toUInt8 ||| f
      else (a >>> (8 * (n - 1 - i))).toUInt8) n

theorem size_natBe (a n : ℕ) (f : UInt8) : (natBe a n f).size = n := by
  rw [natBe_eq]; simp [ByteArray.size]

theorem natBe_getD (a n : ℕ) (f : UInt8) {i : ℕ} (hi : i < n) :
    (natBe a n f)[i]?.getD 0 = if i = 0 then (a >>> (8 * (n - 1 - i))).toUInt8 ||| f
      else (a >>> (8 * (n - 1 - i))).toUInt8 := by
  rw [natBe_eq]
  have hi' : i < (ByteArray.mk (Array.ofFn (n := n) fun i => if i.val = 0 then
      (a >>> (8 * (n - 1 - i.val))).toUInt8 ||| f else (a >>> (8 * (n - 1 - i.val))).toUInt8)).size := by
    simp [ByteArray.size, hi]
  rw [getElem?_pos _ i hi', Option.getD_some]
  simp [ByteArray.getElem_eq_getElem_data]

/-- `beNat` reads back the big-endian bytes of `a`, from `a`'s bits above them. -/
theorem beNat_natBe (b : ByteArray) (off m a : ℕ)
    (hb : ∀ i < m, (b[off + i]?.getD 0).toNat = (a >>> (8 * (m - 1 - i))) % 256) :
    beNat b off m (a >>> (8 * m)) = a := by
  rw [beNat_eq_foldl]
  suffices h : ∀ k ≤ m, (List.range k).foldl (fun v i => v * 256 + (b[off + i]?.getD 0).toNat)
      (a >>> (8 * m)) = a >>> (8 * (m - k)) by
    rw [h m le_rfl, Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero]
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      hb k (by omega), show 8 * (m - k) = 8 * (m - 1 - k) + 8 by omega, Nat.shiftRight_add,
      Nat.shiftRight_eq_div_pow (a >>> (8 * (m - 1 - k))) 8,
      show 8 * (m - (k + 1)) = 8 * (m - 1 - k) by omega]
    exact Nat.div_add_mod' _ _

theorem toNat_toUInt8 (n : ℕ) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat']

/-- The first byte of a compressed point: the coordinate's top five bits (below 32 as it is
below `P < 2³⁸¹`), the compression flag, and the sign flag `s`. -/
theorem flags_byte (t : ℕ) (ht : t < 32) (s : Bool) :
    let b0 := t.toUInt8 ||| (0x80 ||| (if s then 0x20 else 0))
    b0 &&& 128 ≠ 0 ∧ b0 &&& 64 = 0 ∧ (b0 &&& 32 ≠ 0 ↔ s = true) ∧ (b0 &&& 31).toNat = t := by
  have key : ∀ t : Fin 32, ∀ s : Bool,
      let b0 := t.val.toUInt8 ||| (0x80 ||| (if s then 0x20 else 0))
      b0 &&& 128 ≠ 0 ∧ b0 &&& 64 = 0 ∧ (b0 &&& 32 ≠ 0 ↔ s = true) ∧ (b0 &&& 31).toNat = t.val := by
    decide
  exact key ⟨t, ht⟩ s

theorem top_lt_32 {a : ℕ} (ha : a < P) : a >>> 376 < 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (ha.trans (by decide))

theorem getD_append_left (a b : ByteArray) {i : ℕ} (h : i < a.size) :
    (a ++ b)[i]?.getD 0 = a[i]?.getD 0 := by
  rw [getElem?_pos (a ++ b) i (by rw [ByteArray.size_append]; omega), getElem?_pos a i h,
    Option.getD_some, Option.getD_some, ByteArray.getElem_append_left h]

theorem getD_append_right (a b : ByteArray) {i : ℕ} (h1 : a.size ≤ i) (h2 : i < a.size + b.size) :
    (a ++ b)[i]?.getD 0 = b[i - a.size]?.getD 0 := by
  rw [getElem?_pos (a ++ b) i (by rw [ByteArray.size_append]; omega),
    getElem?_pos b (i - a.size) (by omega), Option.getD_some, Option.getD_some,
    ByteArray.getElem_append_right h1]

theorem fneg_fneg {y : ℕ} (h0 : y ≠ 0) (hy : y < P) : fneg (fneg y) = y := by
  unfold fneg; rw [ite_eq_right h0, ite_eq_right (by omega)]; omega

/-! ## G1 -/

/-- **Completeness, G1**: the compression of a reduced point of `E` (affine, so not the
identity) decodes back to it. -/
theorem g1Decompress?_compress {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    g1Decompress? p.compress = some p := by
  obtain ⟨hx, hy⟩ := hp
  have ht := top_lt_32 hx
  obtain ⟨f1, f2, f3, f4⟩ := flags_byte (p.x >>> 376) ht (fLarge p.y)
  have hs : p.compress.size = 48 := size_natBe _ _ _
  have hb0 : p.compress[0]?.getD 0 =
      (p.x >>> 376).toUInt8 ||| (0x80 ||| (if fLarge p.y then 0x20 else 0)) := by
    rw [G1A.compress, natBe_getD _ _ _ (by decide : 0 < 48)]; rfl
  have hbx : beNat p.compress 1 47 (p.x >>> 376) = p.x := by
    have := beNat_natBe p.compress 1 47 p.x (fun i hi => by
      rw [G1A.compress, natBe_getD _ _ _ (by omega), ite_eq_right (by omega), toNat_toUInt8]
      congr 3; omega)
    rwa [show 8 * 47 = 376 from rfl] at this
  rw [g1Decompress?_eq, hb0, f4, hbx, ite_eq_right (by rw [hs]; exact fun h => h rfl),
    ite_eq_right f1, ite_eq_right (fun h => h f2), ite_eq_right (by omega)]
  have hn' := hn
  rw [G1A.toJ, E1_nonsingular_iff] at hn'
  have hsq : IsSquare ((fadd (fmul (fsqr p.x) p.x) 4 : ℕ) : GFp) := ⟨p.y, by
    fp_push; push_cast; linear_combination -hn'⟩
  obtain ⟨y, hyy⟩ := Option.isSome_iff_exists.mp ((fsqrt?_isSome_iff _).mpr hsq)
  rw [hyy, Option.elim_some]
  obtain ⟨hylt, hy2⟩ := fsqrt?_some hyy
  have hy0 : p.y ≠ 0 := by
    intro h0
    exact E1_y_ne_zero (x := (p.x : GFp)) (y := (p.y : GFp)) hn' (by rw [h0, Nat.cast_zero])
  have hpm : y = p.y ∨ y = fneg p.y := by
    have h : ((y : ℕ) : GFp) * y = (p.y : GFp) * p.y := by
      rw [hy2]; fp_push; push_cast; linear_combination -hn'
    have h' : ((y : ℕ) : GFp) = p.y ∨ ((y : ℕ) : GFp) = -(p.y : GFp) := by
      have : ((y : GFp) - p.y) * ((y : GFp) + p.y) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with e | e
      · left; linear_combination e
      · right; linear_combination e
    rcases h' with e | e
    · left; exact (cast_inj hylt hy).mp e
    · right; rw [← cast_fneg hy.le] at e; exact (cast_inj hylt (fneg_lt hy)).mp e
  have hdec : decide ((((p.x >>> 376).toUInt8 ||| (0x80 ||| (if fLarge p.y then 0x20 else 0))) &&&
      32) ≠ 0) = fLarge p.y := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact f3
  rw [hdec]
  rcases hpm with rfl | rfl
  · rw [ite_eq_left (by simp)]
  · rw [fLarge_fneg hy0 hy, ite_eq_right (by cases fLarge p.y <;> simp), fneg_fneg hy0 hy]

/-- **Canonicity, G1**: the one encoding `g1Decompress?` accepts for a point is its compression. -/
theorem g1Decompress?_canonical {b : ByteArray} {p : G1A} (h : g1Decompress? b = some p) :
    b = p.compress := by
  obtain ⟨hr, hn, -⟩ := g1Decompress?_some h
  exact g1Decompress?_inj h (g1Decompress?_compress hr hn)

/-- **KeyValidate is complete**: the compression of a reduced point of `E` with `[r]P = O` (a
point of G1 other than the identity) passes KeyValidate, as that point. -/
theorem keyValidate?_compress {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ)
    (hr : R • Point.toAffine E1 p.toJ = 0) : keyValidate? p.compress = some p := by
  unfold keyValidate?
  rw [G1J.compress_match_1, g1Decompress?_compress hp hn, Option.elim_some,
    ite_eq_left ((G1A.inSubgroupFast_eq hp hn).trans ((G1A.inSubgroup_iff hp hn).mpr hr))]

/-- **KeyValidate is canonical**: it accepts for a point only that point's compression. -/
theorem keyValidate?_canonical {b : ByteArray} {p : G1A} (h : keyValidate? b = some p) :
    b = p.compress :=
  g1Decompress?_canonical (keyValidate?_some h).1

/-! ## G2 -/

theorem Fp2.neg_neg' {y : Fp2} (hy : y.Reduced) : y.neg.neg = y := by
  rw [← Fp2.toGF_inj (Fp2.reduced_neg (Fp2.reduced_neg hy)) hy,
    Fp2.toGF_neg (Fp2.reduced_neg hy), Fp2.toGF_neg hy, neg_neg]

/-- **Completeness, G2**: the compression of a reduced point of `E'` (affine, so not the
identity) decodes back to it. -/
theorem g2Decompress?_compress {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    g2Decompress? p.compress = some p := by
  obtain ⟨⟨hx0, hx1⟩, hy⟩ := hp
  have ht := top_lt_32 hx1
  obtain ⟨f1, f2, f3, f4⟩ := flags_byte (p.x.c1 >>> 376) ht p.y.large
  have hA : (natBe p.x.c1 48 (0x80 ||| (if p.y.large then 0x20 else 0))).size = 48 :=
    size_natBe _ _ _
  have hB : (natBe p.x.c0 48).size = 48 := size_natBe _ _ _
  have hs : p.compress.size = 96 := by rw [G2A.compress, ByteArray.size_append, hA, hB]
  have hb0 : p.compress[0]?.getD 0 =
      (p.x.c1 >>> 376).toUInt8 ||| (0x80 ||| (if p.y.large then 0x20 else 0)) := by
    rw [G2A.compress, getD_append_left _ _ (by rw [hA]; decide),
      natBe_getD _ _ _ (by decide : 0 < 48)]; rfl
  have hbx1 : beNat p.compress 1 47 (p.x.c1 >>> 376) = p.x.c1 := by
    have := beNat_natBe p.compress 1 47 p.x.c1 (fun i hi => by
      rw [G2A.compress, getD_append_left _ _ (by rw [hA]; omega), natBe_getD _ _ _ (by omega),
        ite_eq_right (by omega), toNat_toUInt8]
      congr 3; omega)
    rwa [show 8 * 47 = 376 from rfl] at this
  have hbx0 : beNat p.compress 48 48 = p.x.c0 := by
    have h0 : p.x.c0 >>> (8 * 48) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (hx0.trans (by decide))
    have := beNat_natBe p.compress 48 48 p.x.c0 (fun i hi => by
      rw [G2A.compress, getD_append_right _ _ (by rw [hA]; omega) (by rw [hA, hB]; omega), hA,
        show 48 + i - 48 = i by omega, natBe_getD _ _ _ hi]
      by_cases hi0 : i = 0
      · subst hi0; rw [ite_eq_left rfl, show (0 : UInt8) = 0 from rfl]
        simp
      · rw [ite_eq_right hi0, toNat_toUInt8])
    rwa [h0] at this
  rw [g2Decompress?_eq, hb0, f4, hbx1, hbx0, ite_eq_right (by rw [hs]; exact fun h => h rfl),
    ite_eq_right f1, ite_eq_right (fun h => h f2),
    ite_eq_right (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; omega)]
  have hpx : (⟨p.x.c0, p.x.c1⟩ : Fp2) = p.x := rfl
  rw [hpx]
  have hx : p.x.Reduced := ⟨hx0, hx1⟩
  have hn' := hn
  rw [G2A.toJ, E2_nonsingular_iff] at hn'
  have hrhs : ((p.x.sqr.mul p.x).add bTwist).Reduced :=
    Fp2.reduced_add Fp2.reduced_mul ⟨by decide, by decide⟩
  have hrv : ((p.x.sqr.mul p.x).add bTwist).toGF = p.y.toGF * p.y.toGF := by
    rw [Fp2.toGF_add, Fp2.toGF_mul Fp2.reduced_sqr hx, Fp2.toGF_sqr hx, toGF_bTwist]
    linear_combination -hn'
  obtain ⟨y, hyy⟩ := Option.isSome_iff_exists.mp
    ((Fp2.sqrt?_isSome_iff hrhs).mpr ⟨p.y.toGF, hrv⟩)
  rw [hyy, Option.elim_some]
  obtain ⟨hyr, hy2⟩ := Fp2.sqrt?_some hrhs hyy
  have hy0 : p.y ≠ Fp2.zero := by
    intro h0
    exact E2_y_ne_zero (x := p.x.toGF) (y := p.y.toGF) hn' (by rw [h0, Fp2.toGF_zero])
  have hpm : y = p.y ∨ y = p.y.neg := by
    have h' : y.toGF = p.y.toGF ∨ y.toGF = -p.y.toGF := by
      have : (y.toGF - p.y.toGF) * (y.toGF + p.y.toGF) = 0 := by
        linear_combination hy2.trans hrv
      rcases mul_eq_zero.mp this with e | e
      · left; linear_combination e
      · right; linear_combination e
    rcases h' with e | e
    · left; exact (Fp2.toGF_inj hyr hy).mp e
    · right; rw [← Fp2.toGF_neg hy] at e; exact (Fp2.toGF_inj hyr (Fp2.reduced_neg hy)).mp e
  have hdec : decide ((((p.x.c1 >>> 376).toUInt8 ||| (0x80 ||| (if p.y.large then 0x20 else 0))) &&&
      32) ≠ 0) = p.y.large := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact f3
  rw [hdec]
  rcases hpm with rfl | rfl
  · rw [ite_eq_left (by simp)]
  · rw [Fp2.large_neg hy hy0, ite_eq_right (by cases p.y.large <;> simp), Fp2.neg_neg' hy]

/-- **Canonicity, G2**: the one encoding `g2Decompress?` accepts for a point is its compression. -/
theorem g2Decompress?_canonical {b : ByteArray} {q : G2A} (h : g2Decompress? b = some q) :
    b = q.compress := by
  obtain ⟨hr, hn, -⟩ := g2Decompress?_some h
  exact g2Decompress?_inj h (g2Decompress?_compress hr hn)

/-- **The signature's checks are complete**: the compression of a reduced point of `E'` with
`[r]Q = O` (a point of G2 other than the identity) passes them, as that point. -/
theorem sigValidate?_compress {q : G2A} (hq : q.Reduced) (hn : E2.Nonsingular q.toJ)
    (hr : R • Point.toAffine E2 q.toJ = 0) : sigValidate? q.compress = some q := by
  unfold sigValidate?
  rw [G2J.compress_match_1, g2Decompress?_compress hq hn, Option.elim_some,
    ite_eq_left ((G2A.inSubgroupPsi_eq hq hn).trans ((G2A.inSubgroup_iff hq hn).mpr hr))]

/-- **The signature's checks are canonical**: they accept for a point only its compression. -/
theorem sigValidate?_canonical {b : ByteArray} {q : G2A} (h : sigValidate? b = some q) :
    b = q.compress :=
  g2Decompress?_canonical (sigValidate?_some h).1

end LeanLight.Lc.Bls
