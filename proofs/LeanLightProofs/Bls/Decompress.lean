import LeanLightProofs.Bls.ScottComplete
import LeanLight.Bls.Compress

/-!
# BLS12-381: what decompression, KeyValidate and the signature's checks accept (25c)

Soundness of the runtime's decoders (`LeanLight.Bls.Compress`), on any bytes:

* `g1Decompress?_some`, `g2Decompress?_some`: a decoded point has reduced coordinates and is on
  its curve (`E`, `E'`), hence nonsingular, and is not the identity (an affine point; its
  `Point.toAffine` is not `0`).
* `keyValidate?_some`, `sigValidate?_some`: KeyValidate and the signature's checks accept only
  such points with `[r]P = O`, so points of the order-`r` subgroup other than the identity.
* `keyValidate?_identity`, `sigValidate?_identity`: the identity's canonical encodings are
  refused, by the kernel.
* `g1Decompress?_inj`, `g2Decompress?_inj`: decoding is unique (below).

Uniqueness, on any bytes: two byte strings a decoder takes to the same point are equal
(`g1Decompress?_inj`, `g2Decompress?_inj`): a decoded point fixes the flags (compression set,
identity clear, the sign flag `y`'s `fLarge` or `Fp2.large`, since no point of `E` or `E'` has
`y = 0`, `E1_y_ne_zero`, `E2_y_ne_zero`), and `x` fixes the remaining bits (`beNat` is base 256,
`foldl_bytes_inj`). That the one encoding accepted is `p.compress`, and that every point's
compression decodes (completeness), is not proved here (`natBe`'s side of the round trip is left;
see `docs/INVARIANTS.md` 25c).

The decoders' matches are rewritten to `Option.elim` first (`g1Decompress?_eq` and the like):
reducing them in place has the kernel evaluate `Nat.powMod` on a symbolic argument.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

set_option linter.auxLemma false in
theorem g1Decompress?_match_1 {β : Type} (x : Option ℕ) (n : Unit → β) (f : ℕ → β) :
    g1Decompress?.match_1 (fun _ => β) x n f = x.elim (n ()) f := by cases x <;> rfl

set_option linter.auxLemma false in
theorem g2Decompress?_match_1 {β : Type} (x : Option Fp2) (n : Unit → β) (f : Fp2 → β) :
    g2Decompress?.match_1 (fun _ => β) x n f = x.elim (n ()) f := by cases x <;> rfl

set_option linter.auxLemma false in
theorem G1J.compress_match_1 {β : Type} (x : Option G1A) (f : G1A → β) (n : Unit → β) :
    G1J.compress.match_1 (fun _ => β) x f n = x.elim (n ()) f := by cases x <;> rfl

set_option linter.auxLemma false in
theorem G2J.compress_match_1 {β : Type} (x : Option G2A) (f : G2A → β) (n : Unit → β) :
    G2J.compress.match_1 (fun _ => β) x f n = x.elim (n ()) f := by cases x <;> rfl

/-- `g1Decompress?` with its match as `Option.elim`. -/
theorem g1Decompress?_eq (b : ByteArray) : g1Decompress? b =
    if b.size ≠ 48 then none
    else if (b[0]?.getD 0) &&& 128 = 0 then none
    else if (b[0]?.getD 0) &&& 64 ≠ 0 then none
    else if beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat ≥ P then none
    else (fsqrt? (fadd (fmul (fsqr (beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat))
        (beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat)) 4)).elim none fun y =>
      some ⟨beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat,
        if (fLarge y == decide ((b[0]?.getD 0) &&& 32 ≠ 0)) = true then y else fneg y⟩ := by
  unfold g1Decompress?
  simp (config := { iota := false, zeta := true, beta := false, proj := false, decide := false })
    only [g1Decompress?_match_1]

/-- What `g1Decompress?` returns is a reduced point of `E`, so not the identity. -/
theorem g1Decompress?_some {b : ByteArray} {p : G1A} (h : g1Decompress? b = some p) :
    p.Reduced ∧ E1.Nonsingular p.toJ ∧ Point.toAffine E1 p.toJ ≠ 0 := by
  rw [g1Decompress?_eq] at h
  generalize hx : beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = x at h
  generalize decide ((b[0]?.getD 0) &&& 32 ≠ 0) = sign at h
  split_ifs at h with h1 h2 h3 h4
  cases hy : fsqrt? (fadd (fmul (fsqr x) x) 4) with
  | none => rw [hy, Option.elim_none] at h; cases h
  | some y =>
    rw [hy, Option.elim_some] at h
    cases h
    obtain ⟨hylt, hyy⟩ := fsqrt?_some hy
    have hxlt : x < P := by omega
    have hred : (⟨x, if (fLarge y == sign) = true then y else fneg y⟩ : G1A).Reduced :=
      ⟨hxlt, by split <;> fp_lt⟩
    have hn : E1.Nonsingular (G1A.toJ ⟨x, if (fLarge y == sign) = true then y else fneg y⟩) := by
      rw [G1A.toJ, E1_nonsingular_iff]
      fp_push at hyy
      split
      · linear_combination hyy
      · rw [cast_fneg hylt.le]; linear_combination hyy
    refine ⟨hred, hn, ?_⟩
    rw [G1A.toJ, Point.toAffine_some hn]
    exact Affine.Point.some_ne_zero _

/-- `g2Decompress?` with its match as `Option.elim`. -/
theorem g2Decompress?_eq (b : ByteArray) : g2Decompress? b =
    if b.size ≠ 96 then none
    else if (b[0]?.getD 0) &&& 128 = 0 then none
    else if (b[0]?.getD 0) &&& 64 ≠ 0 then none
    else if (decide (beNat b 48 48 ≥ P) || decide (beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat ≥ P))
        = true then none
    else ((((⟨beNat b 48 48, beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat⟩ : Fp2).sqr.mul
        ⟨beNat b 48 48, beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat⟩).add bTwist).sqrt?).elim
      none fun y =>
      some ⟨⟨beNat b 48 48, beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat⟩,
        if (y.large == decide ((b[0]?.getD 0) &&& 32 ≠ 0)) = true then y else y.neg⟩ := by
  unfold g2Decompress?
  simp (config := { iota := false, zeta := true, beta := false, proj := false, decide := false })
    only [g2Decompress?_match_1]

/-- What `g2Decompress?` returns is a reduced point of `E'`, so not the identity. -/
theorem g2Decompress?_some {b : ByteArray} {q : G2A} (h : g2Decompress? b = some q) :
    q.Reduced ∧ E2.Nonsingular q.toJ ∧ Point.toAffine E2 q.toJ ≠ 0 := by
  rw [g2Decompress?_eq] at h
  generalize beNat b 48 48 = x0 at h
  generalize beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = x1 at h
  generalize decide ((b[0]?.getD 0) &&& 32 ≠ 0) = sign at h
  split_ifs at h with h1 h2 h3 h4
  have hx : (⟨x0, x1⟩ : Fp2).Reduced := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at h4
    exact ⟨h4.1, h4.2⟩
  have hrhs : (((⟨x0, x1⟩ : Fp2).sqr.mul ⟨x0, x1⟩).add bTwist).Reduced :=
    Fp2.reduced_add Fp2.reduced_mul ⟨by decide, by decide⟩
  cases hy : (((⟨x0, x1⟩ : Fp2).sqr.mul ⟨x0, x1⟩).add bTwist).sqrt? with
  | none => rw [hy, Option.elim_none] at h; cases h
  | some y =>
    rw [hy, Option.elim_some] at h
    cases h
    obtain ⟨hyr, hyy⟩ := Fp2.sqrt?_some hrhs hy
    have hred : (⟨⟨x0, x1⟩, if (y.large == sign) = true then y else y.neg⟩ : G2A).Reduced :=
      ⟨hx, by split; exact hyr; exact Fp2.reduced_neg hyr⟩
    have hn : E2.Nonsingular
        (G2A.toJ ⟨⟨x0, x1⟩, if (y.large == sign) = true then y else y.neg⟩) := by
      rw [G2A.toJ, E2_nonsingular_iff]
      rw [Fp2.toGF_add, Fp2.toGF_mul Fp2.reduced_sqr hx, Fp2.toGF_sqr hx, toGF_bTwist] at hyy
      split
      · linear_combination hyy
      · rw [Fp2.toGF_neg hyr]; linear_combination hyy
    refine ⟨hred, hn, ?_⟩
    rw [G2A.toJ, Point.toAffine_some hn]
    exact Affine.Point.some_ne_zero _

/-- KeyValidate (IRTF BLS §2.5) accepts only a reduced point of `E`, other than the identity,
with `[r]P = O`: a point of the order-`r` subgroup G1, decoded from the key's bytes. -/
theorem keyValidate?_some {b : ByteArray} {p : G1A} (h : keyValidate? b = some p) :
    g1Decompress? b = some p ∧ p.Reduced ∧ E1.Nonsingular p.toJ ∧
      Point.toAffine E1 p.toJ ≠ 0 ∧ R • Point.toAffine E1 p.toJ = 0 := by
  unfold keyValidate? at h
  rw [G1J.compress_match_1] at h
  cases hd : g1Decompress? b with
  | none => rw [hd, Option.elim_none] at h; cases h
  | some p' =>
    rw [hd, Option.elim_some] at h
    obtain ⟨hr, hn, hne⟩ := g1Decompress?_some hd
    split at h
    · rename_i hs
      cases h
      exact ⟨rfl, hr, hn, hne,
        (G1A.inSubgroup_iff hr hn).mp ((G1A.inSubgroupFast_eq hr hn).symm.trans hs)⟩
    · cases h

/-- The signature's checks of CoreVerify accept only a reduced point of `E'`, other than the
identity, with `[r]Q = O`: a point of the order-`r` subgroup G2, decoded from the bytes. -/
theorem sigValidate?_some {b : ByteArray} {q : G2A} (h : sigValidate? b = some q) :
    g2Decompress? b = some q ∧ q.Reduced ∧ E2.Nonsingular q.toJ ∧
      Point.toAffine E2 q.toJ ≠ 0 ∧ R • Point.toAffine E2 q.toJ = 0 := by
  unfold sigValidate? at h
  rw [G2J.compress_match_1] at h
  cases hd : g2Decompress? b with
  | none => rw [hd, Option.elim_none] at h; cases h
  | some q' =>
    rw [hd, Option.elim_some] at h
    obtain ⟨hr, hn, hne⟩ := g2Decompress?_some hd
    split at h
    · rename_i hs
      cases h
      exact ⟨rfl, hr, hn, hne,
        (G2A.inSubgroup_iff hr hn).mp ((G2A.inSubgroupPsi_eq hr hn).symm.trans hs)⟩
    · cases h

/-- The identity's canonical 48-byte encoding fails KeyValidate. -/
theorem keyValidate?_identity : keyValidate? (identityBytes 48) = none := by decide +kernel

/-- The identity's canonical 96-byte encoding fails the signature's checks. -/
theorem sigValidate?_identity : sigValidate? (identityBytes 96) = none := by decide +kernel

/-! ## Uniqueness: one encoding per point -/

/-- `beNat` as a fold. -/
theorem beNat_eq_foldl (b : ByteArray) (off n acc : ℕ) :
    beNat b off n acc = (List.range n).foldl (fun v i => v * 256 + (b[off + i]?.getD 0).toNat) acc := by
  unfold beNat
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  rfl

/-- The fold of `n` bytes from `acc`: `acc·256ⁿ` plus the bytes, and it determines them. -/
theorem foldl_bytes_inj (f g : ℕ → ℕ) (hf : ∀ i, f i < 256) (hg : ∀ i, g i < 256) :
    ∀ n (a c : ℕ),
      (List.range n).foldl (fun v i => v * 256 + f i) a =
        (List.range n).foldl (fun v i => v * 256 + g i) c →
      a = c ∧ ∀ i < n, f i = g i := by
  intro n
  induction n with
  | zero => intro a c h; simpa using h
  | succ n ih =>
    intro a c h
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil] at h
    have h1 := hf n
    have h2 := hg n
    have hlast : f n = g n := by omega
    have hdiv : (List.range n).foldl (fun v i => v * 256 + f i) a =
        (List.range n).foldl (fun v i => v * 256 + g i) c := by omega
    obtain ⟨hac, hi⟩ := ih a c hdiv
    refine ⟨hac, fun i hi' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | rfl
    · exact hi i h'
    · exact hlast



/-- `fLarge` of the negation flips, away from zero (`P` is odd). -/
theorem fLarge_fneg {y : ℕ} (h0 : y ≠ 0) (hy : y < P) : fLarge (fneg y) = !fLarge y := by
  have hP : P % 2 = 1 := by decide
  unfold fLarge fneg
  rw [ite_eq_right h0]
  by_cases h : y > (P - 1) / 2
  · simp [h]; omega
  · simp [h]; omega

/-- No point of `E` has `y = 0`: `x³ = −4` would make 2 a cube. -/
theorem E1_y_ne_zero {x y : GFp} (h : y ^ 2 = x ^ 3 + 4) : y ≠ 0 := by
  rintro rfl
  have h2 := two_ne_zero_GFp
  apply two_not_cube ((-x) * (-x) * 2⁻¹)
  have hx : (-x) ^ 3 = 4 := by linear_combination h
  have : ((-x) * (-x) * 2⁻¹) ^ 3 = ((-x) ^ 3) ^ 2 * (2⁻¹) ^ 3 := by ring
  rw [this, hx]
  field_simp
  norm_num

/-- Two arrays of bytes of one size agreeing at every index are equal. -/
theorem byteArray_ext {b b' : ByteArray} (hs : b.size = b'.size)
    (h : ∀ i < b.size, b[i]?.getD 0 = b'[i]?.getD 0) : b = b' := by
  apply ByteArray.ext
  apply Array.ext hs
  intro i hi hi'
  have := h i hi
  rw [getElem?_pos b i hi, getElem?_pos b' i (hs ▸ hi)] at this
  simpa only [Option.getD_some, ByteArray.getElem_eq_getElem_data] using this

/-- A first byte with the compression flag set and the identity flag clear is its low five bits
and its sign bit. -/
theorem flags_toNat (u : UInt8) (h1 : u &&& 128 ≠ 0) (h2 : u &&& 64 = 0) :
    u.toNat = (u &&& 31).toNat + 128 + (if u &&& 32 ≠ 0 then 32 else 0) := by
  have key : ∀ a : Fin 256, UInt8.ofNat a.val &&& 128 ≠ 0 → UInt8.ofNat a.val &&& 64 = 0 →
      (UInt8.ofNat a.val).toNat = (UInt8.ofNat a.val &&& 31).toNat + 128 +
        (if UInt8.ofNat a.val &&& 32 ≠ 0 then 32 else 0) := by decide +kernel
  have := key ⟨u.toNat, u.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h1 h2



/-- What a successful `g1Decompress?` read from its bytes: 48 of them, the compression flag set,
the identity flag clear, `x` the big-endian number after the flags, the sign flag `y`'s
`fLarge`. -/
theorem g1Decompress?_parts {b : ByteArray} {p : G1A} (h : g1Decompress? b = some p) :
    b.size = 48 ∧ (b[0]?.getD 0) &&& 128 ≠ 0 ∧ (b[0]?.getD 0) &&& 64 = 0 ∧
      beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = p.x ∧
      ((b[0]?.getD 0) &&& 32 ≠ 0 ↔ fLarge p.y = true) := by
  rw [g1Decompress?_eq] at h
  generalize hx : beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = x at h
  generalize hs : decide ((b[0]?.getD 0) &&& 32 ≠ 0) = sign at h
  split_ifs at h with h1 h2 h3 h4
  cases hy : fsqrt? (fadd (fmul (fsqr x) x) 4) with
  | none => rw [hy, Option.elim_none] at h; cases h
  | some y =>
    rw [hy, Option.elim_some] at h
    cases h
    obtain ⟨hylt, hyy⟩ := fsqrt?_some hy
    have hy0 : y ≠ 0 := by
      intro h0
      apply E1_y_ne_zero (x := (x : GFp)) (y := (y : GFp))
      · fp_push at hyy; linear_combination hyy
      · rw [h0, Nat.cast_zero]
    refine ⟨by omega, h2, by simpa using h3, rfl, ?_⟩
    have hc : ((b[0]?.getD 0) &&& 32 ≠ 0) ↔ sign = true := by
      rw [← hs]; exact decide_eq_true_iff.symm
    rw [hc]
    dsimp only
    split
    · rename_i hb; simp only [beq_iff_eq] at hb; rw [hb]
    · rename_i hb
      simp only [beq_iff_eq] at hb
      rw [fLarge_fneg hy0 hylt]
      cases sign <;> cases hf : fLarge y <;> simp_all

/-- **Decoding G1 is unique**: two byte strings that decode to the same point are the same. -/
theorem g1Decompress?_inj {b b' : ByteArray} {p : G1A} (h : g1Decompress? b = some p)
    (h' : g1Decompress? b' = some p) : b = b' := by
  obtain ⟨s, f1, f2, hx, hs⟩ := g1Decompress?_parts h
  obtain ⟨s', f1', f2', hx', hs'⟩ := g1Decompress?_parts h'
  rw [← hx', beNat_eq_foldl, beNat_eq_foldl] at hx
  obtain ⟨hlow, hbytes⟩ := foldl_bytes_inj (fun i => (b[1 + i]?.getD 0).toNat)
    (fun i => (b'[1 + i]?.getD 0).toNat) (fun _ => UInt8.toNat_lt _) (fun _ => UInt8.toNat_lt _)
    47 _ _ hx
  have h0 : b[0]?.getD 0 = b'[0]?.getD 0 := by
    apply UInt8.toNat_inj.mp
    rw [flags_toNat _ f1 f2, flags_toNat _ f1' f2', hlow]
    have : ((b[0]?.getD 0) &&& 32 ≠ 0) ↔ ((b'[0]?.getD 0) &&& 32 ≠ 0) := hs.trans hs'.symm
    by_cases hc : (b[0]?.getD 0) &&& 32 ≠ 0
    · rw [ite_eq_left hc, ite_eq_left (this.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun e => hc (this.mpr e))]
  apply byteArray_ext (s.trans s'.symm)
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact h0
  · have := hbytes (i - 1) (by omega)
    rw [show 1 + (i - 1) = i by omega] at this
    exact UInt8.toNat_inj.mp this



/-- `Fp2.large` of the negation flips, away from zero. -/
theorem Fp2.large_neg {y : Fp2} (hy : y.Reduced) (h0 : y ≠ Fp2.zero) : y.neg.large = !y.large := by
  obtain ⟨y0, y1⟩ := y
  obtain ⟨h0', h1'⟩ : y0 < P ∧ y1 < P := hy
  simp only [Fp2.large, Fp2.neg]
  by_cases h1 : y1 = 0
  · subst h1
    have hy0 : y0 ≠ 0 := fun e => h0 (by subst e; rfl)
    simp only [fneg, ite_true]
    exact fLarge_fneg hy0 h0'
  · have hne : fneg y1 ≠ 0 := by unfold fneg; rw [ite_eq_right h1]; omega
    simp only [hne, h1, ↓reduceIte]
    exact fLarge_fneg h1 h1'



/-- What a successful `g2Decompress?` read from its bytes: 96 of them, the compression flag set,
the identity flag clear, `x.c1` the big-endian number of the first 48 after the flags, `x.c0`
of the last 48, the sign flag `y`'s `Fp2.large`. -/
theorem g2Decompress?_parts {b : ByteArray} {q : G2A} (h : g2Decompress? b = some q) :
    b.size = 96 ∧ (b[0]?.getD 0) &&& 128 ≠ 0 ∧ (b[0]?.getD 0) &&& 64 = 0 ∧
      beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = q.x.c1 ∧ beNat b 48 48 = q.x.c0 ∧
      ((b[0]?.getD 0) &&& 32 ≠ 0 ↔ q.y.large = true) := by
  rw [g2Decompress?_eq] at h
  generalize beNat b 48 48 = x0 at h
  generalize beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = x1 at h
  generalize hs : decide ((b[0]?.getD 0) &&& 32 ≠ 0) = sign at h
  split_ifs at h with h1 h2 h3 h4
  have hx : (⟨x0, x1⟩ : Fp2).Reduced := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at h4
    exact ⟨h4.1, h4.2⟩
  have hrhs : (((⟨x0, x1⟩ : Fp2).sqr.mul ⟨x0, x1⟩).add bTwist).Reduced :=
    Fp2.reduced_add Fp2.reduced_mul ⟨by decide, by decide⟩
  cases hy : (((⟨x0, x1⟩ : Fp2).sqr.mul ⟨x0, x1⟩).add bTwist).sqrt? with
  | none => rw [hy, Option.elim_none] at h; cases h
  | some y =>
    rw [hy, Option.elim_some] at h
    cases h
    obtain ⟨hyr, hyy⟩ := Fp2.sqrt?_some hrhs hy
    have hy0 : y ≠ Fp2.zero := by
      intro h0
      apply E2_y_ne_zero (x := (⟨x0, x1⟩ : Fp2).toGF) (y := y.toGF)
      · rw [Fp2.toGF_add, Fp2.toGF_mul Fp2.reduced_sqr hx, Fp2.toGF_sqr hx, toGF_bTwist] at hyy
        linear_combination hyy
      · rw [h0, Fp2.toGF_zero]
    refine ⟨by omega, h2, by simpa using h3, rfl, rfl, ?_⟩
    have hc : ((b[0]?.getD 0) &&& 32 ≠ 0) ↔ sign = true := by
      rw [← hs]; exact decide_eq_true_iff.symm
    rw [hc]
    dsimp only
    split
    · rename_i hb; simp only [beq_iff_eq] at hb; rw [hb]
    · rename_i hb
      simp only [beq_iff_eq] at hb
      rw [Fp2.large_neg hyr hy0]
      cases sign <;> cases hf : y.large <;> simp_all

/-- **Decoding G2 is unique**: two byte strings that decode to the same point are the same. -/
theorem g2Decompress?_inj {b b' : ByteArray} {q : G2A} (h : g2Decompress? b = some q)
    (h' : g2Decompress? b' = some q) : b = b' := by
  obtain ⟨s, f1, f2, hx1, hx0, hs⟩ := g2Decompress?_parts h
  obtain ⟨s', f1', f2', hx1', hx0', hs'⟩ := g2Decompress?_parts h'
  rw [← hx1', beNat_eq_foldl, beNat_eq_foldl] at hx1
  rw [← hx0', beNat_eq_foldl, beNat_eq_foldl] at hx0
  obtain ⟨hlow, hbytes⟩ := foldl_bytes_inj (fun i => (b[1 + i]?.getD 0).toNat)
    (fun i => (b'[1 + i]?.getD 0).toNat) (fun _ => UInt8.toNat_lt _) (fun _ => UInt8.toNat_lt _)
    47 _ _ hx1
  obtain ⟨-, hbytes0⟩ := foldl_bytes_inj (fun i => (b[48 + i]?.getD 0).toNat)
    (fun i => (b'[48 + i]?.getD 0).toNat) (fun _ => UInt8.toNat_lt _) (fun _ => UInt8.toNat_lt _)
    48 _ _ hx0
  have h0 : b[0]?.getD 0 = b'[0]?.getD 0 := by
    apply UInt8.toNat_inj.mp
    rw [flags_toNat _ f1 f2, flags_toNat _ f1' f2', hlow]
    have : ((b[0]?.getD 0) &&& 32 ≠ 0) ↔ ((b'[0]?.getD 0) &&& 32 ≠ 0) := hs.trans hs'.symm
    by_cases hc : (b[0]?.getD 0) &&& 32 ≠ 0
    · rw [ite_eq_left hc, ite_eq_left (this.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun e => hc (this.mpr e))]
  apply byteArray_ext (s.trans s'.symm)
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact h0
  · by_cases hlt : i < 48
    · have := hbytes (i - 1) (by omega)
      rw [show 1 + (i - 1) = i by omega] at this
      exact UInt8.toNat_inj.mp this
    · have := hbytes0 (i - 48) (by omega)
      rw [show 48 + (i - 48) = i by omega] at this
      exact UInt8.toNat_inj.mp this

end LeanLight.Lc.Bls
