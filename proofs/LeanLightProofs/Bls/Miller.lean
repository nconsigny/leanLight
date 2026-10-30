import LeanLightProofs.Bls.Curves
import LeanLightProofs.Bls.FinalExpPow

/-!
# BLS12-381: the runtime's Miller loop and EthLib's agree after the final exponentiation (25c)

The runtime's `millerLoop` (`LeanLight.Bls.Pairing`: one accumulator for every pair, G2's points in
Jacobian coordinates on the twist `E'`, the lines' coefficients from `dblStep` and `addStep`
multiplied in sparsely, the result conjugated since `x < 0`) and EthLib's naive one (affine points
of `E(𝔽_{p¹²})`, the untwist `(x·w⁻², y·w⁻³)` of `Q`, the slopes by inversions, one loop per pair,
each conjugated) compute different values, which agree once raised to `(p¹²−1)/r`, on every pair
whose `Q` is in G2 (`millerLoop_pow_eq`):

* **The runtime's loop over every pair is the product of its loops on each** (`millerLoop_toGF`):
  the squarings of the one accumulator distribute over the product (`roundAll_step`, over the
  inner loops' folds, `foldl_lines`); each pair's loop is `rtIter`, rounds of `rtRound`.
* **EthLib's loop is its rounds** (`ethMillerLoop_eq`, `ethIter`, `ethRound`).
* **One round on one pair** (`round_spec`, the invariant `RoundInv`): the runtime's point `T` is
  `[n]Q`, away from the identity, and EthLib's is its untwist (`Untwists`). The doubling step
  doubles it (`dblStep_good`, through `Jac.dbl_spec`; `E'` has no point with `y = 0`, so `2T ≠ O`)
  and EthLib's tangent at the untwisted point is the untwist's (`millerDouble_spec`,
  `tangent_untwist`, `step_untwist`); the addition of `Q` likewise (`addStep_good`,
  `millerAdd_spec`, `chord_untwist`), provided `x(T) ≠ x(Q)`, which holds when `[r]Q = O`
  because `T = [n]Q` with `2 ≤ n` and `n + 1 < r` (`addStep_H_ne_zero`: else `[n ∓ 1]Q = O`).
* **The lines differ by `s·w³`** (`lineGF_scaled`, with `dblStep_affine`, `addStep_affine`): the
  runtime's line is `s·w³` times EthLib's at `P`, `s` in `𝔽_{p²}` nonzero (`4YZ³` for the tangent,
  `4ZH` for the chord), and `(s·w³)^((p¹²−1)/r) = 1` (`lineScale_pow`: `(s·w³)² = s²·ξ` lies in
  `𝔽_{p²}`, and `2(p² − 1)` divides the exponent, by the kernel).

Nothing is assumed of `P`: the lines are evaluated at its coordinates, read in `𝔽_p`, whatever
they are (`Embeds`). `[r]Q = O` is needed: for `Q` of order 13 (`E'(𝔽_{p²})` has `13² ∣ h₂`), the
round that reaches `[13]Q` adds `Q` to `[12]Q = −Q`, where EthLib's chord has slope `0⁻¹ = 0` and
gives a point off the curve, the runtime's the identity, and the two values then differ after the
final exponentiation (evaluated, not proved: EthLib's inverses recurse on a 381-bit exponent,
beyond the kernel).

The approach is gattaca-com/silver's (`Pairing/LineScaling.lean`, `Untwist.lean`,
`MillerSpec.lean`), whose loop is over two fixed G2 points checked by tables; here it is over
every point of G2, the runtime's Jacobian formulas against EthLib's affine ones.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian
open LeanLight.Lc.Bls.Provenance (ofEth)

local notation "aff2" => Point.toAffine E2

/-! ## `𝔽_{p²}` and `w` inside `𝔽_{p¹²}` -/

/-- `𝔽_{p²}` inside `𝔽_{p¹²}`. -/
noncomputable abbrev emb2 : GFp2 →+* GFp12 := (algebraMap GFp6 GFp12).comp of6

/-- `w`, the generator of `𝔽_{p¹²}` over `𝔽_{p⁶}`: `w² = v`. -/
noncomputable def wGF : GFp12 := QuadraticAlgebra.omega

theorem wGF_sq : wGF ^ 2 = algebraMap GFp6 GFp12 vGF := by
  rw [sq, wGF, QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl

/-- `w⁶ = ξ`. -/
theorem wGF_six : wGF ^ 6 = emb2 ⟨1, 1⟩ := by
  rw [show 6 = 2 * 3 from rfl, pow_mul, wGF_sq, ← map_pow, v_cube]; rfl

theorem wGF_ne_zero : wGF ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [wGF] at this

theorem xi_ne_zero_GFp2 : (⟨1, 1⟩ : GFp2) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp at this

/-- `2(p² − 1)` divides the final exponentiation's exponent, by the kernel. -/
theorem finalExpExp_dvd : 2 * (P ^ 2 - 1) ∣ finalExpExp :=
  Nat.dvd_of_mod_eq_zero (by decide +kernel)

/-- Fermat in `𝔽_{p²}`. -/
theorem pow_card_sub_one_GFp2 {a : GFp2} (ha : a ≠ 0) : a ^ (P ^ 2 - 1) = 1 := by
  let _ := Fintype.ofFinite GFp2
  rw [← card_GFp2, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one a ha

/-- **The final exponentiation removes a line's scale**: for `s ≠ 0` in `𝔽_{p²}`,
`(s·w³)^((p¹²−1)/r) = 1`, since `(s·w³)² = s²·ξ` lies in `𝔽_{p²}` and `2(p² − 1)` divides the
exponent. -/
theorem lineScale_pow {s : GFp2} (hs : s ≠ 0) : (emb2 s * wGF ^ 3) ^ finalExpExp = 1 := by
  obtain ⟨m, hm⟩ := finalExpExp_dvd
  rw [hm, pow_mul, pow_mul]
  have h2 : (emb2 s * wGF ^ 3) ^ 2 = emb2 (s ^ 2 * ⟨1, 1⟩) := by
    rw [mul_pow, ← pow_mul, wGF_six, map_mul, map_pow]
  rw [h2, ← map_pow, pow_card_sub_one_GFp2 (mul_ne_zero (pow_ne_zero _ hs) xi_ne_zero_GFp2),
    map_one, one_pow]

/-! ## EthLib's `Fp6` and `Fp12` inverses, subtraction and constants -/

section EthLib

open EthLib.Cryptography.Bls (Fp)

/-- EthLib's `Fp6` inverse is the field's (`0` to `0`). -/
theorem toGF_ofEth6_inverse (a : EthLib.Cryptography.Bls.Fp6) :
    (ofEth6 a.inverse).toGF = (ofEth6 a).toGF⁻¹ := by
  rw [← Fp6.toGF_inv (reduced_ofEth6 a)]
  have := Fp2.reduced_ofEth a.c0; have := Fp2.reduced_ofEth a.c1
  have := Fp2.reduced_ofEth a.c2
  simp only [ofEth6, Fp6.toGF, Fp6.inv, EthLib.Cryptography.Bls.Fp6.inverse]
  eth_push
  fp2_push
  ring_nf

/-- EthLib's `Fp12` subtraction is the field's. -/
theorem toGF_ofEth12_sub (x y : EthLib.Cryptography.Bls.Fp12) :
    (ofEth12 (x - y)).toGF = (ofEth12 x).toGF - (ofEth12 y).toGF := by
  show (ofEth12 (EthLib.Cryptography.Bls.Fp12.sub x y)).toGF = _
  ext
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.sub, QuadraticAlgebra.re_sub]
    rw [toGF_ofEth6_sub]
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.sub, QuadraticAlgebra.im_sub]
    rw [toGF_ofEth6_sub]

/-- EthLib's `Fp12` inverse, through the norm to `Fp6`, is the field's (`0` to `0`). -/
theorem toGF_ofEth12_inverse (x : EthLib.Cryptography.Bls.Fp12) :
    (ofEth12 x.inverse).toGF = (ofEth12 x).toGF⁻¹ := by
  have hn : (ofEth6 (x.c0 * x.c0 - (x.c1 * x.c1).mulByV)).toGF =
      QuadraticAlgebra.norm (ofEth12 x).toGF := by
    rw [toGF_ofEth6_sub, toGF_ofEth6_mul, toGF_ofEth6_mulByV, toGF_ofEth6_mul,
      QuadraticAlgebra.norm_def]
    simp [ofEth12, Fp12.toGF]; ring
  ext
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.inverse,
      QuadraticAlgebra.inv_def, QuadraticAlgebra.re_smul, QuadraticAlgebra.re_star, smul_eq_mul]
    rw [toGF_ofEth6_mul, toGF_ofEth6_inverse, hn]
    simp [ofEth12, Fp12.toGF]; ring
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.inverse,
      QuadraticAlgebra.inv_def, QuadraticAlgebra.im_smul, QuadraticAlgebra.im_star, smul_eq_mul]
    rw [toGF_ofEth6_neg, toGF_ofEth6_mul, toGF_ofEth6_inverse, hn]
    simp [ofEth12, Fp12.toGF]; ring

/-- EthLib's `Fp12` element `⟨a, 0, 0; 0⟩` of `𝔽_{p²}`. -/
theorem toGF_ofEth12_ofFp2 (a : EthLib.Cryptography.Bls.Fp2) :
    (ofEth12 ⟨EthLib.Cryptography.Bls.Fp6.ofFp2 a, EthLib.Cryptography.Bls.Fp6.zero⟩).toGF =
      emb2 (ofEth a).toGF := by
  have h0 : (ofEth EthLib.Cryptography.Bls.Fp2.zero).toGF = 0 := by
    ext <;> simp [ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.zero,
      EthLib.Cryptography.Bls.Fp.zero]
  ext
  · simp [ofEth12, Fp12.toGF, ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.ofFp2, h0]
  · simp [ofEth12, Fp12.toGF]

/-- EthLib's `Fp2.ofFp c`, read in `𝔽_{p²}`. -/
theorem toGF_ofEth_ofFp (c : Fp) :
    (ofEth (EthLib.Cryptography.Bls.Fp2.ofFp c)).toGF = algebraMap GFp GFp2 (c.val : GFp) := by
  ext <;> simp [ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.ofFp, EthLib.Cryptography.Bls.Fp.zero]

/-- EthLib's `v`, read in `𝔽_{p⁶}`. -/
theorem toGF_ofEth6_v : (ofEth6 ⟨EthLib.Cryptography.Bls.Fp2.zero, EthLib.Cryptography.Bls.Fp2.one,
    EthLib.Cryptography.Bls.Fp2.zero⟩).toGF = vGF := by
  simp [ofEth6, Fp6.toGF, ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.zero,
    EthLib.Cryptography.Bls.Fp2.one, EthLib.Cryptography.Bls.Fp.zero,
    EthLib.Cryptography.Bls.Fp.one]

theorem vGF_ne_zero : vGF ≠ 0 := fun h => v_not_square ⟨0, by rw [h, mul_zero]⟩

/-- `w⁻²`, as EthLib stores it. -/
theorem toGF_wInv2 : (ofEth12 EthLib.Cryptography.Bls.Embedded.wInv2).toGF = (wGF ^ 2)⁻¹ := by
  rw [wGF_sq, ← map_inv₀]
  ext
  · show (ofEth6 (EthLib.Cryptography.Bls.Fp6.inverse ⟨EthLib.Cryptography.Bls.Fp2.zero,
      EthLib.Cryptography.Bls.Fp2.one, EthLib.Cryptography.Bls.Fp2.zero⟩)).toGF = vGF⁻¹
    rw [toGF_ofEth6_inverse, toGF_ofEth6_v]
  · show (ofEth6 EthLib.Cryptography.Bls.Fp6.zero).toGF = 0
    exact toGF_ofEth6_zero

theorem wGF_cube : wGF ^ 3 = ⟨0, vGF⟩ := by
  rw [pow_succ, wGF_sq]
  ext <;> simp [wGF]

/-- `w⁻³`, as EthLib stores it (`v⁻²·w`). -/
theorem toGF_wInv3 : (ofEth12 EthLib.Cryptography.Bls.Embedded.wInv3).toGF = (wGF ^ 3)⁻¹ := by
  have hw : (ofEth12 EthLib.Cryptography.Bls.Embedded.wInv3).toGF = ⟨0, (vGF * vGF)⁻¹⟩ := by
    ext
    · show (ofEth6 EthLib.Cryptography.Bls.Fp6.zero).toGF = 0
      exact toGF_ofEth6_zero
    · show (ofEth6 (EthLib.Cryptography.Bls.Fp6.inverse (⟨EthLib.Cryptography.Bls.Fp2.zero,
        EthLib.Cryptography.Bls.Fp2.one, EthLib.Cryptography.Bls.Fp2.zero⟩ *
        ⟨EthLib.Cryptography.Bls.Fp2.zero, EthLib.Cryptography.Bls.Fp2.one,
        EthLib.Cryptography.Bls.Fp2.zero⟩))).toGF = (vGF * vGF)⁻¹
      rw [toGF_ofEth6_inverse, toGF_ofEth6_mul, toGF_ofEth6_v]
  rw [hw, wGF_cube]
  symm
  apply inv_eq_of_mul_eq_one_right
  have hv := vGF_ne_zero
  ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one]
    field_simp
    ring
  · simp [QuadraticAlgebra.im_one]

end EthLib

/-! ## The runtime's steps in `𝔽_{p²}` -/

/-- The affine `x = X/Z²` of a runtime Jacobian point of `E'`. -/
noncomputable def G2J.ax (t : G2J) : GFp2 := t.x.toGF / t.z.toGF ^ 2

/-- The affine `y = Y/Z³` of a runtime Jacobian point of `E'`. -/
noncomputable def G2J.ay (t : G2J) : GFp2 := t.y.toGF / t.z.toGF ^ 3

theorem reduced_dblStep (t : G2J) : (dblStep t).1.Reduced ∧ (dblStep t).2.2.2.Reduced := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp only [dblStep] <;> fp2_reduced

theorem reduced_addStep (t : G2J) (q : G2A) :
    (addStep t q).1.Reduced ∧ (addStep t q).2.2.2.Reduced := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp only [addStep] <;> fp2_reduced

/-- The doubling step's point, coordinate by coordinate (dbl-2009-l). -/
theorem dblStep_pt {t : G2J} (ht : t.Reduced) :
    (dblStep t).1.x.toGF = 9 * t.x.toGF ^ 4 - 8 * t.x.toGF * t.y.toGF ^ 2 ∧
    (dblStep t).1.y.toGF = 3 * t.x.toGF ^ 2 *
      (4 * t.x.toGF * t.y.toGF ^ 2 - (9 * t.x.toGF ^ 4 - 8 * t.x.toGF * t.y.toGF ^ 2)) -
      8 * t.y.toGF ^ 4 ∧
    (dblStep t).1.z.toGF = 2 * t.y.toGF * t.z.toGF := by
  obtain ⟨hx, hy, hz⟩ := ht
  refine ⟨?_, ?_, ?_⟩ <;> simp only [dblStep] <;> fp2_push <;> ring

/-- The doubling step's line coefficients: `4YZ³`, `−6X²Z²`, `6X³ − 4Y²`. -/
theorem dblStep_coeffs {t : G2J} (ht : t.Reduced) :
    (dblStep t).2.1.toGF = 4 * t.y.toGF * t.z.toGF ^ 3 ∧
    (dblStep t).2.2.1.toGF = -(6 * t.x.toGF ^ 2 * t.z.toGF ^ 2) ∧
    (dblStep t).2.2.2.toGF = 6 * t.x.toGF ^ 3 - 4 * t.y.toGF ^ 2 := by
  obtain ⟨hx, hy, hz⟩ := ht
  refine ⟨?_, ?_, ?_⟩ <;> simp only [dblStep] <;> fp2_push <;> ring

/-- The doubling step's point is `Jac.dbl`'s, away from the identity. -/
theorem dblStep_toJ {t : G2J} (ht : t.Reduced) (hz : t.z.toGF ≠ 0) :
    (dblStep t).1.toJ = Jac.dbl t.toJ := by
  obtain ⟨h1, h2, h3⟩ := dblStep_pt ht
  unfold Jac.dbl
  rw [ite_eq_right (by simpa using hz)]
  funext i
  fin_cases i <;> simp [G2J.toJ, Jac.dblF, h1, h2, h3] <;> ring

/-- The addition step's point, coordinate by coordinate (madd-2007-bl), with
`H = x_Q·Z² − X` and `r = 2(y_Q·Z³ − Y)`. -/
theorem addStep_pt {t : G2J} (ht : t.Reduced) {q : G2A} (hq : q.Reduced) :
    (addStep t q).1.x.toGF = (2 * (q.y.toGF * t.z.toGF ^ 3 - t.y.toGF)) ^ 2 -
      4 * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ^ 3 -
      8 * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ^ 2 * t.x.toGF ∧
    (addStep t q).1.y.toGF = 2 * (q.y.toGF * t.z.toGF ^ 3 - t.y.toGF) *
      (4 * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ^ 2 * t.x.toGF -
        ((2 * (q.y.toGF * t.z.toGF ^ 3 - t.y.toGF)) ^ 2 -
          4 * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ^ 3 -
          8 * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ^ 2 * t.x.toGF)) -
      8 * t.y.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ^ 3 ∧
    (addStep t q).1.z.toGF = 2 * t.z.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) := by
  obtain ⟨hx, hy, hz⟩ := ht; obtain ⟨hqx, hqy⟩ := hq
  refine ⟨?_, ?_, ?_⟩ <;> simp only [addStep] <;> fp2_push <;> ring

/-- The addition step's line coefficients: `4·Z·H`, `−2r`, `2r·x_Q − 4·y_Q·Z·H`. -/
theorem addStep_coeffs {t : G2J} (ht : t.Reduced) {q : G2A} (hq : q.Reduced) :
    (addStep t q).2.1.toGF = 4 * t.z.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ∧
    (addStep t q).2.2.1.toGF = -(2 * (2 * (q.y.toGF * t.z.toGF ^ 3 - t.y.toGF))) ∧
    (addStep t q).2.2.2.toGF = 2 * (2 * (q.y.toGF * t.z.toGF ^ 3 - t.y.toGF)) * q.x.toGF -
      4 * q.y.toGF * t.z.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) := by
  obtain ⟨hx, hy, hz⟩ := ht; obtain ⟨hqx, hqy⟩ := hq
  refine ⟨?_, ?_, ?_⟩ <;> simp only [addStep] <;> fp2_push <;> ring

/-- The addition step's point is `Jac.addA`'s, away from the identity and from `x = x_Q`. -/
theorem addStep_toJ {t : G2J} (ht : t.Reduced) {q : G2A} (hq : q.Reduced) (hz : t.z.toGF ≠ 0)
    (hxq : t.x.toGF ≠ q.x.toGF * (t.z.toGF * t.z.toGF)) :
    (addStep t q).1.toJ = Jac.addA t.toJ q.x.toGF q.y.toGF := by
  obtain ⟨h1, h2, h3⟩ := addStep_pt ht hq
  unfold Jac.addA
  rw [ite_eq_right (by simpa using hz)]
  simp only [G2J.toJ_0, G2J.toJ_2, hxq, ↓reduceIte]
  funext i
  fin_cases i <;> simp [G2J.toJ, h1, h2, h3] <;> ring

/-! ## The lines, in `𝔽_{p¹²}` -/

/-- The line a runtime step multiplies in, `c2 + c1·x_P·v + c0·y_P·v·w`, in `𝔽_{p¹²}`. -/
noncomputable def lineGF (c0 c1 c2 : Fp2) (p : G1A) : GFp12 :=
  ⟨of6 c2.toGF + of6 (c1.mulFp p.x).toGF * vGF, of6 (c0.mulFp p.y).toGF * vGF⟩

theorem toGF_ell {f : Fp12} (hf : f.Reduced) {c0 c1 c2 : Fp2} (hc : c2.Reduced) (p : G1A) :
    (ell f c0 c1 c2 p).toGF = f.toGF * lineGF c0 c1 c2 p :=
  Fp12.toGF_mulBy014 hf hc (Fp2.reduced_mulFp _) (Fp2.reduced_mulFp _)

/-- `P`'s coordinate `a` of `𝔽_p` in `𝔽_{p¹²}`. -/
noncomputable abbrev embP (a : ℕ) : GFp12 := emb2 (algebraMap GFp GFp2 (a : GFp))

theorem lineGF_eq (c0 c1 c2 : Fp2) (p : G1A) :
    lineGF c0 c1 c2 p = emb2 c2.toGF + emb2 c1.toGF * embP p.x * wGF ^ 2 +
      emb2 c0.toGF * embP p.y * wGF ^ 3 := by
  rw [wGF_sq, wGF_cube]
  ext
  · simp [lineGF, embP, Algebra.smul_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring
  · simp [lineGF, embP, Algebra.smul_def, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring

/-- **A runtime line is EthLib's line scaled**: if the coefficients are `s`, `−s·m` and
`s·(m·x − y)`, the runtime's line is `s·w³` times the line of slope `m·w⁻¹` through the untwisted
`(x·w⁻², y·w⁻³)`, evaluated at `P`. -/
theorem lineGF_scaled {c0 c1 c2 : Fp2} (p : G1A) {s m x y : GFp2} (h0 : c0.toGF = s)
    (h1 : c1.toGF = -(s * m)) (h2 : c2.toGF = s * (m * x - y)) :
    lineGF c0 c1 c2 p = emb2 s * wGF ^ 3 * ((embP p.y - emb2 y * (wGF ^ 3)⁻¹) -
      emb2 m * wGF⁻¹ * (embP p.x - emb2 x * (wGF ^ 2)⁻¹)) := by
  rw [lineGF_eq, h0, h1, h2]
  have hw := wGF_ne_zero
  simp only [map_mul, map_sub, map_neg]
  field_simp
  ring

/-! ## EthLib's steps, read in `𝔽_{p¹²}` -/

/-- An EthLib point of `E(𝔽_{p¹²})` that is the untwist `(x·w⁻², y·w⁻³)` of the point `(x, y)` of
`E'(𝔽_{p²})`, not at infinity. -/
def Untwists (T : EthLib.Cryptography.Bls.Embedded.Point) (x y : GFp2) : Prop :=
  T.inf = false ∧ (ofEth12 T.x).toGF = emb2 x * (wGF ^ 2)⁻¹ ∧
    (ofEth12 T.y).toGF = emb2 y * (wGF ^ 3)⁻¹

theorem two_ne_zero_GFp12 : (2 : GFp12) ≠ 0 := by
  rw [← map_ofNat emb2 2]
  exact (map_ne_zero emb2).mpr two_ne_zero_GFp2

/-- EthLib's constants `n` of `Fp12`, `⟨n, 0, 0; 0⟩`. -/
theorem toGF_ofEth12_nat (n : ℕ) :
    (ofEth12 ⟨EthLib.Cryptography.Bls.Fp6.ofFp2
      (EthLib.Cryptography.Bls.Fp2.ofFp (EthLib.Cryptography.Bls.Fp.ofNat n)),
      EthLib.Cryptography.Bls.Fp6.zero⟩).toGF = (n : GFp12) := by
  rw [toGF_ofEth12_ofFp2, toGF_ofEth_ofFp, cast_val_ofNat, map_natCast, map_natCast]

/-- The tangent's slope at an untwisted point is `m·w⁻¹`, `m = 3x²/(2y)` its slope on `E'`. -/
theorem tangent_untwist {x y : GFp2} (hy : y ≠ 0) :
    3 * (emb2 x * (wGF ^ 2)⁻¹) * (emb2 x * (wGF ^ 2)⁻¹) * (2 * (emb2 y * (wGF ^ 3)⁻¹))⁻¹ =
      emb2 (3 * x ^ 2 / (2 * y)) * wGF⁻¹ := by
  have hw := wGF_ne_zero
  have hy' : emb2 y ≠ 0 := (map_ne_zero emb2).mpr hy
  have h2 := two_ne_zero_GFp12
  simp only [map_div₀, map_mul, map_pow, map_ofNat]
  field_simp

/-- The chord's slope through two untwisted points is `m·w⁻¹`, `m` its slope on `E'`. -/
theorem chord_untwist {x y x2 y2 : GFp2} (hx : x ≠ x2) :
    (emb2 y2 * (wGF ^ 3)⁻¹ - emb2 y * (wGF ^ 3)⁻¹) *
      (emb2 x2 * (wGF ^ 2)⁻¹ - emb2 x * (wGF ^ 2)⁻¹)⁻¹ =
      emb2 ((y2 - y) / (x2 - x)) * wGF⁻¹ := by
  have hw := wGF_ne_zero
  have hx' : emb2 x2 - emb2 x ≠ 0 := by
    rw [← map_sub]; exact (map_ne_zero emb2).mpr (sub_ne_zero.mpr (Ne.symm hx))
  simp only [map_div₀, map_sub]
  rw [← sub_mul, ← sub_mul, mul_inv, inv_inv]
  field_simp

/-- The point a slope `m·w⁻¹` gives from an untwisted point is the untwist of the point the slope
`m` gives on `E'`. -/
theorem step_untwist (m x y x2 : GFp2) :
    emb2 m * wGF⁻¹ * (emb2 m * wGF⁻¹) - emb2 x * (wGF ^ 2)⁻¹ - emb2 x2 * (wGF ^ 2)⁻¹ =
      emb2 (m ^ 2 - x - x2) * (wGF ^ 2)⁻¹ ∧
    emb2 m * wGF⁻¹ * (emb2 x * (wGF ^ 2)⁻¹ - emb2 (m ^ 2 - x - x2) * (wGF ^ 2)⁻¹) -
        emb2 y * (wGF ^ 3)⁻¹ =
      emb2 (m * (x - (m ^ 2 - x - x2)) - y) * (wGF ^ 3)⁻¹ := by
  have hw := wGF_ne_zero
  constructor
  · simp only [map_sub, map_pow]
    field_simp
  · simp only [map_sub, map_mul, map_pow]
    field_simp

/-- **EthLib's doubling step** on the untwist of `(x, y)`, `y ≠ 0`: the untwist of the doubled
point, and the value squared times the tangent line at `P`. -/
theorem millerDouble_spec {T Pe : EthLib.Cryptography.Bls.Embedded.Point} {x y : GFp2}
    (hT : Untwists T x y) (hy : y ≠ 0) (f : EthLib.Cryptography.Bls.Fp12) :
    Untwists (EthLib.Cryptography.Bls.millerDouble T Pe f).1
        ((3 * x ^ 2 / (2 * y)) ^ 2 - x - x)
        (3 * x ^ 2 / (2 * y) * (x - ((3 * x ^ 2 / (2 * y)) ^ 2 - x - x)) - y) ∧
      (ofEth12 (EthLib.Cryptography.Bls.millerDouble T Pe f).2).toGF =
        (ofEth12 f).toGF * (ofEth12 f).toGF * (((ofEth12 Pe.y).toGF - emb2 y * (wGF ^ 3)⁻¹) -
          emb2 (3 * x ^ 2 / (2 * y)) * wGF⁻¹ * ((ofEth12 Pe.x).toGF - emb2 x * (wGF ^ 2)⁻¹)) := by
  obtain ⟨hinf, hx, hy'⟩ := hT
  have hm : (ofEth12 (EthLib.Cryptography.Bls.Line.tangentSlope T.x T.y)).toGF =
      emb2 (3 * x ^ 2 / (2 * y)) * wGF⁻¹ := by
    simp only [EthLib.Cryptography.Bls.Line.tangentSlope]
    rw [toGF_ofEth12_mul, toGF_ofEth12_mul, toGF_ofEth12_mul, toGF_ofEth12_inverse,
      toGF_ofEth12_mul, toGF_ofEth12_nat, toGF_ofEth12_nat, hx, hy']
    exact_mod_cast tangent_untwist hy
  obtain ⟨sx, sy⟩ := step_untwist (3 * x ^ 2 / (2 * y)) x y x
  unfold EthLib.Cryptography.Bls.millerDouble
  rw [hinf, ite_eq_right Bool.false_ne_true]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · simp only [toGF_ofEth12_sub, toGF_ofEth12_mul, hm, hx]
    exact sx
  · simp only [toGF_ofEth12_sub, toGF_ofEth12_mul, hm, hx, hy', sx]
    exact sy
  · simp only [EthLib.Cryptography.Bls.Line.evalAt, toGF_ofEth12_sub, toGF_ofEth12_mul, hm, hx,
      hy']

/-- **EthLib's addition step** of the untwists of `(x, y)` and `(x_Q, y_Q)`, `x ≠ x_Q`: the
untwist of their sum, and the value times the chord at `P`. -/
theorem millerAdd_spec {T R0 Pe : EthLib.Cryptography.Bls.Embedded.Point} {x y xq yq : GFp2}
    (hT : Untwists T x y) (hR : Untwists R0 xq yq) (hxq : x ≠ xq)
    (f : EthLib.Cryptography.Bls.Fp12) :
    Untwists (EthLib.Cryptography.Bls.millerAdd T R0 Pe f).1
        (((yq - y) / (xq - x)) ^ 2 - x - xq)
        ((yq - y) / (xq - x) * (x - (((yq - y) / (xq - x)) ^ 2 - x - xq)) - y) ∧
      (ofEth12 (EthLib.Cryptography.Bls.millerAdd T R0 Pe f).2).toGF =
        (ofEth12 f).toGF * (((ofEth12 Pe.y).toGF - emb2 y * (wGF ^ 3)⁻¹) -
          emb2 ((yq - y) / (xq - x)) * wGF⁻¹ * ((ofEth12 Pe.x).toGF - emb2 x * (wGF ^ 2)⁻¹)) := by
  obtain ⟨hinf, hx, hy⟩ := hT
  obtain ⟨hinf', hx', hy'⟩ := hR
  have hm : (ofEth12 (EthLib.Cryptography.Bls.Line.addSlope T.x T.y R0.x R0.y)).toGF =
      emb2 ((yq - y) / (xq - x)) * wGF⁻¹ := by
    simp only [EthLib.Cryptography.Bls.Line.addSlope]
    rw [toGF_ofEth12_mul, toGF_ofEth12_inverse, toGF_ofEth12_sub, toGF_ofEth12_sub, hx, hy, hx',
      hy']
    exact chord_untwist hxq
  obtain ⟨sx, sy⟩ := step_untwist ((yq - y) / (xq - x)) x y xq
  unfold EthLib.Cryptography.Bls.millerAdd
  rw [hinf, ite_eq_right Bool.false_ne_true, hinf', ite_eq_right Bool.false_ne_true]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · simp only [toGF_ofEth12_sub, toGF_ofEth12_mul, hm, hx, hx']
    exact sx
  · simp only [toGF_ofEth12_sub, toGF_ofEth12_mul, hm, hx, hx', hy, sx]
    exact sy
  · simp only [EthLib.Cryptography.Bls.Line.evalAt, toGF_ofEth12_sub, toGF_ofEth12_mul, hm, hx,
      hy]

/-! ## The runtime's steps on affine coordinates -/

/-- The runtime's doubling, on the affine coordinates: the doubled point is the tangent's,
`m = 3x²/(2y)`, and the line's coefficients are `4YZ³` times `(1, −m, m·x − y)`. -/
theorem dblStep_affine {t : G2J} (ht : t.Reduced) (hz : t.z.toGF ≠ 0) (hy : t.y.toGF ≠ 0) :
    (dblStep t).1.ax = (3 * t.ax ^ 2 / (2 * t.ay)) ^ 2 - t.ax - t.ax ∧
    (dblStep t).1.ay = 3 * t.ax ^ 2 / (2 * t.ay) *
      (t.ax - ((3 * t.ax ^ 2 / (2 * t.ay)) ^ 2 - t.ax - t.ax)) - t.ay ∧
    (dblStep t).2.1.toGF = 4 * t.y.toGF * t.z.toGF ^ 3 ∧
    (dblStep t).2.2.1.toGF = -(4 * t.y.toGF * t.z.toGF ^ 3 * (3 * t.ax ^ 2 / (2 * t.ay))) ∧
    (dblStep t).2.2.2.toGF = 4 * t.y.toGF * t.z.toGF ^ 3 *
      (3 * t.ax ^ 2 / (2 * t.ay) * t.ax - t.ay) := by
  obtain ⟨p1, p2, p3⟩ := dblStep_pt ht
  obtain ⟨c1, c2, c3⟩ := dblStep_coeffs ht
  have h2 := two_ne_zero_GFp2
  refine ⟨?_, ?_, c1, ?_, ?_⟩
  · simp only [G2J.ax, G2J.ay, p1, p3]
    field_simp
    ring
  · simp only [G2J.ax, G2J.ay, p2, p3]
    field_simp
    ring
  · rw [c2]; simp only [G2J.ax, G2J.ay]
    field_simp
    ring
  · rw [c3]; simp only [G2J.ax, G2J.ay]
    field_simp
    ring

/-- The runtime's addition of `Q`, on the affine coordinates, `x ≠ x_Q`: the sum is the
chord's, `m = (y_Q − y)/(x_Q − x)`, and the line's coefficients are `4ZH` times `(1, −m, m·x − y)`,
`H = x_Q·Z² − X`. -/
theorem addStep_affine {t : G2J} (ht : t.Reduced) {q : G2A} (hq : q.Reduced) (hz : t.z.toGF ≠ 0)
    (hH : q.x.toGF * t.z.toGF ^ 2 - t.x.toGF ≠ 0) :
    (addStep t q).1.ax = ((q.y.toGF - t.ay) / (q.x.toGF - t.ax)) ^ 2 - t.ax - q.x.toGF ∧
    (addStep t q).1.ay = (q.y.toGF - t.ay) / (q.x.toGF - t.ax) *
      (t.ax - (((q.y.toGF - t.ay) / (q.x.toGF - t.ax)) ^ 2 - t.ax - q.x.toGF)) - t.ay ∧
    (addStep t q).2.1.toGF = 4 * t.z.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) ∧
    (addStep t q).2.2.1.toGF = -(4 * t.z.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) *
      ((q.y.toGF - t.ay) / (q.x.toGF - t.ax))) ∧
    (addStep t q).2.2.2.toGF = 4 * t.z.toGF * (q.x.toGF * t.z.toGF ^ 2 - t.x.toGF) *
      ((q.y.toGF - t.ay) / (q.x.toGF - t.ax) * t.ax - t.ay) := by
  obtain ⟨p1, p2, p3⟩ := addStep_pt ht hq
  obtain ⟨c1, c2, c3⟩ := addStep_coeffs ht hq
  have h2 := two_ne_zero_GFp2
  simp only [G2J.ax, G2J.ay]
  rw [p1, p2, p3, c1, c2, c3]
  generalize hHd : q.x.toGF * t.z.toGF ^ 2 - t.x.toGF = H at hH ⊢
  have hX : t.x.toGF = q.x.toGF * t.z.toGF ^ 2 - H := by rw [← hHd]; ring
  have hden : q.x.toGF - t.x.toGF / t.z.toGF ^ 2 = H / t.z.toGF ^ 2 := by
    rw [hX]; field_simp; ring
  rw [hden, hX]
  refine ⟨?_, ?_, rfl, ?_, ?_⟩ <;> field_simp <;> ring

/-! ## The runtime's points: the group law, away from the exceptional cases -/

/-- A point of `E'` away from the identity has `Y ≠ 0`: `E'` has no point with `y = 0`. -/
theorem G2J.y_ne_zero {t : G2J} (hn : E2.Nonsingular t.toJ) (hz : t.z.toGF ≠ 0) :
    t.y.toGF ≠ 0 := by
  have he := (Jac.equation_iff' (⟨4, 4⟩ : GFp2)).mp hn.1
  simp only [G2J.toJ_0, G2J.toJ_1, G2J.toJ_2] at he
  intro hy
  apply E2_y_ne_zero (x := t.ax) (y := t.ay)
  · simp only [G2J.ax, G2J.ay]
    field_simp
    linear_combination he
  · simp [G2J.ay, hy]

theorem G2J.ay_ne_zero {t : G2J} (hn : E2.Nonsingular t.toJ) (hz : t.z.toGF ≠ 0) : t.ay ≠ 0 :=
  div_ne_zero (G2J.y_ne_zero hn hz) (pow_ne_zero 3 hz)

/-- The runtime's doubling step doubles a point away from the identity, and stays away from it
(`E'` has no point of order 2). -/
theorem dblStep_good {t : G2J} (ht : t.Reduced) (hn : E2.Nonsingular t.toJ)
    (hz : t.z.toGF ≠ 0) :
    (dblStep t).1.Reduced ∧ E2.Nonsingular (dblStep t).1.toJ ∧ (dblStep t).1.z.toGF ≠ 0 ∧
      aff2 (dblStep t).1.toJ = 2 • aff2 t.toJ := by
  have hy := G2J.y_ne_zero hn hz
  obtain ⟨hd1, hd2⟩ := Jac.dbl_spec (⟨4, 4⟩ : GFp2) hn
  rw [← dblStep_toJ ht hz] at hd1 hd2
  refine ⟨(reduced_dblStep t).1, hd1, ?_, hd2⟩
  rw [(dblStep_pt ht).2.2]
  exact mul_ne_zero (mul_ne_zero two_ne_zero_GFp2 hy) hz

/-- The runtime's addition step adds `Q` to a point away from the identity whose `x` is not `Q`'s,
and the sum is away from the identity. -/
theorem addStep_good {t : G2J} (ht : t.Reduced) (hn : E2.Nonsingular t.toJ) (hz : t.z.toGF ≠ 0)
    {q : G2A} (hq : q.Reduced) (hqn : E2.Nonsingular q.toJ)
    (hH : q.x.toGF * t.z.toGF ^ 2 - t.x.toGF ≠ 0) :
    (addStep t q).1.Reduced ∧ E2.Nonsingular (addStep t q).1.toJ ∧ (addStep t q).1.z.toGF ≠ 0 ∧
      aff2 (addStep t q).1.toJ = aff2 t.toJ + aff2 q.toJ := by
  have hxq : t.x.toGF ≠ q.x.toGF * (t.z.toGF * t.z.toGF) := fun h => hH (by rw [h]; ring)
  obtain ⟨ha1, ha2⟩ := Jac.addA_spec (⟨4, 4⟩ : GFp2) two_ne_zero_GFp2 hn hqn
  rw [← addStep_toJ ht hq hz hxq] at ha1 ha2
  refine ⟨(reduced_addStep t q).1, ha1, ?_, ha2⟩
  rw [(addStep_pt ht hq).2.2]
  exact mul_ne_zero (mul_ne_zero two_ne_zero_GFp2 hz) hH

/-- **The addition step is never exceptional on G2**: if `T = [n]Q`, `Q` of order `r`, with
`2 ≤ n` and `n + 1 < r`, then `T ≠ ±Q`, so `x(T) ≠ x(Q)`. -/
theorem addStep_H_ne_zero {t : G2J} (hn : E2.Nonsingular t.toJ) (hz : t.z.toGF ≠ 0) {q : G2A}
    (hqn : E2.Nonsingular q.toJ) (hord : addOrderOf (aff2 q.toJ) = R) {n : ℕ}
    (hmul : aff2 t.toJ = n • aff2 q.toJ) (h1 : 2 ≤ n) (h2 : n + 1 < R) :
    q.x.toGF * t.z.toGF ^ 2 - t.x.toGF ≠ 0 := by
  intro hH
  have hxq : t.toJ 0 = q.x.toGF * (t.toJ 2 * t.toJ 2) := by
    simp only [G2J.toJ_0, G2J.toJ_2]; linear_combination -hH
  obtain ⟨-, ha2⟩ := Jac.addA_spec (⟨4, 4⟩ : GFp2) two_ne_zero_GFp2 hn hqn
  have hz' : ¬t.toJ 2 = 0 := by simpa using hz
  have hsum : aff2 t.toJ + aff2 q.toJ = 2 • aff2 t.toJ ∨ aff2 t.toJ + aff2 q.toJ = 0 := by
    unfold Jac.addA at ha2
    simp only [hz', hxq, ↓reduceIte] at ha2
    split_ifs at ha2
    · left; rw [← (Jac.dbl_spec (⟨4, 4⟩ : GFp2) hn).2]; exact ha2.symm
    · right; rw [← (Jac.inf_spec (⟨4, 4⟩ : GFp2)).2]; exact ha2.symm
  have hdvd : ∀ m, m • aff2 q.toJ = 0 → 0 < m → m < R → False := fun m hm h0 hlt => by
    have := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hm
    rw [hord] at this
    exact absurd (Nat.le_of_dvd h0 this) (by omega)
  rcases hsum with h | h
  · rw [two_nsmul, add_right_inj, hmul] at h
    apply hdvd (n - 1) _ (by omega) (by omega)
    have : n • aff2 q.toJ = (n - 1) • aff2 q.toJ + aff2 q.toJ := by
      rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
    rw [this] at h
    simpa using h
  · rw [hmul, ← succ_nsmul] at h
    exact hdvd (n + 1) h (by omega) h2

/-! ## One round of the two loops, on one pair -/

/-- An EthLib point that is `P`: its coordinates are `P`'s, in `𝔽_p ⊂ 𝔽_{p¹²}`. -/
def Embeds (Pe : EthLib.Cryptography.Bls.Embedded.Point) (p : G1A) : Prop :=
  (ofEth12 Pe.x).toGF = embP p.x ∧ (ofEth12 Pe.y).toGF = embP p.y

/-- One round of the runtime's Miller loop on one pair `(P, Q)`, in `𝔽_{p¹²}`: the doubling step
(the value squared, times the tangent at `P`) and, for bit `i` of `|x|` set, the addition of `Q`
(times the chord at `P`). -/
noncomputable def rtRound (p : G1A) (q : G2A) (i : ℕ) (s : G2J × GFp12) : G2J × GFp12 :=
  if X >>> i % 2 = 1 then
    ((addStep (dblStep s.1).1 q).1,
      s.2 * s.2 * lineGF (dblStep s.1).2.1 (dblStep s.1).2.2.1 (dblStep s.1).2.2.2 p *
        lineGF (addStep (dblStep s.1).1 q).2.1 (addStep (dblStep s.1).1 q).2.2.1
          (addStep (dblStep s.1).1 q).2.2.2 p)
  else ((dblStep s.1).1,
    s.2 * s.2 * lineGF (dblStep s.1).2.1 (dblStep s.1).2.2.1 (dblStep s.1).2.2.2 p)

/-- One round of EthLib's Miller loop: `millerDouble`, then, for bit `i` of `|x|` set,
`millerAdd` of `R₀`. -/
def ethRound (R0 Pe : EthLib.Cryptography.Bls.Embedded.Point) (i : ℕ)
    (s : EthLib.Cryptography.Bls.Embedded.Point × EthLib.Cryptography.Bls.Fp12) :
    EthLib.Cryptography.Bls.Embedded.Point × EthLib.Cryptography.Bls.Fp12 :=
  if EthLib.Cryptography.Bls.blsX >>> i &&& 1 = 1 then
    EthLib.Cryptography.Bls.millerAdd (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).1 R0 Pe
      (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).2
  else EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2

/-- The two loops' states on one pair: the runtime's point is `[n]Q`, away from the identity,
EthLib's is its untwist, and their values agree after the final exponentiation. -/
structure RoundInv (q : G2A) (n : ℕ) (s : G2J × GFp12)
    (e : EthLib.Cryptography.Bls.Embedded.Point × EthLib.Cryptography.Bls.Fp12) : Prop where
  /-- The runtime's point has reduced coordinates. -/
  red : s.1.Reduced
  /-- It is a point of `E'`. -/
  ns : E2.Nonsingular s.1.toJ
  /-- It is not the identity. -/
  z : s.1.z.toGF ≠ 0
  /-- It is `[n]Q`. -/
  mul : aff2 s.1.toJ = n • aff2 q.toJ
  /-- EthLib's point is its untwist. -/
  untw : Untwists e.1 s.1.ax s.1.ay
  /-- The two values agree after the final exponentiation. -/
  val : s.2 ^ finalExpExp = (ofEth12 e.2).toGF ^ finalExpExp

/-- A value times a line scaled by `K` with `K^((p¹²−1)/r) = 1`: the scale goes. -/
theorem pow_mul_scaled {a F K L : GFp12} (hK : K ^ finalExpExp = 1)
    (ha : a ^ finalExpExp = F ^ finalExpExp) :
    (a * (K * L)) ^ finalExpExp = (F * L) ^ finalExpExp := by
  rw [mul_pow, mul_pow, mul_pow, hK, ha, one_mul]

theorem four_ne_zero_GFp2 : (4 : GFp2) ≠ 0 := by
  rw [show (4 : GFp2) = 2 * 2 by norm_num]
  exact mul_ne_zero two_ne_zero_GFp2 two_ne_zero_GFp2

theorem blsX_bit (i : ℕ) :
    EthLib.Cryptography.Bls.blsX >>> i &&& 1 = 1 ↔ X >>> i % 2 = 1 := by
  rw [Nat.and_one_is_mod]; rfl

/-- **One round on one pair**: from states where the runtime's point is `[n]Q`, `1 ≤ n` and
`2n + 1 < r`, `Q` of order `r`, the two loops' rounds for bit `i` give states where it is
`[2n + bit]Q`. -/
theorem round_spec {p : G1A} {q : G2A} (hq : q.Reduced) (hqn : E2.Nonsingular q.toJ)
    (hord : addOrderOf (aff2 q.toJ) = R) {Pe R0 : EthLib.Cryptography.Bls.Embedded.Point}
    (hPe : Embeds Pe p) (hR0 : Untwists R0 q.x.toGF q.y.toGF) {n : ℕ} (hn1 : 1 ≤ n)
    (hn2 : 2 * n + 1 < R) (i : ℕ) {s : G2J × GFp12}
    {e : EthLib.Cryptography.Bls.Embedded.Point × EthLib.Cryptography.Bls.Fp12}
    (h : RoundInv q n s e) :
    RoundInv q (2 * n + X >>> i % 2) (rtRound p q i s) (ethRound R0 Pe i e) := by
  obtain ⟨hr, hns, hz, hmul, hT, hv⟩ := h
  have hY := G2J.y_ne_zero hns hz
  obtain ⟨dr, dns, dz, dmul⟩ := dblStep_good hr hns hz
  obtain ⟨ax1, ay1, c0, c1, c2⟩ := dblStep_affine hr hz hY
  obtain ⟨hdT, hdv⟩ := millerDouble_spec hT (G2J.ay_ne_zero hns hz) (Pe := Pe) e.2
  rw [hPe.1, hPe.2] at hdv
  rw [← ay1, ← ax1] at hdT
  have hdmul : aff2 (dblStep s.1).1.toJ = (2 * n) • aff2 q.toJ := by rw [dmul, hmul, mul_nsmul']
  have hS : 4 * s.1.y.toGF * s.1.z.toGF ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero four_ne_zero_GFp2 hY) (pow_ne_zero 3 hz)
  have hdval : (s.2 * s.2 * lineGF (dblStep s.1).2.1 (dblStep s.1).2.2.1 (dblStep s.1).2.2.2 p) ^
      finalExpExp = (ofEth12 (EthLib.Cryptography.Bls.millerDouble e.1 Pe e.2).2).toGF ^
        finalExpExp := by
    rw [hdv, lineGF_scaled p c0 c1 c2]
    exact pow_mul_scaled (lineScale_pow hS) (by rw [mul_pow, mul_pow, hv])
  unfold rtRound ethRound
  by_cases hb : X >>> i % 2 = 1
  · rw [ite_eq_left hb, ite_eq_left ((blsX_bit i).mpr hb)]
    have hH := addStep_H_ne_zero dns dz hqn hord hdmul (by omega) (by omega)
    obtain ⟨ar, ans, az, amul⟩ := addStep_good dr dns dz hq hqn hH
    obtain ⟨ax2, ay2, a0, a1, a2⟩ := addStep_affine dr hq dz hH
    have hxq : (dblStep s.1).1.ax ≠ q.x.toGF := by
      intro h
      apply hH
      rw [← h, G2J.ax]
      field_simp
      ring
    obtain ⟨haT, hav⟩ := millerAdd_spec hdT hR0 hxq (Pe := Pe)
      (EthLib.Cryptography.Bls.millerDouble e.1 Pe e.2).2
    rw [hPe.1, hPe.2] at hav
    rw [← ay2, ← ax2] at haT
    have hS' : 4 * (dblStep s.1).1.z.toGF * (q.x.toGF * (dblStep s.1).1.z.toGF ^ 2 -
        (dblStep s.1).1.x.toGF) ≠ 0 := mul_ne_zero (mul_ne_zero four_ne_zero_GFp2 dz) hH
    refine ⟨ar, ans, az, ?_, haT, ?_⟩
    · rw [amul, hdmul, hb, ← succ_nsmul]
    · rw [hav, lineGF_scaled p a0 a1 a2]
      exact pow_mul_scaled (lineScale_pow hS') hdval
  · rw [ite_eq_right hb, ite_eq_right (mt (blsX_bit i).mp hb)]
    have hb0 : X >>> i % 2 = 0 := by omega
    refine ⟨dr, dns, dz, ?_, hdT, hdval⟩
    rw [hdmul, hb0, Nat.add_zero]

/-! ## The loops on one pair -/

/-- The runtime's Miller loop on one pair `(P, Q)`, in `𝔽_{p¹²}`, after `k` rounds (bits
`62, …, 63 − k` of `|x|`): its point and its value. -/
noncomputable def rtIter (p : G1A) (q : G2A) : ℕ → G2J × GFp12
  | 0 => (G2J.ofAffine q, 1)
  | k + 1 => rtRound p q (62 - k) (rtIter p q k)

/-- EthLib's Miller loop on one pair, from `(R₀, 1)`, after `k` rounds. -/
def ethIter (R0 Pe : EthLib.Cryptography.Bls.Embedded.Point) :
    ℕ → EthLib.Cryptography.Bls.Embedded.Point × EthLib.Cryptography.Bls.Fp12
  | 0 => (R0, EthLib.Cryptography.Bls.Fp12.one)
  | k + 1 => ethRound R0 Pe (62 - k) (ethIter R0 Pe k)

/-- Before each round `k < 63`, the bits of `|x|` read so far, `⌊|x|/2^(63−k)⌋`, are at least
one and twice them plus one is below `r`, by the kernel. -/
theorem X_prefix_bounds : ∀ k < 63, 1 ≤ X >>> (63 - k) ∧ 2 * (X >>> (63 - k)) + 1 < R := by
  decide +kernel

theorem X_prefix_succ {k : ℕ} (hk : k < 63) :
    2 * (X >>> (63 - k)) + X >>> (62 - k) % 2 = X >>> (63 - (k + 1)) := by
  have := X_shift_succ (k + 1) (by omega)
  rw [show 63 - (k + 1) = 62 - k by omega, show 64 - (k + 1) = 63 - k by omega] at this
  rw [show 63 - (k + 1) = 62 - k by omega]
  omega

theorem X_top : X >>> 63 = 1 := by decide

/-- **The two Miller loops on one pair**, `Q` of order `r`: after every round `k ≤ 63` the runtime's
point is `[⌊|x|/2^(63−k)⌋]Q`, EthLib's is its untwist, and the values agree after the final
exponentiation. -/
theorem iter_spec {p : G1A} {q : G2A} (hq : q.Reduced) (hqn : E2.Nonsingular q.toJ)
    (hord : addOrderOf (aff2 q.toJ) = R) {Pe R0 : EthLib.Cryptography.Bls.Embedded.Point}
    (hPe : Embeds Pe p) (hR0 : Untwists R0 q.x.toGF q.y.toGF) :
    ∀ k ≤ 63, RoundInv q (X >>> (63 - k)) (rtIter p q k) (ethIter R0 Pe k) := by
  intro k
  induction k with
  | zero =>
    intro _
    have hJ : (G2J.ofAffine q).toJ = q.toJ := by
      funext i; fin_cases i <;> simp [G2J.toJ, G2A.toJ, G2J.ofAffine]
    have hz : (G2J.ofAffine q).z.toGF = 1 := Fp2.toGF_one
    refine ⟨⟨hq.1, hq.2, Fp2.reduced_one⟩, hJ ▸ hqn,
      by show (G2J.ofAffine q).z.toGF ≠ 0; rw [hz]; exact one_ne_zero, ?_, ?_, ?_⟩
    · show aff2 (G2J.ofAffine q).toJ = (X >>> 63) • aff2 q.toJ
      rw [hJ, X_top, one_smul]
    · show Untwists R0 (G2J.ofAffine q).ax (G2J.ofAffine q).ay
      simp only [G2J.ax, G2J.ay, hz, one_pow, div_one]
      exact hR0
    · show (1 : GFp12) ^ finalExpExp = (ofEth12 EthLib.Cryptography.Bls.Fp12.one).toGF ^ finalExpExp
      rw [toGF_ofEth12_one]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := X_prefix_bounds k (by omega)
    have := round_spec hq hqn hord hPe hR0 h1 h2 (62 - k) (ih (by omega))
    rw [X_prefix_succ (by omega)] at this
    exact this

/-- EthLib's `millerLoop` over `|x|` is its rounds, from `(R₀, 1)`. -/
theorem ethMillerLoop_eq (R0 Pe : EthLib.Cryptography.Bls.Embedded.Point) :
    EthLib.Cryptography.Bls.millerLoop EthLib.Cryptography.Bls.blsX R0 Pe =
      (ethIter R0 Pe 63).2 := by
  have hlog : EthLib.Cryptography.Bls.blsX.log2 = 63 := by decide +kernel
  unfold EthLib.Cryptography.Bls.millerLoop
  simp only [hlog, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [ite_eq_right (by decide)]
  have hb : (fun (k : ℕ) (s : EthLib.Cryptography.Bls.Embedded.Point ×
      EthLib.Cryptography.Bls.Fp12) =>
      if EthLib.Cryptography.Bls.blsX >>> (63 + 1 - 2 - k) &&& 1 = 1 then
        (pure (ForInStep.yield
          ((EthLib.Cryptography.Bls.millerAdd (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).1 R0
            Pe (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).2).1,
          (EthLib.Cryptography.Bls.millerAdd (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).1 R0
            Pe (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).2).2)) : Id _)
      else pure (ForInStep.yield ((EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).1,
        (EthLib.Cryptography.Bls.millerDouble s.1 Pe s.2).2))) =
      fun k s => pure (ForInStep.yield (ethRound R0 Pe (62 - k) s)) := by
    funext k s
    unfold ethRound
    rw [show 63 + 1 - 2 - k = 62 - k by omega]
    split <;> rfl
  rw [hb, List.forIn_pure_yield_eq_foldl]
  have hf : ∀ n, (List.range' 0 n).foldl (fun s k => ethRound R0 Pe (62 - k) s)
      (R0, EthLib.Cryptography.Bls.Fp12.one) = ethIter R0 Pe n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range'_concat, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, Nat.zero_add,
        Nat.one_mul]
      rfl
  rw [hf]
  rfl

/-! ## The runtime's loop over every pair -/

theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).zip l = l.map fun a => (f a, a)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_self f l, List.map_cons]

/-- The runtime's inner loop over the pairs, as a fold: one accumulator multiplied by each
pair's line, the new points collected in reverse. -/
theorem foldl_lines (g : G2J × (G1A × G2A) → G2J × Fp2 × Fp2 × Fp2)
    (hg : ∀ a, (g a).2.2.2.Reduced) :
    ∀ (l : List (G2J × (G1A × G2A))) (f : Fp12) (acc : List G2J), f.Reduced →
      (l.foldl (fun b a => (ell b.1 (g a).2.1 (g a).2.2.1 (g a).2.2.2 a.2.1, (g a).1 :: b.2))
        (f, acc)).1.Reduced ∧
      (l.foldl (fun b a => (ell b.1 (g a).2.1 (g a).2.2.1 (g a).2.2.2 a.2.1, (g a).1 :: b.2))
        (f, acc)).1.toGF =
        f.toGF * (l.map fun a => lineGF (g a).2.1 (g a).2.2.1 (g a).2.2.2 a.2.1).prod ∧
      (l.foldl (fun b a => (ell b.1 (g a).2.1 (g a).2.2.1 (g a).2.2.2 a.2.1, (g a).1 :: b.2))
        (f, acc)).2 = (l.map fun a => (g a).1).reverse ++ acc
  | [], f, acc, hf => by simp [hf]
  | a :: l, f, acc, hf => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := foldl_lines g hg l _ ((g a).1 :: acc) (reduced_ell f _ _ _ a.2.1)
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, toGF_ell hf (hg a), List.map_cons, List.prod_cons, mul_assoc]
    · rw [h3, List.map_cons, List.reverse_cons, List.append_assoc]; rfl

/-- The runtime's doubling pass over the pairs: each pair's tangent multiplied into one
accumulator, the doubled points collected in reverse. -/
def dblPass (ps : List (G1A × G2A)) (f0 : Fp12) (ts : List G2J) : Fp12 × List G2J :=
  (ts.zip ps).foldl (fun b a => (ell b.1 (dblStep a.1).2.1 (dblStep a.1).2.2.1
    (dblStep a.1).2.2.2 a.2.1, (dblStep a.1).1 :: b.2)) (f0, [])

/-- The runtime's addition pass over the pairs, after a doubling pass. -/
def addPass (ps : List (G1A × G2A)) (s : Fp12 × List G2J) : Fp12 × List G2J :=
  (s.2.reverse.zip ps).foldl (fun b a => (ell b.1 (addStep a.1 a.2.2).2.1
    (addStep a.1 a.2.2).2.2.1 (addStep a.1 a.2.2).2.2.2 a.2.1, (addStep a.1 a.2.2).1 :: b.2))
    (s.1, [])

/-- One round of the runtime's loop over every pair: from an accumulator standing for the
product of the pairs' values squared, and the pairs' points, the doubling pass and (for bit
`62 − k` set) the addition pass give the product of the pairs' values after round `k + 1`,
and their points. -/
theorem roundAll_step (ps : List (G1A × G2A)) {k : ℕ} {f0 : Fp12} {ts : List G2J}
    (hf0 : f0.Reduced) (hts : ts = ps.map fun pq => (rtIter pq.1 pq.2 k).1)
    (hf : f0.toGF = (ps.map fun pq => (rtIter pq.1 pq.2 k).2 * (rtIter pq.1 pq.2 k).2).prod) :
    ∃ c, (if X >>> (62 - k) % 2 = 1 then
        pure (ForInStep.yield ((addPass ps (dblPass ps f0 ts)).1,
          (addPass ps (dblPass ps f0 ts)).2.reverse))
      else pure (ForInStep.yield ((dblPass ps f0 ts).1, (dblPass ps f0 ts).2.reverse)) :
        Id (ForInStep (Fp12 × List G2J))) = ForInStep.yield c ∧
      c.1.Reduced ∧ c.2 = ps.map (fun pq => (rtIter pq.1 pq.2 (k + 1)).1) ∧
        c.1.toGF = (ps.map fun pq => (rtIter pq.1 pq.2 (k + 1)).2).prod := by
  subst hts
  obtain ⟨d1, d2, d3⟩ := foldl_lines (fun a => dblStep a.1) (fun a => (reduced_dblStep a.1).2)
    ((ps.map fun pq => (rtIter pq.1 pq.2 k).1).zip ps) f0 [] hf0
  have e2 : ((ps.map fun pq => (rtIter pq.1 pq.2 k).1).zip ps).map (fun a =>
      lineGF (dblStep a.1).2.1 (dblStep a.1).2.2.1 (dblStep a.1).2.2.2 a.2.1) =
      ps.map fun pq => lineGF (dblStep (rtIter pq.1 pq.2 k).1).2.1
        (dblStep (rtIter pq.1 pq.2 k).1).2.2.1 (dblStep (rtIter pq.1 pq.2 k).1).2.2.2 pq.1 := by
    rw [zip_map_self, List.map_map]; rfl
  have e3 : ((ps.map fun pq => (rtIter pq.1 pq.2 k).1).zip ps).map (fun a => (dblStep a.1).1) =
      ps.map fun pq => (dblStep (rtIter pq.1 pq.2 k).1).1 := by
    rw [zip_map_self, List.map_map]; rfl
  rw [e2] at d2
  rw [e3, List.append_nil] at d3
  generalize hF1 : dblPass ps f0 (ps.map fun pq => (rtIter pq.1 pq.2 k).1) = F1
  have hF1r : F1.1.Reduced := by rw [← hF1]; exact d1
  have hF1t : F1.2.reverse = ps.map fun pq => (dblStep (rtIter pq.1 pq.2 k).1).1 := by
    rw [← hF1, dblPass, d3, List.reverse_reverse]
  have hF1v : F1.1.toGF = (ps.map fun pq => (rtIter pq.1 pq.2 k).2 * (rtIter pq.1 pq.2 k).2 *
      lineGF (dblStep (rtIter pq.1 pq.2 k).1).2.1 (dblStep (rtIter pq.1 pq.2 k).1).2.2.1
        (dblStep (rtIter pq.1 pq.2 k).1).2.2.2 pq.1).prod := by
    rw [← hF1, dblPass, d2, hf, ← List.prod_map_mul]
  obtain ⟨a1, a2, a3⟩ := foldl_lines (fun a => addStep a.1 a.2.2)
    (fun a => (reduced_addStep a.1 a.2.2).2) (F1.2.reverse.zip ps) F1.1 [] hF1r
  have e4 : (F1.2.reverse.zip ps).map (fun a =>
      lineGF (addStep a.1 a.2.2).2.1 (addStep a.1 a.2.2).2.2.1 (addStep a.1 a.2.2).2.2.2 a.2.1) =
      ps.map fun pq => lineGF (addStep (dblStep (rtIter pq.1 pq.2 k).1).1 pq.2).2.1
        (addStep (dblStep (rtIter pq.1 pq.2 k).1).1 pq.2).2.2.1
        (addStep (dblStep (rtIter pq.1 pq.2 k).1).1 pq.2).2.2.2 pq.1 := by
    rw [hF1t, zip_map_self, List.map_map]; rfl
  have e5 : (F1.2.reverse.zip ps).map (fun a => (addStep a.1 a.2.2).1) =
      ps.map fun pq => (addStep (dblStep (rtIter pq.1 pq.2 k).1).1 pq.2).1 := by
    rw [hF1t, zip_map_self, List.map_map]; rfl
  rw [e4] at a2
  rw [e5, List.append_nil] at a3
  by_cases hb : X >>> (62 - k) % 2 = 1
  · rw [ite_eq_left hb]
    refine ⟨_, rfl, a1, ?_, ?_⟩
    · rw [addPass, a3, List.reverse_reverse]
      apply List.map_congr_left
      intro pq _
      simp only [rtIter, rtRound, ite_eq_left hb]
    · rw [addPass, a2, hF1v, ← List.prod_map_mul]
      congr 1
      apply List.map_congr_left
      intro pq _
      simp only [rtIter, rtRound, ite_eq_left hb]
  · rw [ite_eq_right hb]
    refine ⟨_, rfl, hF1r, ?_, ?_⟩
    · rw [hF1t]
      apply List.map_congr_left
      intro pq _
      simp only [rtIter, rtRound, ite_eq_right hb]
    · rw [hF1v]
      congr 1
      apply List.map_congr_left
      intro pq _
      simp only [rtIter, rtRound, ite_eq_right hb]

/-- **The runtime's Miller loop over every pair** is the conjugate of the product of its loop on
each pair: one accumulator, squared once per round, whose squarings distribute over the
product. -/
theorem millerLoop_toGF (ps : List (G1A × G2A)) :
    (millerLoop ps).toGF = star (ps.map fun pq => (rtIter pq.1 pq.2 63).2).prod := by
  unfold millerLoop
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  suffices H : ∀ A : Fp12 × List G2J, (A.1.Reduced ∧
      A.2 = ps.map (fun pq => (rtIter pq.1 pq.2 63).1) ∧
      A.1.toGF = (ps.map fun pq => (rtIter pq.1 pq.2 63).2).prod) →
      A.1.conj.toGF = star (ps.map fun pq => (rtIter pq.1 pq.2 63).2).prod by
    refine H _ (forIn_range'_inv (fun k (s : Fp12 × List G2J) => s.1.Reduced ∧
      s.2 = ps.map (fun pq => (rtIter pq.1 pq.2 k).1) ∧
      s.1.toGF = (ps.map fun pq => (rtIter pq.1 pq.2 k).2).prod) _ 63 0 _ ?_ ?_)
    · rintro k ⟨f, ts⟩ - - ⟨hr, hts, hf⟩
      split
      · exact roundAll_step ps (Fp12.reduced_sqr hr) hts
          (by rw [Fp12.toGF_sqr hr, hf, List.prod_map_mul])
      · rename_i hk0
        have hk : k = 0 := by omega
        subst hk
        refine roundAll_step ps hr hts ?_
        rw [hf]
        simp [rtIter]
    · exact ⟨Fp12.reduced_one, rfl, by simp [rtIter]⟩
  rintro A ⟨hr, -, hv⟩
  rw [Fp12.toGF_conj hr, hv]

/-! ## The two Miller loops agree after the final exponentiation -/

/-- **The two Miller loops on one pair agree after the final exponentiation**: for `Q` a reduced
point of `E'` with `[r]Q = O` and EthLib points `P_e` standing for `P` and `R₀` the untwist of
`Q`, the runtime's loop on `(P, Q)` and EthLib's `millerLoop` over `|x|` from `R₀` at `P_e` give
the same value raised to `(p¹²−1)/r`. -/
theorem miller_pair {p : G1A} {q : G2A} (hq : q.Reduced) (hqn : E2.Nonsingular q.toJ)
    (hr : R • aff2 q.toJ = 0) {Pe R0 : EthLib.Cryptography.Bls.Embedded.Point}
    (hPe : Embeds Pe p) (hR0 : Untwists R0 q.x.toGF q.y.toGF) :
    (rtIter p q 63).2 ^ finalExpExp = (ofEth12 (EthLib.Cryptography.Bls.millerLoop
      EthLib.Cryptography.Bls.blsX R0 Pe)).toGF ^ finalExpExp := by
  have hne : aff2 q.toJ ≠ 0 := by
    rw [G2A.toJ, Point.toAffine_some (by rw [← G2A.toJ]; exact hqn)]
    exact Affine.Point.some_ne_zero _
  have := Fact.mk R_prime
  have hord : addOrderOf (aff2 q.toJ) = R := addOrderOf_eq_prime hr hne
  rw [ethMillerLoop_eq]
  exact (iter_spec hq hqn hord hPe hR0 63 le_rfl).val

theorem prod_pow_congr {α : Type} {f g : α → GFp12} {n : ℕ} :
    ∀ l : List α, (∀ a ∈ l, f a ^ n = g a ^ n) → (l.map f).prod ^ n = (l.map g).prod ^ n
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, mul_pow, mul_pow,
      h a List.mem_cons_self, prod_pow_congr l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem star_prod {α : Type} (f : α → GFp12) (l : List α) :
    star (l.map f).prod = (l.map fun a => star (f a)).prod := by
  rw [← starRingEnd_apply, map_list_prod, List.map_map]
  rfl

/-- **The runtime's Miller loop and EthLib's, over a list of pairs, after the final
exponentiation**: if every pair's `Q` is a reduced point of `E'` with `[r]Q = O`, and `emb`
gives EthLib points standing for each pair's `P` and the untwist of its `Q`, then the runtime's
`millerLoop ps` and the product of EthLib's conjugated `millerLoop`s over `|x|` give the same value
raised to `(p¹²−1)/r`. -/
theorem millerLoop_pow_eq (ps : List (G1A × G2A))
    (emb : G1A × G2A → EthLib.Cryptography.Bls.Embedded.Point ×
      EthLib.Cryptography.Bls.Embedded.Point)
    (h : ∀ pq ∈ ps, pq.2.Reduced ∧ E2.Nonsingular pq.2.toJ ∧ R • aff2 pq.2.toJ = 0 ∧
      Embeds (emb pq).1 pq.1 ∧ Untwists (emb pq).2 pq.2.x.toGF pq.2.y.toGF) :
    (millerLoop ps).toGF ^ finalExpExp = (ps.map fun pq => star (ofEth12
      (EthLib.Cryptography.Bls.millerLoop EthLib.Cryptography.Bls.blsX (emb pq).2
        (emb pq).1)).toGF).prod ^ finalExpExp := by
  rw [millerLoop_toGF, ← star_pow, ← star_prod, ← star_pow]
  refine congrArg star (prod_pow_congr ps fun pq hpq => ?_)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h pq hpq
  exact miller_pair h1 h2 h3 h4 h5

end LeanLight.Lc.Bls
