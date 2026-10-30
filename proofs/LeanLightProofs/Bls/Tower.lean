import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic
import LeanLightProofs.Bls.Fp2
import LeanLight.Bls.Fp12

/-!
# BLS12-381: `Fp6` and `Fp12` are fields, `𝔽_{p⁶}` and `𝔽_{p¹²}` (25c)

The tower's upper floors as fields, after reuse rule C4f:

* `GFp6 = 𝔽_{p²}[v]/(v³ − ξ)`, Mathlib's `AdjoinRoot`, a field because `X³ − ξ` is irreducible
  (`fp6Poly_irreducible`: Mathlib's `X_pow_sub_C_irreducible_of_prime`, `ξ` not a cube,
  `xi_not_cube`); `v` is its root (`vGF`, `v_cube`), and `1, v, v²` are independent
  (`tower6_inj`).
* `GFp12 = 𝔽_{p⁶}[w]/(w² − v)`, Mathlib's `QuadraticAlgebra GFp6 v 0`, a field because `v` is
  not a square in `𝔽_{p⁶}` (`v_not_square`: its norm to `𝔽_{p²}` is `ξ`, `norm_v`, which is not
  a square, `xi_not_square`).
* They have `p⁶` and `p¹²` elements (`card_GFp6`, `card_GFp12`), so every nonzero `f` of
  `𝔽_{p¹²}` has `f^(p¹²−1) = 1` (`pow_card_sub_one_GFp12`), which the cube lemma uses.
* **The runtime's tower** (`Fp6.toGF`: `c0 + c1·v + c2·v²`, `Fp12.toGF`: `c0 + c1·w`, on
  `Reduced` values, where they are injective): addition, subtraction, negation, the
  interpolated product and Chung–Hasan's squaring, the products by `v` and by sparse Miller-loop
  lines (`mulBy1`, `mulBy01`, `mulBy014`), the inverses through the norms, the conjugate of
  `Fp12` (`star`), and the tests `eq`, `isZero`, `isOne` are the fields' (`Fp6.toGF_mul`,
  `Fp12.toGF_inv`, `Fp12.isOne_iff` and the like). The Frobenius, the conjugate as a power and the
  cyclotomic squaring of the final exponentiation are in `LeanLightProofs.Bls.Frobenius`, the
  final exponentiation itself in `LeanLightProofs.Bls.FinalExpPow`.
* **EthLib's readable tower** (`ofEth6`, `ofEth12`, injective): its operations are the fields'
  too (`toGF_ofEth6_mul`, `toGF_ofEth12_mul`, `toGF_ofEth12_powNat`: its square and multiply is
  the power, `isOne_ofEth12_iff`), so the runtime's on EthLib's values give EthLib's
  (`Fp6.mul_ofEth6`, `Fp12.mul_ofEth12`, `Fp12.sqr_ofEth12` and the like).
-/

namespace LeanLight.Lc.Bls

open Polynomial

/-- `X³ − ξ` over `𝔽_{p²}`, `ξ = 1 + u`. -/
noncomputable def fp6Poly : GFp2[X] := Polynomial.X ^ 3 - C ⟨1, 1⟩

theorem fp6Poly_monic : fp6Poly.Monic := by
  unfold fp6Poly; exact monic_X_pow_sub_C _ (by norm_num)

theorem fp6Poly_natDegree : fp6Poly.natDegree = 3 := by
  unfold fp6Poly; exact natDegree_X_pow_sub_C

/-- `X³ − ξ` is irreducible over `𝔽_{p²}`: `ξ` is not a cube. -/
theorem fp6Poly_irreducible : Irreducible fp6Poly :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three xi_not_cube

instance fact_fp6Poly_irreducible : Fact (Irreducible fp6Poly) := ⟨fp6Poly_irreducible⟩

/-- `𝔽_{p⁶} = 𝔽_{p²}[v]/(v³ − ξ)`. -/
abbrev GFp6 := AdjoinRoot fp6Poly

noncomputable example : Field GFp6 := inferInstance

/-- `v`, the root of `X³ − ξ` in `𝔽_{p⁶}`. -/
noncomputable def vGF : GFp6 := AdjoinRoot.root fp6Poly

/-- `𝔽_{p²}` inside `𝔽_{p⁶}`. -/
noncomputable abbrev of6 : GFp2 →+* GFp6 := AdjoinRoot.of fp6Poly

/-- `v³ = ξ`. -/
theorem v_cube : vGF ^ 3 = of6 ⟨1, 1⟩ := by
  have h := AdjoinRoot.eval₂_root fp6Poly
  rwa [fp6Poly, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h

/-- The norm of `v` from `𝔽_{p⁶}` to `𝔽_{p²}` is `ξ`. -/
theorem norm_v : Algebra.norm GFp2 vGF = ⟨1, 1⟩ := by
  have hgen : (AdjoinRoot.powerBasis' fp6Poly_monic).gen = vGF := rfl
  rw [← hgen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, AdjoinRoot.powerBasis'_dim,
    fp6Poly_natDegree, hgen, vGF,
    AdjoinRoot.minpoly_root fp6Poly_irreducible.ne_zero, fp6Poly_monic.leadingCoeff, inv_one,
    C_1, mul_one, fp6Poly]
  simp only [coeff_sub, coeff_X_pow, coeff_C_zero]
  ext <;> norm_num

/-- `v` is not a square in `𝔽_{p⁶}`: its norm `ξ` is not one in `𝔽_{p²}`. -/
theorem v_not_square : ¬IsSquare vGF := by
  rintro ⟨s, hs⟩
  apply xi_not_square
  exact ⟨Algebra.norm GFp2 s, by rw [← norm_v, hs, map_mul]⟩

instance fact_v_not_square : Fact (¬IsSquare vGF) := ⟨v_not_square⟩

/-- `𝔽_{p¹²} = 𝔽_{p⁶}[w]/(w² − v)`. -/
abbrev GFp12 := QuadraticAlgebra GFp6 vGF 0

noncomputable example : Field GFp12 := inferInstance

instance : Finite GFp6 :=
  haveI := fp6Poly_monic.finite_adjoinRoot
  Module.finite_of_finite GFp2

instance : Finite GFp12 := Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm

/-- `𝔽_{p⁶}` has `p⁶` elements. -/
theorem card_GFp6 : Nat.card GFp6 = P ^ 6 := by
  rw [Nat.card_congr (AdjoinRoot.powerBasis' fp6Poly_monic).basis.equivFun.toEquiv,
    Nat.card_fun, card_GFp2, Nat.card_eq_fintype_card, Fintype.card_fin,
    AdjoinRoot.powerBasis'_dim, fp6Poly_natDegree, ← pow_mul]

/-- `𝔽_{p¹²}` has `p¹²` elements. -/
theorem card_GFp12 : Nat.card GFp12 = P ^ 12 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd _ _), Nat.card_prod, card_GFp6, ← pow_add]

/-- Fermat in `𝔽_{p¹²}`: a nonzero `f` has `f^(p¹²−1) = 1`. -/
theorem pow_card_sub_one_GFp12 {f : GFp12} (hf : f ≠ 0) : f ^ (P ^ 12 - 1) = 1 := by
  let _ := Fintype.ofFinite GFp12
  rw [← card_GFp12, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one f hf

/-- `x0 + x1·v + x2·v²` is zero only when `x0`, `x1`, `x2` are: `1, v, v²` are independent over
`𝔽_{p²}`. -/
theorem tower6_eq_zero {x0 x1 x2 : GFp2} (h : of6 x0 + of6 x1 * vGF + of6 x2 * vGF ^ 2 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by
  have hmk : of6 x0 + of6 x1 * vGF + of6 x2 * vGF ^ 2 =
      AdjoinRoot.mk fp6Poly (C x0 + C x1 * Polynomial.X + C x2 * Polynomial.X ^ 2) := by
    simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, vGF]
  rw [hmk, AdjoinRoot.mk_eq_zero] at h
  have hq := eq_zero_of_dvd_of_natDegree_lt h (by
    rw [fp6Poly_natDegree]
    calc (C x0 + C x1 * Polynomial.X + C x2 * Polynomial.X ^ 2).natDegree ≤ 2 := by
          compute_degree
      _ < 3 := by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 0) hq
  · simpa using congrArg (coeff · 1) hq
  · simpa using congrArg (coeff · 2) hq

/-- `x0 + x1·v + x2·v²` determines `x0`, `x1`, `x2`. -/
theorem tower6_inj {x0 x1 x2 y0 y1 y2 : GFp2}
    (h : of6 x0 + of6 x1 * vGF + of6 x2 * vGF ^ 2 = of6 y0 + of6 y1 * vGF + of6 y2 * vGF ^ 2) :
    x0 = y0 ∧ x1 = y1 ∧ x2 = y2 := by
  have := tower6_eq_zero (x0 := x0 - y0) (x1 := x1 - y1) (x2 := x2 - y2)
    (by simp only [map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2.1, sub_eq_zero.mp this.2.2⟩

/-! ## The runtime's `Fp6` -/

namespace Fp6

/-- The element `c0 + c1·v + c2·v²` of `𝔽_{p⁶}` a runtime `Fp6` stands for. -/
noncomputable def toGF (a : Fp6) : GFp6 :=
  of6 a.c0.toGF + of6 a.c1.toGF * vGF + of6 a.c2.toGF * vGF ^ 2

/-- Every coordinate reduced. -/
def Reduced (a : Fp6) : Prop := a.c0.Reduced ∧ a.c1.Reduced ∧ a.c2.Reduced

/-- On reduced values, `toGF` is injective. -/
theorem toGF_inj {a b : Fp6} (ha : a.Reduced) (hb : b.Reduced) : a.toGF = b.toGF ↔ a = b := by
  constructor
  · intro h
    obtain ⟨h0, h1, h2⟩ := tower6_inj h
    obtain ⟨a0, a1, a2⟩ := a; obtain ⟨b0, b1, b2⟩ := b
    rw [Fp2.toGF_inj ha.1 hb.1] at h0
    rw [Fp2.toGF_inj ha.2.1 hb.2.1] at h1
    rw [Fp2.toGF_inj ha.2.2 hb.2.2] at h2
    subst h0 h1 h2; rfl
  · rintro rfl; rfl

end Fp6

/-- Proves a runtime `Fp2` reduced from its operations and the hypotheses in context. -/
syntax "fp2_reduced" : tactic
macro_rules
  | `(tactic| fp2_reduced) => `(tactic| with_reducible first
    | assumption | exact Fp2.reduced_mul | exact Fp2.reduced_sqr | exact Fp2.reduced_inv
    | exact Fp2.reduced_mulFp _ | exact Fp2.reduced_zero | exact Fp2.reduced_one
    | exact Fp2.reduced_xi
    | (apply Fp2.reduced_add <;> fp2_reduced) | (apply Fp2.reduced_sub; fp2_reduced)
    | (apply Fp2.reduced_neg; fp2_reduced) | (apply Fp2.reduced_dbl; fp2_reduced)
    | (apply Fp2.reduced_conj; fp2_reduced) | (apply Fp2.reduced_mulXi; fp2_reduced))

/-- Pushes `Fp2.toGF` through the runtime's `Fp2` operations, proving the arguments reduced. -/
macro "fp2_push" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp (disch := fp2_reduced)
    only [Fp2.toGF_add, Fp2.toGF_sub, Fp2.toGF_neg, Fp2.toGF_dbl, Fp2.toGF_conj,
      Fp2.toGF_mul, Fp2.toGF_sqr, Fp2.toGF_mulFp, Fp2.toGF_mulXi, Fp2.toGF_inv, Fp2.toGF_zero,
      Fp2.toGF_one] $(loc)?)

namespace Fp6

variable {a b : Fp6}

theorem reduced_add (ha : a.Reduced) (hb : b.Reduced) : (a.add b).Reduced :=
  ⟨Fp2.reduced_add ha.1 hb.1, Fp2.reduced_add ha.2.1 hb.2.1, Fp2.reduced_add ha.2.2 hb.2.2⟩

theorem reduced_sub (ha : a.Reduced) : (a.sub b).Reduced :=
  ⟨Fp2.reduced_sub ha.1, Fp2.reduced_sub ha.2.1, Fp2.reduced_sub ha.2.2⟩

theorem reduced_neg (ha : a.Reduced) : a.neg.Reduced :=
  ⟨Fp2.reduced_neg ha.1, Fp2.reduced_neg ha.2.1, Fp2.reduced_neg ha.2.2⟩

theorem reduced_dbl (ha : a.Reduced) : a.dbl.Reduced :=
  ⟨Fp2.reduced_dbl ha.1, Fp2.reduced_dbl ha.2.1, Fp2.reduced_dbl ha.2.2⟩

theorem reduced_mul (ha : a.Reduced) (hb : b.Reduced) : (a.mul b).Reduced := by
  have := ha.1; have := ha.2.1; have := ha.2.2; have := hb.1; have := hb.2.1; have := hb.2.2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [mul] <;> fp2_reduced

theorem reduced_sqr (ha : a.Reduced) : a.sqr.Reduced := by
  have := ha.1; have := ha.2.1; have := ha.2.2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [sqr] <;> fp2_reduced

theorem reduced_mulV (ha : a.Reduced) : a.mulV.Reduced :=
  ⟨Fp2.reduced_mulXi ha.2.2, ha.1, ha.2.1⟩

theorem reduced_mulFp2 (s : Fp2) : (a.mulFp2 s).Reduced :=
  ⟨Fp2.reduced_mul, Fp2.reduced_mul, Fp2.reduced_mul⟩

theorem reduced_inv : a.inv.Reduced := ⟨Fp2.reduced_mul, Fp2.reduced_mul, Fp2.reduced_mul⟩

theorem reduced_zero : zero.Reduced := ⟨Fp2.reduced_zero, Fp2.reduced_zero, Fp2.reduced_zero⟩
theorem reduced_one : one.Reduced := ⟨Fp2.reduced_one, Fp2.reduced_zero, Fp2.reduced_zero⟩

@[simp] theorem toGF_zero : zero.toGF = 0 := by simp [toGF, zero]
@[simp] theorem toGF_one : one.toGF = 1 := by simp [toGF, one]

theorem toGF_add : (a.add b).toGF = a.toGF + b.toGF := by
  simp only [toGF, add]; fp2_push; simp only [map_add]; ring

theorem toGF_sub (hb : b.Reduced) : (a.sub b).toGF = a.toGF - b.toGF := by
  simp only [toGF, sub]
  rw [Fp2.toGF_sub hb.1, Fp2.toGF_sub hb.2.1, Fp2.toGF_sub hb.2.2]
  simp only [map_sub]; ring

theorem toGF_neg (ha : a.Reduced) : a.neg.toGF = -a.toGF := by
  simp only [toGF, neg]
  rw [Fp2.toGF_neg ha.1, Fp2.toGF_neg ha.2.1, Fp2.toGF_neg ha.2.2]
  simp only [map_neg]; ring

theorem toGF_dbl : a.dbl.toGF = a.toGF + a.toGF := by
  simp only [toGF, dbl, Fp2.toGF_dbl, map_add]; ring

/-- Multiplication by `v`. -/
theorem toGF_mulV (ha : a.Reduced) : a.mulV.toGF = vGF * a.toGF := by
  simp only [toGF, mulV]
  rw [Fp2.toGF_mulXi ha.2.2]
  simp only [map_mul]
  linear_combination (-(of6 a.c2.toGF)) * v_cube

/-- Multiplication by an element of `𝔽_{p²}`. -/
theorem toGF_mulFp2 {s : Fp2} (ha : a.Reduced) (hs : s.Reduced) :
    (a.mulFp2 s).toGF = of6 s.toGF * a.toGF := by
  simp only [toGF, mulFp2]
  rw [Fp2.toGF_mul ha.1 hs, Fp2.toGF_mul ha.2.1 hs, Fp2.toGF_mul ha.2.2 hs]
  simp only [map_mul]; ring

/-- The interpolated product is the field's. -/
theorem toGF_mul (ha : a.Reduced) (hb : b.Reduced) : (a.mul b).toGF = a.toGF * b.toGF := by
  have h0 := ha.1; have h1 := ha.2.1; have h2 := ha.2.2
  have h3 := hb.1; have h4 := hb.2.1; have h5 := hb.2.2
  simp only [toGF, mul]
  fp2_push
  simp only [map_add, map_sub, map_mul]
  linear_combination (-(of6 a.c1.toGF * of6 b.c2.toGF + of6 a.c2.toGF * of6 b.c1.toGF) -
    of6 a.c2.toGF * of6 b.c2.toGF * vGF) * v_cube

/-- Chung–Hasan's squaring is the field's. -/
theorem toGF_sqr (ha : a.Reduced) : a.sqr.toGF = a.toGF * a.toGF := by
  have h0 := ha.1; have h1 := ha.2.1; have h2 := ha.2.2
  simp only [toGF, sqr]
  fp2_push
  simp only [map_add, map_sub, map_mul]
  linear_combination (-(2 * of6 a.c1.toGF * of6 a.c2.toGF) -
    of6 a.c2.toGF * of6 a.c2.toGF * vGF) * v_cube

/-- The sparse product by `c1·v`. -/
theorem toGF_mulBy1 {c1 : Fp2} (ha : a.Reduced) (hc : c1.Reduced) :
    (a.mulBy1 c1).toGF = a.toGF * (of6 c1.toGF * vGF) := by
  have h0 := ha.1; have h1 := ha.2.1; have h2 := ha.2.2
  simp only [toGF, mulBy1]
  fp2_push
  simp only [map_mul]
  linear_combination (-(of6 a.c2.toGF * of6 c1.toGF)) * v_cube

/-- The sparse product by `c0 + c1·v`. -/
theorem toGF_mulBy01 {c0 c1 : Fp2} (ha : a.Reduced) (hc0 : c0.Reduced) (hc1 : c1.Reduced) :
    (a.mulBy01 c0 c1).toGF = a.toGF * (of6 c0.toGF + of6 c1.toGF * vGF) := by
  have h0 := ha.1; have h1 := ha.2.1; have h2 := ha.2.2
  simp only [toGF, mulBy01]
  fp2_push
  simp only [map_add, map_sub, map_mul]
  linear_combination (-(of6 a.c2.toGF * of6 c1.toGF)) * v_cube

/-- `Fp6.eq` is the field's equality, on reduced values. -/
theorem eq_iff (ha : a.Reduced) (hb : b.Reduced) : a.eq b = true ↔ a.toGF = b.toGF := by
  rw [toGF_inj ha hb]
  obtain ⟨a0, a1, a2⟩ := a; obtain ⟨b0, b1, b2⟩ := b
  simp only [eq, Bool.and_eq_true, mk.injEq]
  rw [Fp2.eq_iff ha.1 hb.1, Fp2.eq_iff ha.2.1 hb.2.1, Fp2.eq_iff ha.2.2 hb.2.2,
    Fp2.toGF_inj ha.1 hb.1, Fp2.toGF_inj ha.2.1 hb.2.1, Fp2.toGF_inj ha.2.2 hb.2.2, and_assoc]

/-- `Fp6.isZero` is the field's test for zero, on reduced values. -/
theorem isZero_iff (ha : a.Reduced) : a.isZero = true ↔ a.toGF = 0 := by
  rw [← toGF_zero, toGF_inj ha reduced_zero]
  obtain ⟨a0, a1, a2⟩ := a
  simp only [isZero, Bool.and_eq_true, zero, mk.injEq]
  rw [Fp2.isZero_iff ha.1, Fp2.isZero_iff ha.2.1, Fp2.isZero_iff ha.2.2, ← Fp2.toGF_zero,
    Fp2.toGF_inj ha.1 Fp2.reduced_zero, Fp2.toGF_inj ha.2.1 Fp2.reduced_zero,
    Fp2.toGF_inj ha.2.2 Fp2.reduced_zero, and_assoc]

theorem reduced_mulBy1 {c1 : Fp2} : (a.mulBy1 c1).Reduced :=
  ⟨Fp2.reduced_mulXi Fp2.reduced_mul, Fp2.reduced_mul, Fp2.reduced_mul⟩

theorem reduced_mulBy01 (ha : a.Reduced) {c0 c1 : Fp2} : (a.mulBy01 c0 c1).Reduced := by
  have := ha.1
  refine ⟨?_, ?_, ?_⟩ <;> simp only [mulBy01] <;> fp2_reduced

/-- `Fp6.inv`'s norm identity: `a·(c0 + c1·v + c2·v²) = t`, with its `c0`, `c1`, `c2`, `t`. -/
theorem inv_norm (ha : a.Reduced) :
    a.toGF * (of6 (a.c0.sqr.sub (a.c1.mul a.c2).mulXi).toGF +
        of6 (a.c2.sqr.mulXi.sub (a.c0.mul a.c1)).toGF * vGF +
        of6 (a.c1.sqr.sub (a.c0.mul a.c2)).toGF * vGF ^ 2) =
      of6 (((a.c2.mul (a.c2.sqr.mulXi.sub (a.c0.mul a.c1))).add
        (a.c1.mul (a.c1.sqr.sub (a.c0.mul a.c2)))).mulXi.add
        (a.c0.mul (a.c0.sqr.sub (a.c1.mul a.c2).mulXi))).toGF := by
  have h0 := ha.1; have h1 := ha.2.1; have h2 := ha.2.2
  simp only [toGF]
  fp2_push
  simp only [map_add, map_sub, map_mul]
  linear_combination (of6 a.c1.toGF * (of6 a.c1.toGF * of6 a.c1.toGF -
      of6 a.c0.toGF * of6 a.c2.toGF) + of6 a.c2.toGF * (of6 ⟨1, 1⟩ * of6 a.c2.toGF *
      of6 a.c2.toGF - of6 a.c0.toGF * of6 a.c1.toGF) + (of6 a.c2.toGF * (of6 a.c1.toGF *
      of6 a.c1.toGF - of6 a.c0.toGF * of6 a.c2.toGF)) * vGF) * v_cube

/-- If `a1² = a0·a2`, `ξ·a2² = a0·a1` and `a0² = ξ·a1·a2` in `𝔽_{p²}`, then `a = 0`: else
`ξ = (a1/a2)³`. -/
theorem zero_of_adj {a0 a1 a2 : GFp2} (h0 : a0 * a0 - ⟨1, 1⟩ * (a1 * a2) = 0)
    (h1 : ⟨1, 1⟩ * (a2 * a2) - a0 * a1 = 0) (h2 : a1 * a1 - a0 * a2 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  by_cases ha2 : a2 = 0
  · subst ha2
    have h1' : a1 = 0 := mul_self_eq_zero.mp (by simpa using h2)
    subst h1'
    exact ⟨mul_self_eq_zero.mp (by simpa using h0), rfl, rfl⟩
  · exfalso
    apply xi_not_cube (a1 * a2⁻¹)
    have hinv : a2 * a2⁻¹ = 1 := mul_inv_cancel₀ ha2
    linear_combination a2⁻¹ ^ 3 * a1 * h2 - a2⁻¹ ^ 3 * a2 * h1 +
      (⟨1, 1⟩ : GFp2) * ((a2 * a2⁻¹) ^ 2 + a2 * a2⁻¹ + 1) * hinv

/-- An inverse through a norm: if `x·c = t` in `𝔽_{p²}`, and `c = 0` only when `x = 0`, then
`t⁻¹·c = x⁻¹` (both `0` when `x = 0`). -/
theorem inv_of_norm {x c : GFp6} {t : GFp2} (h : x * c = of6 t) (hz : c = 0 → x = 0) :
    of6 t⁻¹ * c = x⁻¹ := by
  by_cases ht : t = 0
  · subst ht
    rw [inv_zero, map_zero, zero_mul]
    rw [map_zero, mul_eq_zero] at h
    rcases h with h | h
    · rw [h, inv_zero]
    · rw [hz h, inv_zero]
  · have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_mul, eq_comm, map_eq_zero_iff _ (AdjoinRoot.of fp6Poly).injective] at h
      exact ht h
    refine eq_inv_of_mul_eq_one_left ?_
    rw [show of6 t⁻¹ * c * x = of6 t⁻¹ * (x * c) by ring, h, ← map_mul, inv_mul_cancel₀ ht,
      map_one]

/-- The inverse through the norm to `𝔽_{p²}` is the field's (`0` to `0`). -/
theorem toGF_inv (ha : a.Reduced) : a.inv.toGF = a.toGF⁻¹ := by
  have h0 := ha.1; have h1 := ha.2.1; have h2 := ha.2.2
  have hn := inv_norm ha
  have e : a.inv.toGF = of6 ((((a.c2.mul (a.c2.sqr.mulXi.sub (a.c0.mul a.c1))).add
        (a.c1.mul (a.c1.sqr.sub (a.c0.mul a.c2)))).mulXi.add
        (a.c0.mul (a.c0.sqr.sub (a.c1.mul a.c2).mulXi))).toGF)⁻¹ *
      (of6 (a.c0.sqr.sub (a.c1.mul a.c2).mulXi).toGF +
        of6 (a.c2.sqr.mulXi.sub (a.c0.mul a.c1)).toGF * vGF +
        of6 (a.c1.sqr.sub (a.c0.mul a.c2)).toGF * vGF ^ 2) := by
    simp only [inv, toGF]
    rw [Fp2.toGF_mul (by fp2_reduced) Fp2.reduced_inv, Fp2.toGF_mul (by fp2_reduced) Fp2.reduced_inv,
      Fp2.toGF_mul (by fp2_reduced) Fp2.reduced_inv, Fp2.toGF_inv]
    simp only [map_mul]; ring
  rw [e]
  refine inv_of_norm hn fun hc => ?_
  obtain ⟨z0, z1, z2⟩ := tower6_eq_zero hc
  fp2_push at z0 z1 z2
  obtain ⟨e0, e1, e2⟩ := zero_of_adj z0 z1 z2
  simp only [toGF, e0, e1, e2, map_zero, zero_mul, add_zero]

end Fp6

/-- Proves a runtime `Fp6` reduced from its operations and the hypotheses in context. -/
syntax "fp6_reduced" : tactic
macro_rules
  | `(tactic| fp6_reduced) => `(tactic| with_reducible first
    | assumption | exact Fp6.reduced_inv | exact Fp6.reduced_mulFp2 _ | exact Fp6.reduced_zero
    | exact Fp6.reduced_one
    | (apply Fp6.reduced_add <;> fp6_reduced) | (apply Fp6.reduced_sub; fp6_reduced)
    | (apply Fp6.reduced_neg; fp6_reduced) | (apply Fp6.reduced_dbl; fp6_reduced)
    | (apply Fp6.reduced_mul <;> fp6_reduced) | (apply Fp6.reduced_sqr; fp6_reduced)
    | (apply Fp6.reduced_mulV; fp6_reduced) | exact Fp6.reduced_mulBy1
    | (apply Fp6.reduced_mulBy01; fp6_reduced))

/-! ## The runtime's `Fp12` -/

namespace Fp12

/-- The element `c0 + c1·w` of `𝔽_{p¹²}` a runtime `Fp12` stands for. -/
noncomputable def toGF (a : Fp12) : GFp12 := ⟨a.c0.toGF, a.c1.toGF⟩

/-- Both coordinates reduced. -/
def Reduced (a : Fp12) : Prop := a.c0.Reduced ∧ a.c1.Reduced

variable {a b : Fp12}

/-- On reduced values, `toGF` is injective. -/
theorem toGF_inj (ha : a.Reduced) (hb : b.Reduced) : a.toGF = b.toGF ↔ a = b := by
  obtain ⟨a0, a1⟩ := a; obtain ⟨b0, b1⟩ := b
  simp only [toGF, QuadraticAlgebra.mk.injEq, mk.injEq]
  rw [Fp6.toGF_inj ha.1 hb.1, Fp6.toGF_inj ha.2 hb.2]

theorem reduced_one : one.Reduced := ⟨Fp6.reduced_one, Fp6.reduced_zero⟩

@[simp] theorem toGF_one : one.toGF = 1 := by
  ext <;> simp [toGF, one]

theorem reduced_mul (ha : a.Reduced) (hb : b.Reduced) : (a.mul b).Reduced := by
  have := ha.1; have := ha.2; have := hb.1; have := hb.2
  refine ⟨?_, ?_⟩ <;> simp only [mul] <;> fp6_reduced

theorem reduced_sqr (ha : a.Reduced) : a.sqr.Reduced := by
  have := ha.1; have := ha.2
  refine ⟨?_, ?_⟩ <;> simp only [sqr] <;> fp6_reduced

theorem reduced_conj (ha : a.Reduced) : a.conj.Reduced := ⟨ha.1, Fp6.reduced_neg ha.2⟩

theorem reduced_inv (ha : a.Reduced) : a.inv.Reduced := by
  have := ha.1; have := ha.2
  refine ⟨?_, ?_⟩ <;> simp only [inv] <;> fp6_reduced

/-- The Karatsuba product is the field's. -/
theorem toGF_mul (ha : a.Reduced) (hb : b.Reduced) : (a.mul b).toGF = a.toGF * b.toGF := by
  have := ha.1; have := ha.2; have := hb.1; have := hb.2
  ext
  · simp only [toGF, mul, QuadraticAlgebra.re_mul]
    rw [Fp6.toGF_add, Fp6.toGF_mul ha.1 hb.1, Fp6.toGF_mulV (Fp6.reduced_mul ha.2 hb.2),
      Fp6.toGF_mul ha.2 hb.2]
    ring
  · simp only [toGF, mul, QuadraticAlgebra.im_mul]
    rw [Fp6.toGF_sub (by fp6_reduced), Fp6.toGF_sub (by fp6_reduced),
      Fp6.toGF_mul (by fp6_reduced) (by fp6_reduced), Fp6.toGF_add, Fp6.toGF_add,
      Fp6.toGF_mul ha.1 hb.1, Fp6.toGF_mul ha.2 hb.2]
    ring

/-- The complex squaring is the field's. -/
theorem toGF_sqr (ha : a.Reduced) : a.sqr.toGF = a.toGF * a.toGF := by
  have := ha.1; have := ha.2
  ext
  · simp only [toGF, sqr, QuadraticAlgebra.re_mul]
    rw [Fp6.toGF_sub (by fp6_reduced), Fp6.toGF_sub (by fp6_reduced),
      Fp6.toGF_mul (by fp6_reduced) (by fp6_reduced), Fp6.toGF_add, Fp6.toGF_add,
      Fp6.toGF_mulV ha.2, Fp6.toGF_mulV (Fp6.reduced_mul ha.1 ha.2), Fp6.toGF_mul ha.1 ha.2]
    ring
  · simp only [toGF, sqr, QuadraticAlgebra.im_mul]
    rw [Fp6.toGF_dbl, Fp6.toGF_mul ha.1 ha.2]
    ring

/-- The conjugate `c0 − c1·w` is `star`. -/
theorem toGF_conj (ha : a.Reduced) : a.conj.toGF = star a.toGF := by
  ext
  · simp [toGF, conj]
  · simp [toGF, conj, Fp6.toGF_neg ha.2]

/-- The inverse through the norm to `𝔽_{p⁶}` is the field's (`0` to `0`). -/
theorem toGF_inv (ha : a.Reduced) : a.inv.toGF = a.toGF⁻¹ := by
  have := ha.1; have := ha.2
  have hnorm : (a.c0.sqr.sub a.c1.sqr.mulV).toGF = QuadraticAlgebra.norm a.toGF := by
    rw [Fp6.toGF_sub (by fp6_reduced), Fp6.toGF_sqr ha.1, Fp6.toGF_mulV (Fp6.reduced_sqr ha.2),
      Fp6.toGF_sqr ha.2, QuadraticAlgebra.norm_def]
    simp [toGF]; ring
  have ht : (a.c0.sqr.sub a.c1.sqr.mulV).inv.toGF = (QuadraticAlgebra.norm a.toGF)⁻¹ := by
    rw [Fp6.toGF_inv (by fp6_reduced), hnorm]
  ext
  · simp only [toGF, inv, QuadraticAlgebra.inv_def, QuadraticAlgebra.re_smul,
      QuadraticAlgebra.re_star, smul_eq_mul]
    rw [Fp6.toGF_mul ha.1 Fp6.reduced_inv, ht]
    simp [toGF]; ring
  · simp only [toGF, inv, QuadraticAlgebra.inv_def, QuadraticAlgebra.im_smul,
      QuadraticAlgebra.im_star, smul_eq_mul]
    rw [Fp6.toGF_neg (Fp6.reduced_mul ha.2 Fp6.reduced_inv), Fp6.toGF_mul ha.2 Fp6.reduced_inv,
      ht]
    simp [toGF]; ring

/-- The sparse product by `c0 + c1·v + c4·v·w`, a Miller-loop line. -/
theorem toGF_mulBy014 {c0 c1 c4 : Fp2} (ha : a.Reduced) (h0 : c0.Reduced) (h1 : c1.Reduced)
    (h4 : c4.Reduced) :
    (a.mulBy014 c0 c1 c4).toGF =
      a.toGF * ⟨of6 c0.toGF + of6 c1.toGF * vGF, of6 c4.toGF * vGF⟩ := by
  have := ha.1; have := ha.2
  have h14 : (c1.add c4).Reduced := Fp2.reduced_add h1 h4
  have hs : (a.c1.add a.c0).Reduced := Fp6.reduced_add ha.2 ha.1
  ext
  · simp only [toGF, mulBy014, QuadraticAlgebra.re_mul]
    rw [Fp6.toGF_add, Fp6.toGF_mulV (Fp6.reduced_mulBy1), Fp6.toGF_mulBy1 ha.2 h4,
      Fp6.toGF_mulBy01 ha.1 h0 h1]
    ring
  · simp only [toGF, mulBy014, QuadraticAlgebra.im_mul]
    rw [Fp6.toGF_sub (Fp6.reduced_mulBy1), Fp6.toGF_sub (Fp6.reduced_mulBy01 ha.1),
      Fp6.toGF_mulBy01 hs h0 h14, Fp6.toGF_mulBy01 ha.1 h0 h1, Fp6.toGF_mulBy1 ha.2 h4,
      Fp6.toGF_add, Fp2.toGF_add]
    simp only [map_add]; ring

/-- `Fp12.isOne` is the field's test for one, on reduced values. -/
theorem isOne_iff (ha : a.Reduced) : a.isOne = true ↔ a.toGF = 1 := by
  rw [← toGF_one, toGF_inj ha reduced_one]
  obtain ⟨a0, a1⟩ := a
  simp only [isOne, eq, Bool.and_eq_true, one, mk.injEq]
  rw [Fp6.eq_iff ha.1 Fp6.reduced_one, Fp6.eq_iff ha.2 Fp6.reduced_zero,
    Fp6.toGF_inj ha.1 Fp6.reduced_one, Fp6.toGF_inj ha.2 Fp6.reduced_zero]

end Fp12

/-! ## EthLib's `Fp6` and `Fp12`, by values -/

open LeanLight.Lc.Bls.Provenance (ofEth)

/-- EthLib's `Fp6` as the runtime's. -/
def ofEth6 (a : EthLib.Cryptography.Bls.Fp6) : Fp6 := ⟨ofEth a.c0, ofEth a.c1, ofEth a.c2⟩

/-- EthLib's `Fp12` as the runtime's. -/
def ofEth12 (a : EthLib.Cryptography.Bls.Fp12) : Fp12 := ⟨ofEth6 a.c0, ofEth6 a.c1⟩

theorem reduced_ofEth6 (a : EthLib.Cryptography.Bls.Fp6) : (ofEth6 a).Reduced :=
  ⟨Fp2.reduced_ofEth _, Fp2.reduced_ofEth _, Fp2.reduced_ofEth _⟩

theorem reduced_ofEth12 (a : EthLib.Cryptography.Bls.Fp12) : (ofEth12 a).Reduced :=
  ⟨reduced_ofEth6 _, reduced_ofEth6 _⟩

theorem ofEth6_inj {a b : EthLib.Cryptography.Bls.Fp6} : ofEth6 a = ofEth6 b ↔ a = b := by
  obtain ⟨a0, a1, a2⟩ := a; obtain ⟨b0, b1, b2⟩ := b
  simp only [ofEth6, Fp6.mk.injEq, EthLib.Cryptography.Bls.Fp6.mk.injEq, Fp2.ofEth_inj]

theorem ofEth12_inj {a b : EthLib.Cryptography.Bls.Fp12} : ofEth12 a = ofEth12 b ↔ a = b := by
  obtain ⟨a0, a1⟩ := a; obtain ⟨b0, b1⟩ := b
  simp only [ofEth12, Fp12.mk.injEq, EthLib.Cryptography.Bls.Fp12.mk.injEq, ofEth6_inj]

/-- Pushes `toGF ∘ ofEth` through EthLib's `Fp2` operations. -/
macro "eth_push" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_sub, Fp2.toGF_ofEth_neg, Fp2.toGF_ofEth_mul,
    Fp2.toGF_ofEth_mulByOnePlusI, Fp2.toGF_ofEth_conjugate, Fp2.toGF_ofEth_inverse]
    $(loc)?)

section EthLib


variable (a b : EthLib.Cryptography.Bls.Fp6)

theorem toGF_ofEth6_add : (ofEth6 (a + b)).toGF = (ofEth6 a).toGF + (ofEth6 b).toGF := by
  show (ofEth6 (EthLib.Cryptography.Bls.Fp6.add a b)).toGF = _
  simp only [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.add]; eth_push; simp only [map_add]; ring

theorem toGF_ofEth6_sub : (ofEth6 (a - b)).toGF = (ofEth6 a).toGF - (ofEth6 b).toGF := by
  show (ofEth6 (EthLib.Cryptography.Bls.Fp6.sub a b)).toGF = _
  simp only [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.sub]; eth_push; simp only [map_sub]; ring

theorem toGF_ofEth6_neg : (ofEth6 (-a)).toGF = -(ofEth6 a).toGF := by
  show (ofEth6 (EthLib.Cryptography.Bls.Fp6.neg a)).toGF = _
  simp only [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.neg]; eth_push; simp only [map_neg]; ring

theorem toGF_ofEth6_mul : (ofEth6 (a * b)).toGF = (ofEth6 a).toGF * (ofEth6 b).toGF := by
  show (ofEth6 (EthLib.Cryptography.Bls.Fp6.mul a b)).toGF = _
  simp only [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.mul]; eth_push; simp only [map_add, map_sub, map_mul]
  linear_combination (-(of6 (ofEth a.c1).toGF * of6 (ofEth b.c2).toGF +
    of6 (ofEth a.c2).toGF * of6 (ofEth b.c1).toGF) -
    of6 (ofEth a.c2).toGF * of6 (ofEth b.c2).toGF * vGF) * v_cube

theorem toGF_ofEth6_mulByV : (ofEth6 a.mulByV).toGF = vGF * (ofEth6 a).toGF := by
  simp only [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.mulByV]; eth_push; simp only [map_mul]
  linear_combination (-(of6 (ofEth a.c2).toGF)) * v_cube

@[simp] theorem toGF_ofEth6_one : (ofEth6 EthLib.Cryptography.Bls.Fp6.one).toGF = 1 := by
  simp [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.one, EthLib.Cryptography.Bls.Fp2.one,
    EthLib.Cryptography.Bls.Fp2.zero, ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp.one,
    EthLib.Cryptography.Bls.Fp.zero]

@[simp] theorem toGF_ofEth6_zero : (ofEth6 EthLib.Cryptography.Bls.Fp6.zero).toGF = 0 := by
  simp [ofEth6, Fp6.toGF, EthLib.Cryptography.Bls.Fp6.zero, EthLib.Cryptography.Bls.Fp2.zero, ofEth, Fp2.toGF,
    EthLib.Cryptography.Bls.Fp.zero]

/-! The runtime's `Fp6` operations on EthLib's values give EthLib's. -/

theorem Fp6.add_ofEth6 : (ofEth6 a).add (ofEth6 b) = ofEth6 (a + b) := by
  rw [← LeanLight.Lc.Bls.Fp6.toGF_inj (LeanLight.Lc.Bls.Fp6.reduced_add (reduced_ofEth6 a)
    (reduced_ofEth6 b)) (reduced_ofEth6 _), LeanLight.Lc.Bls.Fp6.toGF_add, toGF_ofEth6_add]

theorem Fp6.sub_ofEth6 : (ofEth6 a).sub (ofEth6 b) = ofEth6 (a - b) := by
  rw [← LeanLight.Lc.Bls.Fp6.toGF_inj (LeanLight.Lc.Bls.Fp6.reduced_sub (reduced_ofEth6 a))
    (reduced_ofEth6 _), LeanLight.Lc.Bls.Fp6.toGF_sub (reduced_ofEth6 b), toGF_ofEth6_sub]

theorem Fp6.neg_ofEth6 : (ofEth6 a).neg = ofEth6 (-a) := by
  rw [← LeanLight.Lc.Bls.Fp6.toGF_inj (LeanLight.Lc.Bls.Fp6.reduced_neg (reduced_ofEth6 a))
    (reduced_ofEth6 _), LeanLight.Lc.Bls.Fp6.toGF_neg (reduced_ofEth6 a), toGF_ofEth6_neg]

/-- The runtime's interpolated product is EthLib's. -/
theorem Fp6.mul_ofEth6 : (ofEth6 a).mul (ofEth6 b) = ofEth6 (a * b) := by
  rw [← LeanLight.Lc.Bls.Fp6.toGF_inj (LeanLight.Lc.Bls.Fp6.reduced_mul (reduced_ofEth6 a)
    (reduced_ofEth6 b)) (reduced_ofEth6 _),
    LeanLight.Lc.Bls.Fp6.toGF_mul (reduced_ofEth6 a) (reduced_ofEth6 b), toGF_ofEth6_mul]

/-- The runtime's Chung–Hasan squaring is EthLib's `a * a`. -/
theorem Fp6.sqr_ofEth6 : (ofEth6 a).sqr = ofEth6 (a * a) := by
  rw [← LeanLight.Lc.Bls.Fp6.toGF_inj (LeanLight.Lc.Bls.Fp6.reduced_sqr (reduced_ofEth6 a))
    (reduced_ofEth6 _), LeanLight.Lc.Bls.Fp6.toGF_sqr (reduced_ofEth6 a), toGF_ofEth6_mul]

theorem Fp6.mulV_ofEth6 : (ofEth6 a).mulV = ofEth6 a.mulByV := by
  rw [← LeanLight.Lc.Bls.Fp6.toGF_inj (LeanLight.Lc.Bls.Fp6.reduced_mulV (reduced_ofEth6 a))
    (reduced_ofEth6 _), LeanLight.Lc.Bls.Fp6.toGF_mulV (reduced_ofEth6 a), toGF_ofEth6_mulByV]

variable (x y : EthLib.Cryptography.Bls.Fp12)

theorem toGF_ofEth12_mul : (ofEth12 (x * y)).toGF = (ofEth12 x).toGF * (ofEth12 y).toGF := by
  show (ofEth12 (EthLib.Cryptography.Bls.Fp12.mul x y)).toGF = _
  ext
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.mul, QuadraticAlgebra.re_mul]
    rw [toGF_ofEth6_add, toGF_ofEth6_mul, toGF_ofEth6_mulByV, toGF_ofEth6_mul]; ring
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.mul, QuadraticAlgebra.im_mul]
    rw [toGF_ofEth6_sub, toGF_ofEth6_sub, toGF_ofEth6_mul, toGF_ofEth6_add, toGF_ofEth6_add,
      toGF_ofEth6_mul, toGF_ofEth6_mul]; ring

theorem toGF_ofEth12_conjugate : (ofEth12 x.conjugate).toGF = star (ofEth12 x).toGF := by
  ext
  · simp [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.conjugate]
  · simp only [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.conjugate, QuadraticAlgebra.im_star]
    rw [toGF_ofEth6_neg]

@[simp] theorem toGF_ofEth12_one : (ofEth12 EthLib.Cryptography.Bls.Fp12.one).toGF = 1 := by
  ext <;> simp [ofEth12, Fp12.toGF, EthLib.Cryptography.Bls.Fp12.one]

/-- EthLib's square and multiply in `Fp12` is the power. -/
theorem toGF_ofEth12_powNat (n : ℕ) : (ofEth12 (x.powNat n)).toGF = (ofEth12 x).toGF ^ n := by
  induction n using Nat.strongRecOn generalizing x with
  | _ n ih =>
    rw [EthLib.Cryptography.Bls.Fp12.powNat]
    split
    · rename_i h; subst h; rw [toGF_ofEth12_one, pow_zero]
    · rename_i h
      have hh := ih (n / 2) (by omega) (x * x)
      split
      · rw [toGF_ofEth12_mul, hh, toGF_ofEth12_mul, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1; omega
      · rw [hh, toGF_ofEth12_mul, ← pow_two, ← pow_mul]
        congr 1; omega

/-- EthLib's `Fp12.isOne` is the field's test for one. -/
theorem isOne_ofEth12_iff : x.isOne = true ↔ (ofEth12 x).toGF = 1 := by
  rw [← toGF_ofEth12_one, LeanLight.Lc.Bls.Fp12.toGF_inj (reduced_ofEth12 x) (reduced_ofEth12 _),
    ofEth12_inj]
  obtain ⟨⟨⟨a0, a1⟩, ⟨a2, a3⟩, ⟨a4, a5⟩⟩, ⟨⟨b0, b1⟩, ⟨b2, b3⟩, ⟨b4, b5⟩⟩⟩ := x
  simp only [EthLib.Cryptography.Bls.Fp12.isOne, EthLib.Cryptography.Bls.Fp6.beq,
    EthLib.Cryptography.Bls.Fp6.isZero, EthLib.Cryptography.Bls.Fp2.beq,
    EthLib.Cryptography.Bls.Fp2.isZero, EthLib.Cryptography.Bls.Fp.beq,
    EthLib.Cryptography.Bls.Fp.isZero, EthLib.Cryptography.Bls.Fp12.one,
    EthLib.Cryptography.Bls.Fp6.one, EthLib.Cryptography.Bls.Fp6.zero,
    EthLib.Cryptography.Bls.Fp2.one, EthLib.Cryptography.Bls.Fp2.zero,
    EthLib.Cryptography.Bls.Fp.one, EthLib.Cryptography.Bls.Fp.zero,
    EthLib.Cryptography.Bls.Fp12.mk.injEq, EthLib.Cryptography.Bls.Fp6.mk.injEq,
    EthLib.Cryptography.Bls.Fp2.mk.injEq, Bool.and_eq_true, beq_iff_eq, Fin.ext_iff]
  tauto

/-- The runtime's Karatsuba product in `Fp12` is EthLib's. -/
theorem Fp12.mul_ofEth12 : (ofEth12 x).mul (ofEth12 y) = ofEth12 (x * y) := by
  rw [← LeanLight.Lc.Bls.Fp12.toGF_inj (LeanLight.Lc.Bls.Fp12.reduced_mul (reduced_ofEth12 x)
    (reduced_ofEth12 y)) (reduced_ofEth12 _),
    LeanLight.Lc.Bls.Fp12.toGF_mul (reduced_ofEth12 x) (reduced_ofEth12 y), toGF_ofEth12_mul]

/-- The runtime's complex squaring in `Fp12` is EthLib's `x * x`. -/
theorem Fp12.sqr_ofEth12 : (ofEth12 x).sqr = ofEth12 (x * x) := by
  rw [← LeanLight.Lc.Bls.Fp12.toGF_inj (LeanLight.Lc.Bls.Fp12.reduced_sqr (reduced_ofEth12 x))
    (reduced_ofEth12 _), LeanLight.Lc.Bls.Fp12.toGF_sqr (reduced_ofEth12 x), toGF_ofEth12_mul]

theorem Fp12.conj_ofEth12 : (ofEth12 x).conj = ofEth12 x.conjugate := by
  rw [← LeanLight.Lc.Bls.Fp12.toGF_inj (LeanLight.Lc.Bls.Fp12.reduced_conj (reduced_ofEth12 x))
    (reduced_ofEth12 _), LeanLight.Lc.Bls.Fp12.toGF_conj (reduced_ofEth12 x),
    toGF_ofEth12_conjugate]

end EthLib

end LeanLight.Lc.Bls
