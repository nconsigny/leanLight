import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Hasse's bound for `y² = x³ + b` (25c)

Over a finite field `F` of `q` elements, with `q` odd, `3 ∣ q − 1` and `b ≠ 0`, an affine curve
`W` whose nonsingular points are exactly the solutions of `y² = x³ + b` has `N` points (the
identity included) with

  `(N − (q + 1))² ≤ 4q`   (`card_sub_sq_le`),

Hasse's bound for these curves. The proof, after gattaca-com/silver's `Spec/CubicHasse.lean`
(MIT), is the classical one by Jacobi sums, all of it Mathlib's number theory:

* `N = q + 1 + S` with `S = Σₓ φ(x³ + b)` for the quadratic character `φ` of `F`
  (`card_eq_character_sum`): each `x` has `1 + φ(x³ + b)` square roots of `x³ + b`.
* With a character `χ` of order 3 into `ℂ` (one exists since `3 ∣ q − 1`), `t` has
  `1 + χ(t) + χ⁻¹(t)` cube roots (`card_cube_fiber`), so
  `S = χ(−b)φ(b)·J(χ, φ) + χ⁻¹(−b)φ(b)·J(χ⁻¹, φ)` (`sum_cube_eq_jacobiSum`).
* Each Jacobi sum has absolute value `√q` (`norm_jacobiSum`, Mathlib's
  `jacobiSum_mul_jacobiSum_inv`), the characters' values absolute value one, so `|S| ≤ 2√q`.

`LeanLightProofs.Bls.PointCount` applies it to `E(𝔽_p)` and `E'(𝔽_{p²})`.
-/

namespace LeanLight.Lc.Bls.Hasse

open MulChar WeierstrassCurve

/-! ## Characters into `ℂ` -/

section Char

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- `F`'s quadratic character, with values in `ℂ`. -/
noncomputable def quadraticCharComplex : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharComplex_apply (a : F) :
    quadraticCharComplex F a = (quadraticChar F a : ℂ) := rfl

theorem quadraticCharComplex_ne_one (hF : ringChar F ≠ 2) : quadraticCharComplex F ≠ 1 := by
  apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
  exact quadraticChar_ne_one hF

theorem quadraticCharComplex_sq : quadraticCharComplex F ^ 2 = 1 := by
  rw [quadraticCharComplex, MulChar.ringHomComp_pow, (quadraticChar_isQuadratic F).sq_eq_one,
    MulChar.ringHomComp_one]

theorem orderOf_quadraticCharComplex (hF : ringChar F ≠ 2) :
    orderOf (quadraticCharComplex F) = 2 :=
  orderOf_eq_prime (quadraticCharComplex_sq F) (quadraticCharComplex_ne_one F hF)

theorem cubic_mul_quadratic_ne_one {χ : MulChar F ℂ} (hχ : orderOf χ = 3)
    (hF : ringChar F ≠ 2) : χ * quadraticCharComplex F ≠ 1 := by
  intro h
  have he : χ = (quadraticCharComplex F)⁻¹ := mul_eq_one_iff_eq_inv.mp h
  have ho := congrArg orderOf he
  rw [hχ, orderOf_inv, orderOf_quadraticCharComplex F hF] at ho
  exact absurd ho (by decide)

omit [DecidableEq F] in
/-- A character of order 3 into `ℂ`, when `3 ∣ q − 1`. -/
theorem exists_cubicChar (h3 : 3 ∣ Fintype.card F - 1) : ∃ χ : MulChar F ℂ, orderOf χ = 3 :=
  MulChar.exists_mulChar_orderOf F h3 (Complex.isPrimitiveRoot_exp 3 (by decide))

end Char

/-! ## Norms of character values and Jacobi sums -/

section Norm

variable {F : Type*} [Field F] [Fintype F]

theorem norm_mulChar_apply_eq_one (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  classical
  obtain ⟨u, rfl⟩ := ha.isUnit
  simpa using Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem jacobiSum_inv_inv_eq_star (χ φ : MulChar F ℂ) :
    jacobiSum χ⁻¹ φ⁻¹ = star (jacobiSum χ φ) := by
  simp only [jacobiSum, star_sum, star_mul', star_apply']

theorem norm_jacobiSum_sq {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ ^ 2 = Fintype.card F := by
  have hc : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  have h := jacobiSum_mul_jacobiSum_inv hc hχ hφ hχφ
  rw [jacobiSum_inv_inv_eq_star, Complex.star_def, Complex.mul_conj'] at h
  exact_mod_cast h

/-- A Jacobi sum of two nontrivial characters whose product is nontrivial has absolute value
`√q`. -/
theorem norm_jacobiSum {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F) := by
  rw [← norm_jacobiSum_sq hχ hφ hχφ, Real.sqrt_sq (norm_nonneg _)]

end Norm

/-! ## Cube roots, through a character of order 3 -/

section Cube

variable {F : Type*} [Field F]

theorem mulChar_apply_eq_one_iff_exists_cube [Fintype F] {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) {t : F} (ht : t ≠ 0) : χ t = 1 ↔ ∃ a, a ^ 3 = t := by
  classical
  constructor
  · intro h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hpow : ∀ n : ℕ, equivToUnitHom χ g ^ n = 1 ↔ χ ^ n = 1 := by
      intro n
      rw [MulChar.eq_iff hg (χ ^ n) 1, pow_apply_coe, one_apply_coe, ← Units.val_eq_one,
        Units.val_pow_eq_pow_val, coe_equivToUnitHom]
    have hord : orderOf (equivToUnitHom χ g) = 3 := by
      rw [← hχ]
      exact orderOf_eq_orderOf_iff.mpr hpow
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 t ht))
    have hk1 : equivToUnitHom χ g ^ k = 1 := by
      rw [← map_zpow, hk]
      ext
      rw [coe_equivToUnitHom, Units.val_mk0, h1, Units.val_one]
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hk1
    rw [hord] at hd
    obtain ⟨m, rfl⟩ : (3 : ℤ) ∣ k := by exact_mod_cast hd
    have hcube : (g ^ m) ^ 3 = Units.mk0 t ht := by
      rw [← hk, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    refine ⟨((g ^ m : Fˣ) : F), ?_⟩
    rw [← Units.val_pow_eq_pow_val, hcube, Units.val_mk0]
  · rintro ⟨a, rfl⟩
    have ha : a ≠ 0 := fun h => ht (by rw [h, zero_pow three_ne_zero])
    have h3 : χ ^ 3 = 1 := by
      rw [← hχ]
      exact pow_orderOf_eq_one χ
    rw [map_pow, ← χ.pow_apply' three_ne_zero, h3, MulChar.one_apply ha.isUnit]

theorem exists_isPrimitiveRoot_three [Fintype F] (h : 3 ∣ Fintype.card F - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) 3 (by rwa [Fintype.card_units])
  exact ⟨(g : F), IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hg)⟩

theorem card_cube_fiber_zero : Nat.card {x : F // x ^ 3 = 0} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨0, zero_pow three_ne_zero⟩,
    fun y => Subtype.ext ((pow_eq_zero_iff three_ne_zero).mp y.2)⟩

theorem card_cube_fiber_of_cube {ζ : F} (hζ : IsPrimitiveRoot ζ 3) {t : F} (ht : t ≠ 0)
    (h : ∃ a, a ^ 3 = t) : Nat.card {x : F // x ^ 3 = t} = 3 := by
  classical
  have hcard := hζ.card_nthRoots t
  rw [ite_eq_left h] at hcard
  have e : {x : F // x ^ 3 = t} ≃ {x : F // x ∈ (Polynomial.nthRoots 3 t).toFinset} :=
    Equiv.subtypeEquivRight fun x => by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, Multiset.toFinset_card_of_nodup
    (hζ.nthRoots_nodup ht), hcard]

theorem card_cube_fiber_of_not_cube {t : F} (h : ¬ ∃ a, a ^ 3 = t) :
    Nat.card {x : F // x ^ 3 = t} = 0 := by
  have : IsEmpty {x : F // x ^ 3 = t} := ⟨fun x => h ⟨x.1, x.2⟩⟩
  exact Nat.card_of_isEmpty

/-- `t` has `1 + χ(t) + χ⁻¹(t)` cube roots in `F`, for `χ` of order 3. -/
theorem card_cube_fiber [Fintype F] {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (t : F) :
    (Nat.card {x : F // x ^ 3 = t} : ℂ) = 1 + χ t + χ⁻¹ t := by
  by_cases ht : t = 0
  · subst ht
    rw [card_cube_fiber_zero, MulChar.map_zero, MulChar.map_zero]
    norm_num
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three (F := F) (by
    rw [← hχ]
    exact MulChar.orderOf_dvd_card_sub_one F χ)
  have h3 : χ ^ 3 = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  have hz3 : χ t ^ 3 = 1 := by
    rw [← χ.pow_apply' three_ne_zero, h3, MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)]
  have hz0 : χ t ≠ 0 := fun h => by
    rw [h, zero_pow three_ne_zero] at hz3
    exact zero_ne_one hz3
  rw [MulChar.inv_apply_eq_inv']
  by_cases hc : ∃ a, a ^ 3 = t
  · rw [card_cube_fiber_of_cube hζ ht hc, (mulChar_apply_eq_one_iff_exists_cube hχ ht).mpr hc]
    norm_num
  · rw [card_cube_fiber_of_not_cube hc, Nat.cast_zero]
    have hne : χ t ≠ 1 := fun h => hc ((mulChar_apply_eq_one_iff_exists_cube hχ ht).mp h)
    have key : (χ t - 1) * (1 + χ t + χ t ^ 2) = 0 := by linear_combination hz3
    have hq : 1 + χ t + χ t ^ 2 = 0 :=
      (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr hne)
    have hinv : χ t * (χ t)⁻¹ = 1 := mul_inv_cancel₀ hz0
    linear_combination (1 + χ t) * hinv - (χ t)⁻¹ * hq

end Cube

/-! ## The character sum as two Jacobi sums -/

section Sum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem sum_mulChar_shift (χ φ : MulChar F ℂ) {b : F} (hb : b ≠ 0) :
    ∑ t : F, χ t * φ (t + b) = χ (-b) * φ b * jacobiSum χ φ := by
  classical
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ (-b) (neg_ne_zero.mpr hb))]
  simp only [Equiv.mulLeft₀_apply]
  have he (u : F) : -b * u + b = b * (1 - u) := by ring
  simp_rw [he, map_mul]
  rw [jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem sum_cube_eq_jacobiSum (χ φ : MulChar F ℂ) (hφ : φ ≠ 1)
    (hcube : ∀ t : F, (Nat.card {x : F // x ^ 3 = t} : ℂ) = 1 + χ t + χ⁻¹ t)
    {b : F} (hb : b ≠ 0) :
    ∑ x : F, φ (x ^ 3 + b) =
      χ (-b) * φ b * jacobiSum χ φ + χ⁻¹ (-b) * φ b * jacobiSum χ⁻¹ φ := by
  classical
  have hf : ∑ x : F, φ (x ^ 3 + b) = ∑ t : F, (1 + χ t + χ⁻¹ t) * φ (t + b) := by
    rw [← Fintype.sum_fiberwise (fun x : F => x ^ 3) (fun x => φ (x ^ 3 + b))]
    apply Finset.sum_congr rfl
    intro t _
    simp only [show ∀ x : {x : F // x ^ 3 = t}, (x : F) ^ 3 = t from fun x => x.property,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hcube]
  rw [hf]
  simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
  have hz : ∑ t : F, φ (t + b) = 0 :=
    (Equiv.sum_comp (Equiv.addRight b) φ).trans (MulChar.sum_eq_zero_of_ne_one hφ)
  rw [hz, zero_add, sum_mulChar_shift χ φ hb, sum_mulChar_shift χ⁻¹ φ hb]

/-- `|Σₓ φ(x³ + b)| ≤ 2√q` for the quadratic character `φ`, when `q` is odd, `3 ∣ q − 1` and
`b ≠ 0`. -/
theorem norm_character_sum_le (hF : ringChar F ≠ 2)
    (h3 : 3 ∣ Fintype.card F - 1) {b : F} (hb : b ≠ 0) :
    ‖∑ x : F, quadraticCharComplex F (x ^ 3 + b)‖ ≤ 2 * Real.sqrt (Fintype.card F) := by
  obtain ⟨χ, hχ⟩ := exists_cubicChar F h3
  set φ := quadraticCharComplex F
  have hφ : φ ≠ 1 := quadraticCharComplex_ne_one F hF
  have hχne : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hχ
    exact absurd hχ (by decide)
  have hinv : orderOf χ⁻¹ = 3 := by rw [orderOf_inv, hχ]
  rw [sum_cube_eq_jacobiSum χ φ hφ (fun t => card_cube_fiber hχ t) hb]
  calc
    _ ≤ ‖χ (-b) * φ b * jacobiSum χ φ‖ + ‖χ⁻¹ (-b) * φ b * jacobiSum χ⁻¹ φ‖ := norm_add_le _ _
    _ = Real.sqrt (Fintype.card F) + Real.sqrt (Fintype.card F) := by
      simp only [norm_mul, norm_mulChar_apply_eq_one _ (neg_ne_zero.mpr hb),
        norm_mulChar_apply_eq_one _ hb, one_mul]
      rw [norm_jacobiSum hχne hφ (cubic_mul_quadratic_ne_one F hχ hF),
        norm_jacobiSum (inv_ne_one.mpr hχne) hφ (cubic_mul_quadratic_ne_one F hinv hF)]
    _ = 2 * Real.sqrt (Fintype.card F) := by ring

end Sum

/-! ## Counting the points -/

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_solution_pairs (hF : ringChar F ≠ 2) (b : F) :
    (Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + b} : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (x ^ 3 + b) := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun x y : F => y ^ 2 = x ^ 3 + b)),
    Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
  have hroot (x : F) : (Fintype.card {y : F // y ^ 2 = x ^ 3 + b} : ℤ) =
      quadraticChar F (x ^ 3 + b) + 1 := by
    rw [← quadraticChar_card_sqrts hF (x ^ 3 + b), Set.toFinset_card]
    rfl
  simp only [hroot, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  ring

omit [DecidableEq F] in
/-- An affine curve over a finite field has finitely many points. -/
theorem finite_point (W : Affine F) : Finite W.Point :=
  Finite.of_equiv (Option {xy : F × F // W.Nonsingular xy.1 xy.2})
    (W.nonsingularPointEquiv.symm : Option _ ≃ W.Point)

/-- **The point count**: `N = q + 1 + Σₓ φ(x³ + b)`, for a curve whose nonsingular points are the
solutions of `y² = x³ + b`, `q` odd. -/
theorem card_eq_character_sum (hF : ringChar F ≠ 2) (W : Affine F) (b : F)
    (hW : ∀ x y : F, W.Nonsingular x y ↔ y ^ 2 = x ^ 3 + b) :
    (Nat.card W.Point : ℤ) = Fintype.card F + 1 + ∑ x : F, quadraticChar F (x ^ 3 + b) := by
  have he : W.Point ≃ WithZero {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + b} :=
    W.nonsingularPointEquiv.trans
      (Equiv.optionCongr (Equiv.subtypeEquivRight fun xy => hW xy.1 xy.2))
  have hfin : Finite {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + b} := inferInstance
  rw [Nat.card_congr he]
  rw [show Nat.card (WithZero {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + b}) =
      Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + b} + 1 from Finite.card_option]
  push_cast
  rw [card_solution_pairs hF b]
  ring

/-- **Hasse's bound** for `y² = x³ + b` over a field of `q` elements, `q` odd, `3 ∣ q − 1` and
`b ≠ 0`: a curve `W` whose nonsingular points are exactly the solutions of that equation has `N`
points, the identity included, with `(N − (q + 1))² ≤ 4q`. -/
theorem card_sub_sq_le (hF : ringChar F ≠ 2) (h3 : 3 ∣ Fintype.card F - 1) (W : Affine F)
    {b : F} (hb : b ≠ 0) (hW : ∀ x y : F, W.Nonsingular x y ↔ y ^ 2 = x ^ 3 + b) :
    ((Nat.card W.Point : ℤ) - (Fintype.card F + 1)) ^ 2 ≤ 4 * Fintype.card F := by
  set S : ℤ := ∑ x : F, quadraticChar F (x ^ 3 + b) with hS
  have hc := card_eq_character_sum hF W b hW
  have hS' : ((S : ℝ) : ℂ) = ∑ x : F, quadraticCharComplex F (x ^ 3 + b) := by
    simp only [hS, quadraticCharComplex_apply]
    push_cast
    rfl
  have hn := norm_character_sum_le hF h3 hb
  rw [← hS', Complex.norm_real, Real.norm_eq_abs] at hn
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have h2 : (S : ℝ) ^ 2 ≤ 4 * Fintype.card F := by
    have habs : |(S : ℝ)| ^ 2 ≤ (2 * Real.sqrt (Fintype.card F)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hn 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hq] at habs
    linarith
  have h2' : S ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by exact_mod_cast h2
  rw [hc]
  ring_nf
  ring_nf at h2'
  linarith

end Count

end LeanLight.Lc.Bls.Hasse
