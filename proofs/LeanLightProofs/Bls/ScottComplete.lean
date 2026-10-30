import LeanLightProofs.Bls.PointCount
import Mathlib.Tactic.Module

/-!
# BLS12-381: Scott's subgroup tests are sound and complete, on G1 and G2 (25c)

**G2.** `ψ(x, y) = (c_x·x̄, c_y·ȳ)` on `E'(𝔽_{p²})`, `c_x`, `c_y` the runtime's `psiX`, `psiY`
(`ψ = twist⁻¹ ∘ Frobenius ∘ twist`, `LeanLight.Bls.G2J.psi`), after gattaca-com/silver's
`Spec/Scott.lean`:

* `ψ` maps `E'` to itself and is a group endomorphism of `E'(𝔽_{p²})` (`psi`, an `→+`), from
  `c_x³ = c_y²` and `c_y²·b̄ = b`, checked by the kernel on the constants.
* `ψ²(x, y) = (ζx, −y)` with `ζ = N(c_x)` a primitive cube root of unity (`psi_psi`), and
  `P + φ(P) + φ²(P) = O` for `φ(x, y) = (ζx, y)` (`add_phi_add_phi_phi`, the line `Y = y`,
  the tangent at `x = 0`).
* **Soundness** (`G2.scott_sound`): `ψ(P) = [x]P` (`x = −X`) gives `[x⁴ − x² + 1]P = [r]P = O`,
  for every point.
* **Completeness** (`G2.scott_complete`): every point with `[r]P = O` is a multiple of the
  generator (`E2_torsion_mem`, from `#E'(𝔽_{p²}) = r·h₂`, `r ∤ h₂`), and `ψ(G) = [x]G`
  (`psi_acts`, the kernel running the runtime's test on the generator), so `ψ(P) = [x]P`.
* `G2.scott_iff`: `[r]P = O ↔ ψ(P) = [x]P` on every point of `E'(𝔽_{p²})`; as the runtime
  computes it, `G2A.inSubgroupPsi_eq`: on a reduced point of `E'`, `inSubgroupPsi` (its
  `ψ`, `mulA`, `neg` and `eq`) is `inSubgroup` (`[r]P = O`).

**G1.** `Scott.scott_complete`: on `E(𝔽_p)`, every point with `[r]P = O` has `σ(P) = −[x²]P`
(the generator generates them, `E1_torsion_mem`, and `beta_acts` checks it); with
`Scott.scott_sound` (`LeanLightProofs.Bls.Scott`), `Scott.scott_iff` for `x ≠ 0`, and as it runs,
`G1A.inSubgroupScott_eq`: on a reduced point of `E` with `x ≠ 0`, `inSubgroupScott` is
`inSubgroup`.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

local notation "aff1" => Point.toAffine E1
local notation "aff2" => Point.toAffine E2

namespace G2

/-- `E'` as an affine curve, whose points form the group. -/
abbrev A : WeierstrassCurve.Affine GFp2 := E2.toAffine

theorem a₁ : A.a₁ = 0 := rfl
theorem a₂ : A.a₂ = 0 := rfl
theorem a₃ : A.a₃ = 0 := rfl
theorem a₄ : A.a₄ = 0 := rfl

theorem negY_eq (x y : GFp2) : A.negY x y = -y := by simp [Affine.negY]

theorem nonsingular_iff {x y : GFp2} : A.Nonsingular x y ↔ y ^ 2 = x ^ 3 + ⟨4, 4⟩ :=
  E2_affine_nonsingular_iff x y

/-! ## The constants -/

/-- `c_x`, the runtime's `psiX`. -/
noncomputable abbrev cx : GFp2 := psiX.toGF

/-- `c_y`, the runtime's `psiY`. -/
noncomputable abbrev cy : GFp2 := psiY.toGF

theorem psiX_reduced : psiX.Reduced := ⟨by decide, by decide⟩
theorem psiY_reduced : psiY.Reduced := ⟨by decide, by decide⟩

theorem cx_cube : cx ^ 3 = cy ^ 2 := by
  have h1 := psiX_reduced
  have h2 := psiY_reduced
  have h : (psiX.mul psiX).mul psiX = psiY.mul psiY := by decide +kernel
  have := congrArg Fp2.toGF h
  fp2_push at this
  rw [pow_succ, sq, sq]; exact this

theorem cy_sq_star_b : cy ^ 2 * star (⟨4, 4⟩ : GFp2) = ⟨4, 4⟩ := by
  have h : (psiY.mul psiY).mul bTwist.conj = bTwist := by decide +kernel
  have hb : bTwist.Reduced := ⟨by decide, by decide⟩
  have := congrArg Fp2.toGF h
  fp2_push at this
  rw [toGF_bTwist] at this; rw [sq]; exact this

/-- `ζ = β²`, a primitive cube root of unity of `𝔽_p`, in `𝔽_{p²}`. -/
noncomputable def zeta : GFp2 := algebraMap GFp GFp2 (((beta * beta % P : ℕ) : GFp))

theorem toGF_ofNat0 (n : ℕ) : (⟨n, 0⟩ : Fp2).toGF = algebraMap GFp GFp2 (n : GFp) := by
  ext <;> simp [Fp2.toGF]

theorem cx_mul_star : cx * star cx = zeta := by
  have h : psiX.mul psiX.conj = ⟨beta * beta % P, 0⟩ := by decide +kernel
  have := congrArg Fp2.toGF h
  rw [Fp2.toGF_mul psiX_reduced (Fp2.reduced_conj psiX_reduced), Fp2.toGF_conj psiX_reduced,
    toGF_ofNat0] at this
  exact this

theorem cy_mul_star : cy * star cy = -1 := by
  have h : psiY.mul psiY.conj = ⟨P - 1, 0⟩ := by decide +kernel
  have := congrArg Fp2.toGF h
  rw [Fp2.toGF_mul psiY_reduced (Fp2.reduced_conj psiY_reduced), Fp2.toGF_conj psiY_reduced,
    toGF_ofNat0, Nat.cast_sub (by decide), ZMod.natCast_self, Nat.cast_one, zero_sub,
    map_neg, map_one] at this
  exact this

theorem zeta_sq_add : zeta ^ 2 + zeta + 1 = 0 := by
  have h : (((beta * beta % P) * (beta * beta % P) + beta * beta % P + 1 : ℕ) : GFp) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    decide +kernel
  push_cast at h
  have := congrArg (algebraMap GFp GFp2) h
  rw [map_zero] at this
  rw [zeta, ← this]
  simp only [map_add, map_mul, map_one, map_natCast]
  ring

theorem zeta_cube : zeta ^ 3 = 1 := by linear_combination (zeta - 1) * zeta_sq_add

theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  have := zeta_sq_add
  rw [h] at this
  have h3 : ((3 : ℕ) : GFp2) = 0 := by push_cast; linear_combination this
  have := congrArg QuadraticAlgebra.re h3
  simp only [QuadraticAlgebra.re_natCast, QuadraticAlgebra.re_zero] at this
  rw [cast_eq_zero (by decide)] at this
  exact absurd this (by decide)

theorem cx_ne_zero : cx ≠ 0 := by
  intro h; have := cx_mul_star; rw [h, zero_mul] at this
  exact zeta_ne_one (by
    have h2 := zeta_sq_add; rw [← this] at h2; norm_num at h2)

theorem cy_ne_zero : cy ≠ 0 := by
  intro h; have := cy_mul_star; rw [h, zero_mul] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem b_ne_zero : (⟨4, 4⟩ : GFp2) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [QuadraticAlgebra.re_zero] at this
  rw [show (4 : GFp) = ((4 : ℕ) : GFp) by norm_num, cast_eq_zero (by decide)] at this
  exact absurd this (by decide)

/-! ## ψ on points -/

theorem nonsingular_psi {x y : GFp2} (h : A.Nonsingular x y) :
    A.Nonsingular (cx * star x) (cy * star y) := by
  rw [nonsingular_iff] at h ⊢
  have hs := congrArg star h
  rw [star_pow, star_add, star_pow] at hs
  linear_combination cy ^ 2 * hs - star x ^ 3 * cx_cube + cy_sq_star_b

/-- `ψ(x, y) = (c_x·x̄, c_y·ȳ)` on `E'(𝔽_{p²})`, the identity fixed. -/
noncomputable def psiF : A.Point → A.Point
  | 0 => 0
  | .some x y h => .some (cx * star x) (cy * star y) (nonsingular_psi h)

theorem star_inj' {a b : GFp2} (h : star a = star b) : a = b := star_injective h

theorem psi_add (P Q : A.Point) : psiF (P + Q) = psiF P + psiF Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact (zero_add (psiF (.some x₂ y₂ h₂))).symm ▸ (congrArg psiF (zero_add _)).trans rfl
  · exact (add_zero (psiF (.some x₁ y₁ h₁))).symm ▸ (congrArg psiF (add_zero _)).trans rfl
  have hcx := cx_ne_zero
  have hcy := cy_ne_zero
  have hx : ∀ a b : GFp2, cx * star a = cx * star b ↔ a = b := fun a b => by
    rw [mul_right_inj' hcx]; exact ⟨star_inj', fun h => h ▸ rfl⟩
  have hy : ∀ a b : GFp2, cy * star a = -(cy * star b) ↔ a = -b := fun a b => by
    rw [← mul_neg, ← star_neg, mul_right_inj' hcy]; exact ⟨star_inj', fun h => h ▸ rfl⟩
  by_cases hxy : x₁ = x₂ ∧ y₁ = A.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    show (0 : A.Point) = Affine.Point.some (cx * star x₁) (cy * star y₁) _ +
      Affine.Point.some (cx * star x₂) (cy * star y₂) _
    rw [Affine.Point.add_of_Y_eq ((hx _ _).mpr hxy.1)
      (by rw [negY_eq]; rw [negY_eq] at hxy; exact (hy _ _).mpr hxy.2)]
  · have hxy' : ¬(cx * star x₁ = cx * star x₂ ∧
        cy * star y₁ = A.negY (cx * star x₂) (cy * star y₂)) := by
      rintro ⟨e1, e2⟩
      rw [negY_eq] at e2
      exact hxy ⟨(hx _ _).mp e1, by rw [negY_eq]; exact (hy _ _).mp e2⟩
    rw [Affine.Point.add_some hxy]
    show Affine.Point.some _ _ _ = Affine.Point.some (cx * star x₁) (cy * star y₁) _ +
      Affine.Point.some (cx * star x₂) (cy * star y₂) _
    rw [Affine.Point.add_some hxy', Affine.Point.some.injEq]
    -- the slope is multiplied by `c_y / c_x` and conjugated
    have hsl : A.slope (cx * star x₁) (cx * star x₂) (cy * star y₁) (cy * star y₂) =
        cy / cx * star (A.slope x₁ x₂ y₁ y₂) := by
      by_cases hx12 : x₁ = x₂
      · subst hx12
        have hy12 : y₁ ≠ A.negY x₁ y₂ := fun e => hxy ⟨rfl, e⟩
        have hy12' : cy * star y₁ ≠ A.negY (cx * star x₁) (cy * star y₂) := by
          rw [negY_eq]; rw [negY_eq] at hy12; exact fun e => hy12 ((hy _ _).mp e)
        rw [Affine.slope_of_Y_ne rfl hy12', Affine.slope_of_Y_ne rfl hy12]
        simp only [negY_eq]
        have hy0 : y₁ ≠ 0 := E2_y_ne_zero (nonsingular_iff.mp h₁)
        have hsy : star y₁ ≠ 0 := (star_ne_zero).mpr hy0
        have h2 : (2 : GFp2) ≠ 0 := two_ne_zero_GFp2
        rw [star_div₀]
        simp only [star_mul', star_pow, star_ofNat, star_neg, star_sub,
          mul_zero, zero_mul, add_zero, sub_zero]
        field_simp
        linear_combination (star x₁ ^ 2 * 2⁻¹ * 3) * cx_cube
      · have hx' : cx * star x₁ ≠ cx * star x₂ := fun e => hx12 ((hx _ _).mp e)
        rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx12, star_div₀, star_sub, star_sub]
        have h1 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
        have h1' : star x₁ - star x₂ ≠ 0 := by
          rw [← star_sub]; exact (star_ne_zero).mpr h1
        rw [div_mul_div_comm, div_eq_div_iff (by
          rw [← mul_sub]; exact mul_ne_zero hcx h1') (mul_ne_zero hcx h1')]
        ring
    simp only [Affine.addX, Affine.addY, Affine.negAddY, negY_eq, hsl]
    have hc : (cy / cx) ^ 2 = cx := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hcx)]
      linear_combination -cx_cube
    have hc' : cy = cy / cx * cx := (div_mul_cancel₀ cy hcx).symm
    obtain ⟨k, hk⟩ : ∃ k, cy / cx = k := ⟨_, rfl⟩
    rw [hk] at hc hc'
    rw [hk, hc']
    simp only [star_neg, star_add, star_mul', star_sub, star_pow, zero_mul, add_zero, sub_zero]
    generalize star (A.slope x₁ x₂ y₁ y₂) = S
    constructor
    · linear_combination (-S ^ 2) * hc
    · linear_combination (k * S ^ 3) * hc

/-- `ψ` as an endomorphism of `E'(𝔽_{p²})`. -/
noncomputable def psi : A.Point →+ A.Point where
  toFun := psiF
  map_zero' := rfl
  map_add' := psi_add

theorem psi_some {x y : GFp2} (h : A.Nonsingular x y) :
    psi (.some x y h) = .some (cx * star x) (cy * star y) (nonsingular_psi h) := rfl

/-! ## ψ² = −φ -/

theorem nonsingular_phi {x y : GFp2} (h : A.Nonsingular x y) : A.Nonsingular (zeta * x) y := by
  rw [nonsingular_iff] at h ⊢
  linear_combination h - x ^ 3 * zeta_cube

/-- `φ(x, y) = (ζx, y)`. -/
noncomputable def phi : A.Point → A.Point
  | 0 => 0
  | .some x y h => .some (zeta * x) y (nonsingular_phi h)

theorem psi_psi (P : A.Point) : psi (psi P) = -phi P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [psi_some, psi_some]
    show _ = -Affine.Point.some (zeta * x) y _
    rw [Affine.Point.neg_some, Affine.Point.some.injEq, negY_eq, star_mul', star_star,
      star_mul', star_star, ← mul_assoc, ← mul_assoc, cx_mul_star, cy_mul_star, neg_one_mul]
    exact ⟨rfl, rfl⟩

theorem phi_phi (P : A.Point) : phi (phi P) = psi (psi (psi (psi P))) := by
  rw [psi_psi P, map_neg, map_neg, psi_psi, neg_neg]

/-- `P + φ(P) + φ²(P) = O`: `(x, y)`, `(ζx, y)` and `(ζ²x, y)` lie on the line `Y = y`, the
tangent at `P` when `x = 0`. -/
theorem add_phi_add_phi_phi (P : A.Point) : P + phi P + phi (phi P) = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  by_cases hx : x = 0
  · subst hx
    have hφ : phi (.some 0 y h) = .some 0 y h := by
      simp only [phi, mul_zero]
    have hy0 : y ≠ 0 := E2_y_ne_zero (nonsingular_iff.mp h)
    have hy : y ≠ A.negY 0 y := by
      rw [negY_eq]
      intro e
      apply hy0
      have h2 : (2 : GFp2) * y = 0 := by linear_combination e
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero_GFp2
    have h2P : Affine.Point.some 0 y h + Affine.Point.some 0 y h = -Affine.Point.some 0 y h := by
      rw [Affine.Point.add_self_of_Y_ne hy, Affine.Point.neg_some, Affine.Point.some.injEq]
      simp [Affine.slope_of_Y_ne rfl hy, Affine.addX, Affine.addY, Affine.negAddY]
    rw [hφ, hφ, h2P, neg_add_cancel]
  · have hxζ : x ≠ zeta * x := by
      intro hxζ
      apply hx
      have h1 : (zeta - 1) * x = 0 := by linear_combination -hxζ
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr zeta_ne_one)
    have hs : Affine.Point.some x y h + phi (.some x y h) = -phi (phi (.some x y h)) := by
      simp only [phi]
      rw [Affine.Point.add_of_X_ne hxζ, Affine.Point.neg_some, Affine.Point.some.injEq]
      simp only [Affine.slope_of_X_ne hxζ, sub_self, zero_div, Affine.addX, Affine.addY,
        Affine.negAddY, negY_eq, zero_mul, add_zero, sub_zero, zero_add]
      constructor
      · linear_combination (-x) * zeta_sq_add
      · trivial
    rw [hs, neg_add_cancel]

/-! ## Soundness and completeness -/

theorem torsion_of_psi_eq_zsmul (k : ℤ) (P : A.Point) (h : psi P = k • P) :
    (k ^ 4 - k ^ 2 + 1) • P = 0 := by
  have h2 : psi (psi P) = (k * k) • P := by rw [h, map_zsmul, h, smul_smul]
  have h4 : psi (psi (psi (psi P))) = (k * k * (k * k)) • P := by
    rw [h2, map_zsmul, map_zsmul, h2, smul_smul]
  have hφ : phi P = -((k * k) • P) := by rw [← h2, psi_psi, neg_neg]
  have hl := add_phi_add_phi_phi P
  rw [phi_phi, h4, hφ] at hl
  calc (k ^ 4 - k ^ 2 + 1) • P = P + -((k * k) • P) + (k * k * (k * k)) • P := by module
    _ = 0 := hl

/-- `r = x⁴ − x² + 1`, for `x = −X`, in `ℤ`. -/
theorem R_eq_int : ((-(X : ℤ)) ^ 4 - (-(X : ℤ)) ^ 2 + 1) = (R : ℤ) := by
  norm_num [R, X]

/-- **Scott's test on G2 is sound**: a point `P` of `E'(𝔽_{p²})` with `ψ(P) = [x]P`
(`x = −X`) has `[r]P = O`. -/
theorem scott_sound (P : A.Point) (h : psi P = -(X • P)) : R • P = 0 := by
  have h' : psi P = (-(X : ℤ)) • P := by rw [h, neg_smul, natCast_zsmul]
  have := torsion_of_psi_eq_zsmul _ P h'
  rwa [R_eq_int, natCast_zsmul] at this

end G2

/-! ## The runtime's G2 test -/

namespace G2J

/-- The runtime's negation is the group's. -/
theorem neg_spec {p : G2J} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.neg.Reduced ∧ E2.Nonsingular p.neg.toJ ∧
      Point.toAffine E2 p.neg.toJ = -Point.toAffine E2 p.toJ := by
  have he : p.neg.toJ = E2.neg p.toJ := by
    funext i
    fin_cases i <;> simp [toJ, neg, Jacobian.neg, Jacobian.negY, Fp2.toGF_neg hp.2.1]
  refine ⟨⟨hp.1, Fp2.reduced_neg hp.2.1, hp.2.2⟩, by rw [he]; exact nonsingular_neg hn, ?_⟩
  rw [he, Point.toAffine_neg hn]

/-- The runtime's equality test on reduced nonsingular triples is equality of the points they
stand for. -/
theorem eq_iff {p q : G2J} (hp : p.Reduced) (hq : q.Reduced) (hnp : E2.Nonsingular p.toJ)
    (hnq : E2.Nonsingular q.toJ) :
    p.eq q = true ↔ Point.toAffine E2 p.toJ = Point.toAffine E2 q.toJ := by
  unfold eq
  by_cases hpz : p.toJ 2 = 0
  · rw [ite_eq_left ((Fp2.isZero_iff hp.2.2).mpr hpz), Point.toAffine_of_Z_eq_zero hpz]
    have := (isInf_iff_zero hq hnq)
    rw [isInf] at this
    rw [this, eq_comm]
  rw [ite_eq_right (fun h => hpz ((Fp2.isZero_iff hp.2.2).mp h))]
  by_cases hqz : q.toJ 2 = 0
  · rw [ite_eq_left ((Fp2.isZero_iff hq.2.2).mpr hqz), Point.toAffine_of_Z_eq_zero hqz,
      Point.toAffine_of_Z_ne_zero hnp hpz]
    simp only [Bool.false_eq_true, false_iff]
    exact Affine.Point.some_ne_zero _
  rw [ite_eq_right (fun h => hqz ((Fp2.isZero_iff hq.2.2).mp h))]
  obtain ⟨hpx, hpy, hpz1⟩ := hp
  obtain ⟨hqx, hqy, hqz1⟩ := hq
  have hpz' := hpz; have hqz' := hqz
  simp only [toJ_2] at hpz' hqz'
  rw [Bool.and_eq_true, Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul,
    Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul,
    Point.toAffine_of_Z_ne_zero hnp hpz, Point.toAffine_of_Z_ne_zero hnq hqz,
    Affine.Point.some.injEq]
  fp2_push
  simp only [toJ_0, toJ_1, toJ_2]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · field_simp; linear_combination h1
    · field_simp; linear_combination h2
  · rintro ⟨h1, h2⟩
    field_simp at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2

end G2J

namespace G2A

/-- `ψ` of a reduced affine point on `E'`, as the runtime computes it, is `ψ`. -/
theorem psi_spec {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    (G2J.ofAffine p).psi.Reduced ∧ E2.Nonsingular (G2J.ofAffine p).psi.toJ ∧
      Point.toAffine E2 (G2J.ofAffine p).psi.toJ = G2.psi (Point.toAffine E2 p.toJ) := by
  have hna : G2.A.Nonsingular p.x.toGF p.y.toGF := (nonsingular_some (W' := E2) _ _).mp hn
  have he : (G2J.ofAffine p).psi.toJ = ![G2.cx * star p.x.toGF, G2.cy * star p.y.toGF, 1] := by
    funext i
    fin_cases i
    · simp [G2J.psi, G2J.ofAffine, G2J.toJ, Fp2.toGF_mul (Fp2.reduced_conj hp.1)
        G2.psiX_reduced, Fp2.toGF_conj hp.1, mul_comm]
    · simp [G2J.psi, G2J.ofAffine, G2J.toJ, Fp2.toGF_mul (Fp2.reduced_conj hp.2)
        G2.psiY_reduced, Fp2.toGF_conj hp.2, mul_comm]
    · simp [G2J.psi, G2J.ofAffine, G2J.toJ, Fp2.toGF_conj Fp2.reduced_one]
  have hn' : E2.Nonsingular (G2J.ofAffine p).psi.toJ := by
    rw [he, nonsingular_some]; exact G2.nonsingular_psi hna
  refine ⟨⟨Fp2.reduced_mul, Fp2.reduced_mul, Fp2.reduced_conj Fp2.reduced_one⟩, hn', ?_⟩
  rw [show p.toJ = ![p.x.toGF, p.y.toGF, 1] from rfl, Point.toAffine_some hn]
  rw [he] at hn' ⊢
  rw [Point.toAffine_some hn']
  rfl

/-- What the runtime's test `inSubgroupPsi` checks: `ψ(P) = [x]P`, `x = −X`. -/
theorem inSubgroupPsi_iff {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.inSubgroupPsi = true ↔
      G2.psi (Point.toAffine E2 p.toJ) = -(X • Point.toAffine E2 p.toJ) := by
  obtain ⟨hsr, hsn, hsa⟩ := psi_spec hp hn
  obtain ⟨hmr, hmj⟩ := G2J.toJ_mulA hp X
  obtain ⟨hmn, hma⟩ := Jac.mulA_spec (⟨4, 4⟩ : GFp2) two_ne_zero_GFp2 hn X
  rw [← hmj] at hmn hma
  obtain ⟨hnr, hnn, hna⟩ := G2J.neg_spec hmr hmn
  unfold inSubgroupPsi
  rw [G2J.eq_iff hsr hnr hsn hnn, hsa, hna, hma]
  rfl

end G2A

namespace G2

/-- `ψ(G) = [x]G` on G2's generator: the runtime's `psi_acts`, by the kernel. -/
theorem psi_gen : psi (aff2 g2Gen.toJ) = -(X • aff2 g2Gen.toJ) :=
  (G2A.inSubgroupPsi_iff g2Gen_reduced g2Gen_nonsingular).mp psi_acts

/-- **Scott's test on G2 is complete**: every point `P` of `E'(𝔽_{p²})` with `[r]P = O` has
`ψ(P) = [x]P` (`x = −X`). The points with `[r]P = O` are the multiples of the generator, as
`#E'(𝔽_{p²}) = r·h₂` with `r ∤ h₂` (`card_E2`), and the generator passes (`psi_gen`). -/
theorem scott_complete (P : A.Point) (h : R • P = 0) : psi P = -(X • P) := by
  obtain ⟨k, rfl⟩ := E2_torsion_mem h
  rw [map_zsmul, psi_gen, zsmul_neg, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul,
    mul_comm]

/-- **Scott's test on G2**: on every point of `E'(𝔽_{p²})`, `[r]P = O` exactly when
`ψ(P) = [x]P` (`x = −X`). -/
theorem scott_iff (P : A.Point) : R • P = 0 ↔ psi P = -(X • P) :=
  ⟨scott_complete P, scott_sound P⟩

end G2

namespace G2A

/-- **The runtime's ψ test is G2's membership**: on a reduced point of `E'`, `inSubgroupPsi`
(`ψ(P) = [x]P` by the runtime's `psi`, `mulA`, `neg` and `eq`) is `inSubgroup` (`[r]P = O`).
What a runtime switching G2's subgroup check to `inSubgroupPsi` needs. -/
theorem inSubgroupPsi_eq {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.inSubgroupPsi = p.inSubgroup := by
  rw [Bool.eq_iff_iff, inSubgroupPsi_iff hp hn, inSubgroup_iff hp hn]
  exact (G2.scott_iff _).symm

end G2A

/-! ## G1 -/

namespace G1J

/-- The runtime's equality test on reduced nonsingular triples is equality of the points they
stand for (`eq_sound`, and its converse). -/
theorem eq_iff {p q : G1J} (hp : p.Reduced) (hq : q.Reduced) (hnp : E1.Nonsingular p.toJ)
    (hnq : E1.Nonsingular q.toJ) :
    p.eq q = true ↔ Point.toAffine E1 p.toJ = Point.toAffine E1 q.toJ := by
  refine ⟨eq_sound hp hq hnp hnq, fun h => ?_⟩
  unfold eq
  by_cases hpz : p.z = 0
  · have hpz' : p.toJ 2 = 0 := by simp [hpz]
    rw [ite_eq_left hpz, decide_eq_true_iff]
    rw [Point.toAffine_of_Z_eq_zero hpz'] at h
    by_contra hqz
    have hqz' : q.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hq.2.2]; exact hqz
    rw [Point.toAffine_of_Z_ne_zero hnq hqz'] at h
    exact Affine.Point.some_ne_zero _ h.symm
  rw [ite_eq_right hpz]
  have hpz' : p.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hp.2.2]; exact hpz
  by_cases hqz : q.z = 0
  · have hqz' : q.toJ 2 = 0 := by simp [hqz]
    rw [Point.toAffine_of_Z_eq_zero hqz', Point.toAffine_of_Z_ne_zero hnp hpz'] at h
    exact absurd h (Affine.Point.some_ne_zero _)
  rw [ite_eq_right hqz]
  have hqz' : q.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hq.2.2]; exact hqz
  rw [Point.toAffine_of_Z_ne_zero hnp hpz', Point.toAffine_of_Z_ne_zero hnq hqz',
    Affine.Point.some.injEq] at h
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    nat_eq_iff_cast fmul_lt fmul_lt, nat_eq_iff_cast fmul_lt fmul_lt]
  fp_push
  simp only [toJ_0, toJ_1, toJ_2] at hpz' hqz' h
  obtain ⟨h1, h2⟩ := h
  field_simp at h1 h2
  constructor
  · linear_combination h1
  · linear_combination h2

end G1J

namespace G1A

/-- What the runtime's test `inSubgroupScott` checks: `σ(P) = −[x²]P`. -/
theorem inSubgroupScott_iff {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    p.inSubgroupScott = true ↔
      Scott.sigma (aff1 p.toJ) = -((X * X) • aff1 p.toJ) := by
  have hna : Scott.A.Nonsingular (p.x : GFp) p.y := (nonsingular_some (W' := E1) _ _).mp hn
  have hP : Point.toAffine E1 p.toJ = .some (p.x : GFp) p.y hna := Point.toAffine_some hn
  have hsr : (p.sigma).Reduced := ⟨fmul_lt, hp.2, show (1 : ℕ) < P by decide⟩
  have hsj : (p.sigma).toJ = ![Scott.b * p.x, p.y, 1] := by
    funext i; fin_cases i <;> simp [G1A.sigma, G1J.toJ, cast_fmul]
  have hsn : E1.Nonsingular (p.sigma).toJ := by
    rw [hsj, nonsingular_some]; exact Scott.nonsingular_sigma hna
  have hs : Point.toAffine E1 (p.sigma).toJ = Scott.sigma (Point.toAffine E1 p.toJ) := by
    rw [hP]
    show _ = Affine.Point.some _ _ _
    rw [show (p.sigma).toJ = ![Scott.b * p.x, p.y, 1] from hsj]
    exact Point.toAffine_some (hsj ▸ hsn)
  obtain ⟨hmr, hmj⟩ := G1J.toJ_mulA hp (X * X)
  obtain ⟨hmn, hma⟩ := Jac.mulA_spec 4 two_ne_zero_GFp hn (X * X)
  rw [← hmj] at hmn hma
  obtain ⟨hnr, hnn, hna'⟩ := G1J.neg_spec hmr hmn
  unfold inSubgroupScott
  rw [G1J.eq_iff hsr hnr hsn hnn, hs, hna', hma]
  rfl

end G1A

namespace Scott

/-- `σ(G) = −[x²]G` on G1's generator: the runtime's `beta_acts`, by the kernel. -/
theorem sigma_gen : sigma (aff1 g1Gen.toJ) = -((X * X) • aff1 g1Gen.toJ) :=
  (G1A.inSubgroupScott_iff g1Gen_reduced g1Gen_nonsingular).mp beta_acts

/-- **Scott's test on G1 is complete**: every point `P` of `E(𝔽_p)` with `[r]P = O` has
`σ(P) = −[x²]P`. The points with `[r]P = O` are the multiples of the generator, as
`#E(𝔽_p) = r·h₁` with `r ∤ h₁` (`card_E1`), and the generator passes (`sigma_gen`). -/
theorem scott_complete (P : A.Point) (h : R • P = 0) : sigma P = -((X * X) • P) := by
  obtain ⟨k, rfl⟩ := E1_torsion_mem h
  change sigmaHom (k • _) = _
  rw [map_zsmul, show sigmaHom (aff1 g1Gen.toJ) = sigma (aff1 g1Gen.toJ) from rfl, sigma_gen,
    zsmul_neg, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, mul_comm]

/-- **Scott's test on G1**: a point `P = (x, y)` of `E(𝔽_p)` with `x ≠ 0` has `[r]P = O` exactly
when `σ(P) = −[x²]P`. -/
theorem scott_iff {x y : GFp} (h : A.Nonsingular x y) (hx : x ≠ 0) :
    R • (.some x y h : A.Point) = 0 ↔ sigma (.some x y h) = -((X * X) • (.some x y h : A.Point)) :=
  ⟨scott_complete _, scott_sound h hx⟩

end Scott

namespace G1A

/-- **The runtime's Scott test is G1's membership**: on a reduced point of `E` with `x ≠ 0`,
`inSubgroupScott` (`σ(P) = −[x²]P` by the runtime's `sigma`, `mulA`, `neg` and `eq`) is
`inSubgroup` (`[r]P = O`), so `inSubgroupFast` needs its fallback only at `x = 0`. -/
theorem inSubgroupScott_eq {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ)
    (hx : p.x ≠ 0) : p.inSubgroupScott = p.inSubgroup := by
  rw [Bool.eq_iff_iff, inSubgroupScott_iff hp hn, inSubgroup_iff hp hn]
  have hna : Scott.A.Nonsingular (p.x : GFp) p.y := (nonsingular_some (W' := E1) _ _).mp hn
  have hP : Point.toAffine E1 p.toJ = .some (p.x : GFp) p.y hna := Point.toAffine_some hn
  have hx' : (p.x : GFp) ≠ 0 := fun h0 => hx ((cast_eq_zero hp.1).mp h0)
  rw [hP]
  exact (Scott.scott_iff hna hx').symm

end G1A

end LeanLight.Lc.Bls
