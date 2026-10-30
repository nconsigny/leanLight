import LeanLightProofs.Bls.GrangerScott
import LeanLightProofs.Bls.Tower
import LeanLight.Bls.Pairing

/-!
# BLS12-381: the Frobenius, the conjugate and the cyclotomic squaring (25c)

What the runtime's final exponentiation is built from, as powers in `𝔽_{p¹²}`, on reduced values:

* `Fp12.toGF_frob`: the Frobenius `Fp12.frob` (its constants `frobV1`, `frobV2`, `frobW` are the
  powers of `ξ` they claim, by the kernel: `toGF_frobW` and the like) is `f ↦ f^p`;
* `Fp12.toGF_conj_pow`: the conjugate `Fp12.conj` is `f ↦ f^(p⁶)`;
* `toGF_cycSqr`: Granger–Scott's squaring `cycSqr` is the square on every `f` with
  `f^(p⁴ − p² + 1) = 1` (the cyclotomic subgroup) and on `0`.

The proofs are gattaca-com/silver's (`Spec/Cyclotomic/Tower.lean`, `Field.lean`,
`FieldBridge.lean`), ported: `𝔽_{p¹²}` maps injectively into `T = 𝔽_{p⁴}[w]/(w³ − y)`, with
`𝔽_{p⁴} = 𝔽_{p²}[y]/(y² − ξ)` (`toCubic`), where `f^(p²)` and `f^(p⁴)` have explicit coordinates
(`assemble_pow_q`, `assemble_pow_qq`) and an element of the cyclotomic subgroup satisfies
`f · f^(p⁴) = f^(p²)`, from which Granger–Scott's formula follows
(`Cyclotomic.granger_scott_of_frobenius_relation`). The one constant the argument needs,
`δ = ξ^((p²−1)/6)`, is computed by the kernel (`xi_sixth`), with `δ² − δ + 1 = 0`.
-/

namespace LeanLight.Lc.Bls

/-! ## Powers of `ξ`, computed by the kernel -/

namespace Fp2

/-- `a^(e mod 2ⁿ)`, square and multiply over the low `n` bits of `e`, top first: structural on
`n`, so the kernel can evaluate it on constants. Proof-only. -/
def powBits (a : Fp2) : ℕ → ℕ → Fp2
  | 0, _ => one
  | n + 1, e => if e % 2 = 1 then (powBits a n (e / 2)).sqr.mul a else (powBits a n (e / 2)).sqr

theorem powBits_spec {a : Fp2} (ha : a.Reduced) (n e : ℕ) :
    (powBits a n e).Reduced ∧ (powBits a n e).toGF = a.toGF ^ (e % 2 ^ n) := by
  induction n generalizing e with
  | zero => simp [powBits, reduced_one, Nat.mod_one]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (e / 2)
    have hm : e % 2 ^ (n + 1) = e % 2 + 2 * (e / 2 % 2 ^ n) := by
      rw [pow_succ, mul_comm, Nat.mod_mul]
    simp only [powBits]
    split
    · next he =>
      refine ⟨reduced_mul, ?_⟩
      rw [toGF_mul reduced_sqr ha, toGF_sqr h1, h2, hm, he, pow_add, pow_mul]; ring
    · next he =>
      have h0 : e % 2 = 0 := by omega
      refine ⟨reduced_sqr, ?_⟩
      rw [toGF_sqr h1, h2, hm, h0, zero_add, pow_mul]; ring

theorem toGF_powBits_xi {n e : ℕ} (he : e < 2 ^ n) :
    (powBits xi n e).toGF = (⟨1, 1⟩ : GFp2) ^ e := by
  rw [(powBits_spec reduced_xi n e).2, Nat.mod_eq_of_lt he, toGF_xi]

end Fp2

/-- `(p − 1)/6`, the exponent of the Frobenius constant of `w`. -/
abbrev frobK : ℕ := (P - 1) / 6

theorem toGF_frobW : frobW.toGF = (⟨1, 1⟩ : GFp2) ^ frobK := by
  rw [show frobW = Fp2.powBits xi 381 frobK by decide +kernel,
    Fp2.toGF_powBits_xi (by decide +kernel)]

theorem toGF_frobV1 : frobV1.toGF = (⟨1, 1⟩ : GFp2) ^ (2 * frobK) := by
  rw [show frobV1 = Fp2.powBits xi 381 (2 * frobK) by decide +kernel,
    Fp2.toGF_powBits_xi (by decide +kernel)]

theorem toGF_frobV2 : frobV2.toGF = (⟨1, 1⟩ : GFp2) ^ (4 * frobK) := by
  rw [show frobV2 = Fp2.powBits xi 381 (4 * frobK) by decide +kernel,
    Fp2.toGF_powBits_xi (by decide +kernel)]

theorem reduced_frobW : frobW.Reduced := ⟨by decide, by decide⟩
theorem reduced_frobV1 : frobV1.Reduced := ⟨by decide, by decide⟩
theorem reduced_frobV2 : frobV2.Reduced := ⟨by decide, by decide⟩

/-- `δ = ξ^((p²−1)/6)`, in `𝔽_p`. -/
def deltaWord : ℕ :=
  793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351

namespace Cyclotomic

open Schedule

/-- `δ`, in `𝔽_{p²}`. -/
noncomputable def delta : GFp2 := ⟨(deltaWord : GFp), 0⟩

/-- `p²`. -/
abbrev q : ℕ := P ^ 2

theorem xi_sixth : (⟨1, 1⟩ : GFp2) ^ ((q - 1) / 6) = delta := by
  rw [← Fp2.toGF_powBits_xi (n := 762) (by decide +kernel),
    show Fp2.powBits xi 762 ((q - 1) / 6) = ⟨deltaWord, 0⟩ by decide +kernel]
  ext <;> simp [Fp2.toGF, delta]

theorem xi_half : (⟨1, 1⟩ : GFp2) ^ ((q - 1) / 2) = -1 := by
  rw [← Fp2.toGF_powBits_xi (n := 762) (by decide +kernel),
    show Fp2.powBits xi 762 ((q - 1) / 2) = ⟨P - 1, 0⟩ by decide +kernel]
  have hm : (((P - 1 : ℕ)) : GFp) = -1 := by
    rw [Nat.cast_sub (by decide : 1 ≤ P), ZMod.natCast_self]; simp
  ext <;> simp [Fp2.toGF, hm]

theorem delta_polynomial : delta ^ 2 - delta + 1 = 0 := by
  have h : (deltaWord : GFp) ^ 2 - deltaWord + 1 = 0 := by decide +kernel
  have hm := congrArg (algebraMap GFp GFp2) h
  simpa [delta, map_add, map_sub, map_pow] using hm

/-! ## `𝔽_{p²}`'s Frobenius -/

/-- `ω² = −1` in `𝔽_{p²}`. -/
theorem omega_sq : (QuadraticAlgebra.omega : GFp2) ^ 2 = -1 := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem k_pow_q (a : GFp2) : a ^ q = a := by
  let _ := Fintype.ofFinite GFp2
  rw [show q = Fintype.card GFp2 by rw [← Nat.card_eq_fintype_card, card_GFp2]]
  exact FiniteField.pow_card a

theorem k_pow_p (a : GFp2) : a ^ P = star a := by
  have hi : (QuadraticAlgebra.omega : GFp2) ^ P = -QuadraticAlgebra.omega := by
    have hp : P = 4 * ((P - 3) / 4) + 3 := by decide +kernel
    have hi4 : (QuadraticAlgebra.omega : GFp2) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by rfl, pow_mul, omega_sq]; ring
    rw [congrArg ((QuadraticAlgebra.omega : GFp2) ^ ·) hp, pow_add, pow_mul, hi4, one_pow, one_mul,
      show 3 = 2 + 1 by rfl, pow_succ, omega_sq, neg_one_mul]
  let f : GFp →+* GFp2 := algebraMap _ _
  have ha : a = f a.re + f a.im * QuadraticAlgebra.omega := by ext <;> simp [f]
  conv_lhs => rw [ha]
  rw [add_pow_char, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card, hi]
  ext <;> simp [f]

/-! ## The model `T = 𝔽_{p⁴}[w]/(w³ − y)` -/

/-- `𝔽_{p⁴} = 𝔽_{p²}[y]/(y² − ξ)`. -/
abbrev S := QuadraticAlgebra GFp2 ⟨1, 1⟩ 0

/-- `y`, `y² = ξ`. -/
noncomputable abbrev u : S := QuadraticAlgebra.omega

/-- `𝔽_{p²}` inside `𝔽_{p⁴}`. -/
noncomputable abbrev j : GFp2 →+* S := algebraMap GFp2 S

/-- `𝔽_{p⁴}[w]/(w³ − y)`. -/
abbrev T := Cubic u

/-- `δ` in `𝔽_{p⁴}`. -/
noncomputable abbrev d : S := j delta

instance : Nontrivial S := ⟨⟨0, 1, fun h => zero_ne_one (congrArg QuadraticAlgebra.re h)⟩⟩

instance : CharP S P := charP_of_injective_algebraMap (algebraMap GFp2 S).injective P

instance : Nontrivial T := Function.Injective.nontrivial (embed_injective u)

instance : CharP T P := (CharP.charP_iff_prime_eq_zero (Fact.out : P.Prime)).2 (by
  rw [← map_natCast (embed u), CharP.cast_eq_zero S P, map_zero])

theorem u_square : u ^ 2 = j ⟨1, 1⟩ := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl

theorem u_pow_q : u ^ q = -u := by
  have hq : q = 2 * ((q - 1) / 2) + 1 := by decide +kernel
  rw [hq, pow_succ, pow_mul, u_square, ← map_pow, xi_half, map_neg, map_one, neg_one_mul]

theorem s_pow_q (a : S) : a ^ q = star a := by
  have ha : a = j a.re + j a.im * u := by ext <;> simp
  conv_lhs => rw [ha]
  rw [add_pow_char_pow, mul_pow, ← map_pow, ← map_pow, k_pow_q, k_pow_q, u_pow_q]
  rcases a with ⟨a, b⟩
  ext <;> simp [QuadraticAlgebra.star_mk]

theorem d_polynomial : d ^ 2 - d + 1 = 0 := by
  rw [← map_pow, ← map_sub, ← map_one j, ← map_add, delta_polynomial, map_zero]

theorem w_sixth : w u ^ 6 = embed u (j ⟨1, 1⟩) := by
  rw [show 6 = 3 * 2 by rfl, pow_mul, w_cube, ← map_pow, u_square]

theorem w_pow_q : w u ^ q = embed u d * w u := by
  have hq : q = 6 * ((q - 1) / 6) + 1 := by decide +kernel
  rw [root_power (w u) (embed u (j ⟨1, 1⟩)) q ((q - 1) / 6) hq w_sixth,
    ← map_pow, ← map_pow, xi_sixth]

theorem assemble_pow_q (a b c : S) :
    assemble u a b c ^ q = assemble u (star a) (d * star b) (d ^ 2 * star c) := by
  have h2 : (w u ^ 2) ^ q = (embed u d * w u) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm 2 q, pow_mul, w_pow_q]
  simp only [assemble, add_pow_char_pow, mul_pow, h2, ← map_pow, s_pow_q, w_pow_q]
  simp only [map_mul, map_pow]
  ring

theorem star_d : star d = d := by
  ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im]

theorem assemble_pow_qq (a b c : S) :
    assemble u a b c ^ (q ^ 2) = assemble u a (d ^ 2 * b) (d ^ 4 * c) := by
  rw [sq, pow_mul, assemble_pow_q, assemble_pow_q]
  simp only [star_mul, star_pow, star_star, star_d]
  congr 1 <;> ring

/-- Granger–Scott in `T`: on the cyclotomic subgroup, the square has the formula's
coordinates. -/
theorem cyclotomic_square (a b c : S)
    (hphi : assemble u a b c ^ (P ^ 4 - P ^ 2 + 1) = 1) :
    assemble u a b c ^ 2 =
      assemble u (3 * a ^ 2 - 2 * star a) (3 * u * c ^ 2 + 2 * star b)
        (3 * b ^ 2 - 2 * star c) := by
  apply granger_scott_of_frobenius_relation u a b c (star a) (star b) (star c) d d_polynomial
  rw [← assemble_pow_qq]
  have hp : q ^ 2 = P ^ 4 := by simp only [q, ← pow_mul]
  rw [hp]
  have hrel := cyclotomic_relation (assemble u a b c) (P ^ 2) (by decide +kernel)
  rw [← pow_mul, show 2 * 2 = 4 by rfl] at hrel
  rw [hrel hphi, assemble_pow_q]

/-- `𝔽_{p²}` inside `T`. -/
noncomputable abbrev kembed : GFp2 →+* T := (embed u).comp j

/-- `Σ aᵢ wⁱ`. -/
noncomputable def sextic (a : Fin 6 → GFp2) : T := ∑ i : Fin 6, kembed (a i) * w u ^ i.val

theorem p_power_coefficients (a : Fin 6 → GFp2) :
    sextic a ^ P = sextic (fun i => star (a i) * (⟨1, 1⟩ : GFp2) ^ (i.val * frobK)) := by
  have hp : P ^ 1 = 6 * frobK + 1 := by decide +kernel
  have h := coefficient_frobenius P 1 (w u) (kembed ⟨1, 1⟩)
    (fun i => kembed (a i)) frobK hp w_sixth
  simp only [pow_one] at h
  change (∑ i : Fin 6, kembed (a i) * w u ^ i.val) ^ P = _
  rw [h]
  unfold sextic
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_pow, k_pow_p, ← map_pow, ← map_mul]

theorem d_cube : d ^ 3 = -1 := by
  linear_combination (d + 1) * d_polynomial

theorem d_sixth : d ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by rfl, pow_mul, d_cube]
  ring

theorem assemble_pow_p6 (a b c : S) :
    assemble u a b c ^ (P ^ 6) = assemble u (star a) (-star b) (star c) := by
  have hexp : P ^ 6 = q ^ 2 * q := by simp only [q]; ring
  rw [hexp, pow_mul, assemble_pow_qq, assemble_pow_q]
  simp only [star_mul, star_pow, star_d]
  congr 1
  · calc
      d * (star b * d ^ 2) = d ^ 3 * star b := by ring
      _ = -star b := by rw [d_cube, neg_one_mul]
  · calc
      d ^ 2 * (star c * d ^ 4) = d ^ 6 * star c := by ring
      _ = star c := by rw [d_sixth, one_mul]

/-! ## `𝔽_{p¹²}` inside `T` -/

/-- `𝔽_{p⁶} → T`, `v ↦ w²`. -/
noncomputable def fp6ToCubic : GFp6 →+* T :=
  AdjoinRoot.lift (f := fp6Poly) kembed (w u ^ 2) (by
    simp only [fp6Poly, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [← pow_mul, show 2 * 3 = 6 by rfl, w_sixth]
    exact sub_self _)

@[simp] theorem fp6ToCubic_of (a : GFp2) : fp6ToCubic (of6 a) = kembed a :=
  AdjoinRoot.lift_of _

@[simp] theorem fp6ToCubic_v : fp6ToCubic vGF = w u ^ 2 :=
  AdjoinRoot.lift_root _

/-- `𝔽_{p¹²} → T`, `w ↦ w`. -/
noncomputable def toCubic : GFp12 →+* T :=
  letI : Algebra GFp6 T := fp6ToCubic.toAlgebra
  (QuadraticAlgebra.lift (R := GFp6) (a := vGF) (b := 0) (A := T)
    ⟨w u, by
      change w u * w u = fp6ToCubic vGF * 1 + fp6ToCubic 0 * w u
      rw [fp6ToCubic_v, map_zero, zero_mul, add_zero, mul_one, pow_two]⟩).toRingHom

@[simp] theorem toCubic_mk (a b : GFp6) :
    toCubic ⟨a, b⟩ = fp6ToCubic a + fp6ToCubic b * w u := by
  change fp6ToCubic a * 1 + fp6ToCubic b * w u = _
  rw [mul_one]

theorem embed_mk (a b : GFp2) : embed u (⟨a, b⟩ : S) = kembed a + kembed b * w u ^ 3 := by
  rw [w_cube]
  change embed u (⟨a, b⟩ : S) = embed u (j a) + embed u (j b) * embed u u
  rw [← map_mul, ← map_add]
  congr 1
  ext <;> simp

/-- The six coordinates of a runtime `Fp12`, in `𝔽_{p²}`. -/
noncomputable def coeffs (x : Fp12) : Coeffs GFp2 :=
  ⟨x.c0.c0.toGF, x.c0.c1.toGF, x.c0.c2.toGF, x.c1.c0.toGF, x.c1.c1.toGF, x.c1.c2.toGF⟩

theorem toCubic_toGF (x : Fp12) : toCubic x.toGF = decode ⟨1, 1⟩ (coeffs x) := by
  simp only [Fp12.toGF, Fp6.toGF, toCubic_mk, map_add, map_mul, map_pow, fp6ToCubic_of,
    fp6ToCubic_v, decode, assemble, ca, cb, cc, embed_mk, coeffs]
  ring

theorem decode_eq_sextic (x : Coeffs GFp2) : decode ⟨1, 1⟩ x = sextic (powers x) := by
  simp only [decode, assemble, ca, cb, cc, embed_mk, sextic, powers, Fin.sum_univ_succ]
  norm_num [kembed, RingHom.comp_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-! ## The runtime's operations -/

theorem _root_.LeanLight.Lc.Bls.Fp6.reduced_frob {a : Fp6} (ha : a.Reduced) : a.frob.Reduced :=
  ⟨Fp2.reduced_conj ha.1, Fp2.reduced_mul, Fp2.reduced_mul⟩

theorem _root_.LeanLight.Lc.Bls.Fp12.reduced_frob {a : Fp12} (ha : a.Reduced) : a.frob.Reduced :=
  ⟨Fp6.reduced_frob ha.1, Fp6.reduced_mulFp2 _⟩

/-- **The Frobenius**: on a reduced value, `Fp12.frob` is `f ↦ f^p` in `𝔽_{p¹²}`. -/
theorem _root_.LeanLight.Lc.Bls.Fp12.toGF_frob {a : Fp12} (ha : a.Reduced) :
    a.frob.toGF = a.toGF ^ P := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩⟩ := ha
  apply toCubic.injective
  rw [map_pow, toCubic_toGF, toCubic_toGF, decode_eq_sextic, decode_eq_sextic,
    p_power_coefficients]
  congr 1
  funext i
  have := reduced_frobW; have := reduced_frobV1; have := reduced_frobV2
  simp (disch := fp2_reduced) only [powers, coeffs, Fp12.frob, Fp6.frob, Fp6.mulFp2,
    Fp2.toGF_mul, Fp2.toGF_conj, toGF_frobW, toGF_frobV1, toGF_frobV2]
  fin_cases i <;> simp <;> ring

/-- **The conjugate**: on a reduced value, `Fp12.conj` is `f ↦ f^(p⁶)` in `𝔽_{p¹²}`. -/
theorem _root_.LeanLight.Lc.Bls.Fp12.toGF_conj_pow {a : Fp12} (ha : a.Reduced) :
    a.conj.toGF = a.toGF ^ (P ^ 6) := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩⟩ := ha
  apply toCubic.injective
  rw [map_pow, toCubic_toGF, toCubic_toGF]
  simp only [decode]
  rw [assemble_pow_p6]
  congr 1 <;> ext <;>
    simp [ca, cb, cc, coeffs, Fp12.conj, Fp6.neg, Fp2.toGF_neg h10, Fp2.toGF_neg h11,
      Fp2.toGF_neg h12, QuadraticAlgebra.star_mk]

/-- The runtime's cyclotomic squaring is Granger–Scott's schedule on the coordinates. -/
theorem coeffs_cycSqr {a : Fp12} (ha : a.Reduced) :
    coeffs (cycSqr a) = raw ⟨1, 1⟩ (coeffs a) := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩⟩ := ha
  simp only [cycSqr, fp4Sqr, coeffs, raw, fp4Square, less, plus]
  congr 1 <;> fp2_push <;> ring

theorem reduced_cycSqr {a : Fp12} (ha : a.Reduced) : (cycSqr a).Reduced := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩⟩ := ha
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> simp only [cycSqr, fp4Sqr] <;> fp2_reduced

/-- **The cyclotomic squaring**: on a reduced value `f` with `f^(p⁴ − p² + 1) = 1` (the
cyclotomic subgroup) or `f = 0`, `cycSqr f` is `f²` in `𝔽_{p¹²}`. -/
theorem toGF_cycSqr {a : Fp12} (ha : a.Reduced)
    (hphi : a.toGF = 0 ∨ a.toGF ^ (P ^ 4 - P ^ 2 + 1) = 1) :
    (cycSqr a).toGF = a.toGF ^ 2 := by
  apply toCubic.injective
  rw [map_pow, toCubic_toGF, toCubic_toGF, coeffs_cycSqr ha, raw_decode]
  rcases hphi with h0 | h1
  · have h := toCubic_toGF a
    rw [h0, map_zero] at h
    have hz : (0 : T) = assemble u 0 0 0 := by simp [assemble]
    rw [hz] at h
    obtain ⟨ha', hb', hc'⟩ := assemble_injective u _ _ _ _ _ _ h
    simp only [decode] at ⊢
    rw [← ha', ← hb', ← hc']
    simp [assemble]
  · exact (cyclotomic_square _ _ _ (by
      simpa only [map_pow, map_one, toCubic_toGF, decode] using congrArg toCubic h1)).symm

end Cyclotomic

end LeanLight.Lc.Bls
