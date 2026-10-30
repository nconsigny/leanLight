import LeanLightProofs.Bls.Hasse
import LeanLightProofs.Bls.Scott
import LeanLightProofs.Bls.Primes

/-!
# BLS12-381: the orders of `E(𝔽_p)` and `E'(𝔽_{p²})` (25c)

Hasse's bound (`LeanLightProofs.Bls.Hasse`, after gattaca-com/silver's `Spec/CubicHasse.lean`)
and two points of known prime order fix both groups' orders exactly:

* `card_E1`: `E(𝔽_p)` has `r · h₁` points, `h₁ = (x − 1)²/3` (`H1`, `H1_def`). Hasse's bound
  puts the count within `2√p` of `p + 1`, the generator's order `r` divides it, and only one
  multiple of `r` lies there (`r > 4√p`).
* `card_E2`: `E'(𝔽_{p²})` has `r · h₂` points, `h₂` G2's cofactor (`H2`, `H2_def`), with
  `h_eff = 3(x² − 1) · h₂` (`hEff_eq`). Hasse puts the count within `2p` of `p² + 1`
  (`card_E2_bounds`: between `(p − 1)²` and `(p + 1)²`); the generator's order `r` and the
  order of a second point `Q_ℓ` (`g2L`), the prime `ℓ` (`L2`, `L2_prime`) of `h₂ = ℓ · m`, divide
  it, and `r · ℓ > 4p` leaves one multiple in the window. `[ℓ]Q_ℓ = O` is the kernel running
  `G2J.mulA`; `ℓ`'s primality a Lucas certificate tree.

From them (`torsion_mem_zmultiples`): as `r²` divides neither order (`r ∤ h₁`, `r ∤ h₂`), every
point with `[r]P = O` is a multiple of the generator, in both groups, and
(`hEff_smul_mem_G2`) `[r][h_eff]` kills every point of `E'(𝔽_{p²})`: what `[h_eff]` returns
is in G2.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

/-! ## The fields -/

noncomputable instance : Fintype GFp2 := Fintype.ofFinite _

theorem fintype_card_GFp : Fintype.card GFp = P := ZMod.card P

theorem fintype_card_GFp2 : Fintype.card GFp2 = P ^ 2 := by
  rw [← Nat.card_eq_fintype_card, card_GFp2]

theorem ringChar_GFp : ringChar GFp ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_GFp2 : ringChar GFp2 ≠ 2 := by
  rw [ringChar.eq GFp2 P]; decide

/-! ## The curves' points -/

theorem E1_affine_nonsingular_iff (x y : GFp) : E1.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 4 :=
  (nonsingular_some (W' := E1) x y).symm.trans E1_nonsingular_iff

theorem E2_affine_nonsingular_iff (x y : GFp2) :
    E2.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + ⟨4, 4⟩ :=
  (nonsingular_some (W' := E2) x y).symm.trans E2_nonsingular_iff

instance : Finite E1.toAffine.Point := Hasse.finite_point _
instance : Finite E2.toAffine.Point := Hasse.finite_point _

/-- **Hasse's bound for `E(𝔽_p)`**: `(#E(𝔽_p) − (p + 1))² ≤ 4p`. -/
theorem card_E1_hasse :
    ((Nat.card E1.toAffine.Point : ℤ) - (P + 1)) ^ 2 ≤ 4 * P := by
  have h := Hasse.card_sub_sq_le ringChar_GFp (by rw [fintype_card_GFp]; decide) E1.toAffine
    (b := (4 : GFp)) (by
      rw [show (4 : GFp) = ((4 : ℕ) : GFp) by norm_num, Ne, cast_eq_zero (by decide)]
      decide) E1_affine_nonsingular_iff
  rwa [fintype_card_GFp] at h

/-- **Hasse's bound for `E'(𝔽_{p²})`**: `(#E'(𝔽_{p²}) − (p² + 1))² ≤ 4p²`. -/
theorem card_E2_hasse :
    ((Nat.card E2.toAffine.Point : ℤ) - (P ^ 2 + 1)) ^ 2 ≤ 4 * P ^ 2 := by
  have h := Hasse.card_sub_sq_le ringChar_GFp2 (by rw [fintype_card_GFp2]; decide +kernel)
    E2.toAffine (b := (⟨4, 4⟩ : GFp2)) (by
      intro h
      have := congrArg QuadraticAlgebra.re h
      simp only [QuadraticAlgebra.re_zero] at this
      rw [show (4 : GFp) = ((4 : ℕ) : GFp) by norm_num, cast_eq_zero (by decide)] at this
      exact absurd this (by decide)) E2_affine_nonsingular_iff
  rw [fintype_card_GFp2] at h
  exact_mod_cast h

/-- Hasse's bound for `E'(𝔽_{p²})` as an interval: `(p − 1)² ≤ #E'(𝔽_{p²}) ≤ (p + 1)²`
(silver's `E'.hasse_bounds`). -/
theorem card_E2_bounds :
    (P - 1) ^ 2 ≤ Nat.card E2.toAffine.Point ∧ Nat.card E2.toAffine.Point ≤ (P + 1) ^ 2 := by
  have h := card_E2_hasse
  have hP : (1 : ℤ) ≤ P := by exact_mod_cast (show 1 ≤ P by decide)
  have hab := abs_le_of_sq_le_sq' (show ((Nat.card E2.toAffine.Point : ℤ) - (P ^ 2 + 1)) ^ 2 ≤
    (2 * (P : ℤ)) ^ 2 by nlinarith) (by positivity)
  constructor
  · have : (((P - 1 : ℕ) : ℤ)) ^ 2 ≤ Nat.card E2.toAffine.Point := by
      rw [Nat.cast_sub (by decide), Nat.cast_one]; nlinarith [hab.1]
    exact_mod_cast this
  · have : (Nat.card E2.toAffine.Point : ℤ) ≤ ((P + 1 : ℕ) : ℤ) ^ 2 := by
      push_cast; nlinarith [hab.2]
    exact_mod_cast this

/-! ## One multiple in the window -/

/-- If `d ∣ n`, `(n − c)² ≤ B`, and the multiples `d(k₀ − 1)` and `d(k₀ + 1)` lie on either
side of `c` farther than `√B` from it, then `n = d · k₀`. -/
theorem eq_of_window {n d k0 : ℕ} {c B : ℤ} (hd : d ∣ n) (hn : ((n : ℤ) - c) ^ 2 ≤ B)
    (hlo : (d : ℤ) * ((k0 : ℤ) - 1) < c ∧ B < (c - d * ((k0 : ℤ) - 1)) ^ 2)
    (hhi : c < (d : ℤ) * ((k0 : ℤ) + 1) ∧ B < ((d : ℤ) * ((k0 : ℤ) + 1) - c) ^ 2) :
    n = d * k0 := by
  obtain ⟨k, rfl⟩ := hd
  rcases lt_trichotomy k k0 with h | h | h
  · exfalso
    have hk : (k : ℤ) ≤ (k0 : ℤ) - 1 := by omega
    have hdk : (d : ℤ) * k ≤ d * ((k0 : ℤ) - 1) := mul_le_mul_of_nonneg_left hk (by positivity)
    have hv : 0 < c - d * ((k0 : ℤ) - 1) := by linarith [hlo.1]
    have hsq := pow_le_pow_left₀ hv.le (show c - d * ((k0 : ℤ) - 1) ≤ c - d * k by linarith) 2
    push_cast at hn
    nlinarith [hlo.2]
  · rw [h]
  · exfalso
    have hk : (k0 : ℤ) + 1 ≤ k := by omega
    have hdk : (d : ℤ) * ((k0 : ℤ) + 1) ≤ d * k := mul_le_mul_of_nonneg_left hk (by positivity)
    have hv : 0 < (d : ℤ) * ((k0 : ℤ) + 1) - c := by linarith [hhi.1]
    have hsq := pow_le_pow_left₀ hv.le (show (d : ℤ) * ((k0 : ℤ) + 1) - c ≤ d * k - c by linarith) 2
    push_cast at hn
    nlinarith [hhi.2]

/-! ## `E(𝔽_p)` -/

/-- G1's cofactor `h₁ = (x − 1)²/3`. -/
def H1 : ℕ := 0x396c8c005555e1568c00aaab0000aaab

theorem H1_def : 3 * H1 = (X + 1) ^ 2 := by decide

/-- **`E(𝔽_p)` has `r · h₁` points.** -/
theorem card_E1 : Nat.card E1.toAffine.Point = R * H1 := by
  have hd : R ∣ Nat.card E1.toAffine.Point := by
    rw [← g1Gen_order]; exact addOrderOf_dvd_natCard _
  exact eq_of_window hd card_E1_hasse
    ⟨by norm_num [R, H1, P], by norm_num [R, H1, P]⟩ ⟨by norm_num [R, H1, P], by norm_num [R, H1, P]⟩

/-! ## `E'(𝔽_{p²})` -/

/-- G2's cofactor `h₂`, `#E'(𝔽_{p²})/r`. -/
def H2 : ℕ :=
  0x5d543a95414e7f1091d50792876a202cd91de4547085abaa68a205b2e5a7ddfa628f1cb4d9e82ef21537e293a6691ae1616ec6e786f0c70cf1c38e31c7238e5

/-- `h₂ = (x⁸ − 4x⁷ + 5x⁶ − 4x⁴ + 6x³ − 4x² − 4x + 13)/9`, for `x = −X`. -/
theorem H2_def :
    let x : Int := -(X : Int)
    9 * (H2 : Int) = x ^ 8 - 4 * x ^ 7 + 5 * x ^ 6 - 4 * x ^ 4 + 6 * x ^ 3 - 4 * x ^ 2 - 4 * x + 13 := by
  decide +kernel

/-- `h_eff = 3(x² − 1) · h₂`. -/
theorem hEff_eq : hEff = 3 * (X * X - 1) * H2 := by decide +kernel

/-- `ℓ`, the largest prime factor of `h₂`, 447 bits. -/
def L2 : ℕ :=
  402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

/-- `m = h₂/ℓ`. -/
def M2 : ℕ := 759774549028129141

theorem H2_eq : H2 = L2 * M2 := by decide +kernel

/-! ### `ℓ` is prime (a Lucas certificate tree) -/

private theorem prime_1402724681 : Nat.Prime 1402724681 :=
  prime_of_lucas _ 3 [(2, 3), (5, 1), (7, 1), (1307, 1), (3833, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | norm_num))

private theorem prime_16297965815447 : Nat.Prime 16297965815447 :=
  prime_of_lucas _ 5 [(2, 1), (7, 3), (68059, 1), (349079, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | norm_num))

private theorem prime_810774871 : Nat.Prime 810774871 :=
  prime_of_lucas _ 11 [(2, 1), (3, 1), (5, 1), (89, 1), (151, 1), (2011, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | norm_num))

private theorem prime_63240439939 : Nat.Prime 63240439939 :=
  prime_of_lucas _ 3 [(2, 1), (3, 1), (13, 1), (810774871, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_810774871 | norm_num))

private theorem prime_1770732318293 : Nat.Prime 1770732318293 :=
  prime_of_lucas _ 2 [(2, 2), (7, 1), (63240439939, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_63240439939 | norm_num))

private theorem prime_21561538103037546247 : Nat.Prime 21561538103037546247 :=
  prime_of_lucas _ 5 [(2, 1), (3, 3), (225493, 1), (1770732318293, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_1770732318293 | norm_num))

private theorem prime_86246152412150184989 : Nat.Prime 86246152412150184989 :=
  prime_of_lucas _ 2 [(2, 2), (21561538103037546247, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_21561538103037546247 | norm_num))

private theorem prime_1435735831703 : Nat.Prime 1435735831703 :=
  prime_of_lucas _ 5 [(2, 1), (2969, 1), (241787779, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | norm_num))

private theorem prime_12192593745179 : Nat.Prime 12192593745179 :=
  prime_of_lucas _ 2 [(2, 1), (7, 1), (11, 1), (107, 1), (541, 1), (1367711, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | norm_num))

private theorem prime_512088937297519 : Nat.Prime 512088937297519 :=
  prime_of_lucas _ 6 [(2, 1), (3, 1), (7, 1), (12192593745179, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_12192593745179 | norm_num))

private theorem prime_1857858664515398933 : Nat.Prime 1857858664515398933 :=
  prime_of_lucas _ 2 [(2, 2), (907, 1), (512088937297519, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_512088937297519 | norm_num))

private theorem prime_22294303974184787197 : Nat.Prime 22294303974184787197 :=
  prime_of_lucas _ 14 [(2, 2), (3, 1), (1857858664515398933, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_1857858664515398933 | norm_num))

private theorem prime_19931107752921199754119 : Nat.Prime 19931107752921199754119 :=
  prime_of_lucas _ 3 [(2, 1), (3, 1), (149, 1), (22294303974184787197, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_22294303974184787197 | norm_num))

private theorem prime_81162125843606155545104998607900118769099783 : Nat.Prime 81162125843606155545104998607900118769099783 :=
  prime_of_lucas _ 5 [(2, 1), (3, 2), (2731, 1), (57697, 1), (1435735831703, 1), (19931107752921199754119, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_1435735831703 | exact prime_19931107752921199754119 | norm_num))

private theorem prime_26935696298915610574513298451669528361624243820491956655650666425177 : Nat.Prime 26935696298915610574513298451669528361624243820491956655650666425177 :=
  prime_of_lucas _ 3 [(2, 3), (13, 1), (37, 1), (86246152412150184989, 1), (81162125843606155545104998607900118769099783, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_86246152412150184989 | exact prime_81162125843606155545104998607900118769099783 | norm_num))

private theorem prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 : Nat.Prime 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :=
  prime_of_lucas _ 3 [(2, 3), (373, 1), (8329, 1), (37501, 1), (661873, 1), (12211063, 1), (1402724681, 1), (16297965815447, 1), (26935696298915610574513298451669528361624243820491956655650666425177, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_1402724681 | exact prime_16297965815447 | exact prime_26935696298915610574513298451669528361624243820491956655650666425177 | norm_num))

/-- `ℓ` is prime. -/
theorem L2_prime : Nat.Prime L2 :=
  prime_of_lucas _ 13 [(2, 4), (3, 1), (11, 1), (631, 1), (4920833, 1), (52872661, 1), (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> (first | exact prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 | norm_num))
instance fact_L2_prime : Fact (Nat.Prime L2) := ⟨L2_prime⟩

/-! ### A point of order `ℓ` -/

/-- A point of `E'(𝔽_{p²})` of order `ℓ`: `[h₂/ℓ]` of the point with `x = 2`. -/
def g2L : G2A :=
  ⟨⟨0x742c321cfc416938d661ca92e2049e95cbff82f7f224a70ce7f110897519a5d9b04add2c76fff66fbd66bccb00621ac,
    0x3e2e4ca4a68ca97402f2aa09d95197cfc96d6aa1f2b915414c9b44a9440d9a06b6a83f86f01c2e3b1786800eb86c22d⟩,
   ⟨0x7cf38919ab943d5a06d150da63b33d36d4f74f5845a4d4cbc744966e24e1e7a0f510338f484c02b7e3b1a8bbb1a3102,
    0xf3a9c32939b1c049b65f634fdac4efe8ceab9d9a758fc1d53eb78af860513bf0fb9a200edcd0f043cdf355cc142fa01⟩⟩

theorem g2L_reduced : g2L.Reduced := ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem g2L_onCurve : g2L.onCurve = true := by decide +kernel

theorem g2L_nonsingular : E2.Nonsingular g2L.toJ := (G2A.onCurve_iff g2L_reduced).mp g2L_onCurve

/-- `[ℓ]Q_ℓ = O`, by the kernel running `G2J.mulA`. -/
theorem g2L_mul : (G2J.mulA g2L L2).isInf = true := by decide +kernel

/-- `Q_ℓ` has order `ℓ`. -/
theorem g2L_order : addOrderOf (Point.toAffine E2 g2L.toJ) = L2 := by
  apply addOrderOf_eq_prime
  · obtain ⟨hr, hn, ha⟩ := G2J.mulA_spec g2L_reduced g2L_nonsingular L2
    rw [← ha]
    exact (G2J.isInf_iff_zero hr hn).mp g2L_mul
  · rw [show g2L.toJ = ![g2L.x.toGF, g2L.y.toGF, 1] from rfl,
      Point.toAffine_some g2L_nonsingular]
    exact Affine.Point.some_ne_zero _

/-- **`E'(𝔽_{p²})` has `r · h₂` points.** -/
theorem card_E2 : Nat.card E2.toAffine.Point = R * H2 := by
  have hr : R ∣ Nat.card E2.toAffine.Point := by
    rw [← g2Gen_order]; exact addOrderOf_dvd_natCard _
  have hl : L2 ∣ Nat.card E2.toAffine.Point := by
    rw [← g2L_order]; exact addOrderOf_dvd_natCard _
  have hd : R * L2 ∣ Nat.card E2.toAffine.Point :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide +kernel) hr hl
  rw [H2_eq, ← mul_assoc]
  refine eq_of_window hd card_E2_hasse ⟨?_, ?_⟩ ⟨?_, ?_⟩ <;>
    norm_num [R, L2, M2, P]

/-! ## The `r`-torsion -/

/-- In a finite group of `r · h` elements, `r` prime, `r ∤ h`, a point `G` of order `r`
generates every point `P` with `[r]P = O`. (silver's `torsion_eq_zsmul_generator_of_card`.) -/
theorem torsion_mem_zmultiples {A : Type*} [AddCommGroup A] [Finite A] {r h : ℕ}
    (hr : r.Prime) (hcard : Nat.card A = r * h) (hh : ¬ r ∣ h) {G : A}
    (hG : addOrderOf G = r) {Q : A} (hQ : r • Q = 0) : ∃ k : ℤ, Q = k • G := by
  let H := AddSubgroup.zmultiples G
  have hH : Nat.card H = r := by rw [Nat.card_zmultiples, hG]
  have hi : H.index = h := by
    apply Nat.eq_of_mul_eq_mul_left hr.pos
    rw [← hcard, ← hH, H.card_mul_index]
  have hc : (Nat.card (A ⧸ H)).Coprime r := by
    rw [← H.index_eq_card, hi]
    exact (hr.coprime_iff_not_dvd.mpr hh).symm
  have hq : (QuotientAddGroup.mk' H) Q = 0 := by
    apply hc.nsmul_right_bijective.injective
    dsimp only
    rw [← map_nsmul, hQ, map_zero, smul_zero]
  have hm : Q ∈ H := (QuotientAddGroup.eq_zero_iff Q).mp hq
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  exact ⟨k, hk.symm⟩

/-- Every point of `E(𝔽_p)` with `[r]P = O` is a multiple of G1's generator. -/
theorem E1_torsion_mem {Q : E1.toAffine.Point} (hQ : R • Q = 0) :
    ∃ k : ℤ, Q = k • Point.toAffine E1 g1Gen.toJ :=
  torsion_mem_zmultiples R_prime card_E1 (by decide +kernel) g1Gen_order hQ

/-- Every point of `E'(𝔽_{p²})` with `[r]P = O` is a multiple of G2's generator. -/
theorem E2_torsion_mem {Q : E2.toAffine.Point} (hQ : R • Q = 0) :
    ∃ k : ℤ, Q = k • Point.toAffine E2 g2Gen.toJ :=
  torsion_mem_zmultiples R_prime card_E2 (by decide +kernel) g2Gen_order hQ

/-- **`[h_eff]` maps `E'(𝔽_{p²})` into G2**: `[r][h_eff]P = O` for every point `P`, since
`r · h_eff = 3(x² − 1) · #E'(𝔽_{p²})`. -/
theorem hEff_smul_mem_G2 (Q : E2.toAffine.Point) : R • (hEff • Q) = 0 := by
  rw [smul_smul, hEff_eq, show R * (3 * (X * X - 1) * H2) = 3 * (X * X - 1) * (R * H2) by ring,
    ← card_E2, mul_smul, card_nsmul_eq_zero', smul_zero]

end LeanLight.Lc.Bls
