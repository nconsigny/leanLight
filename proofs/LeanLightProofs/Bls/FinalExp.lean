import LeanLightProofs.Bls.Tower
import LeanLight.Bls.Pairing
import LeanLightProofs.Vendor.EthLib.Bls.Pairing

/-!
# BLS12-381: the cube lemma (25c)

The runtime's final exponentiation (`LeanLight.Bls.finalExp`, zkcrypto's chain) computes the
**cube** of the final exponentiation, where EthLib's readable `finalExponentiation` computes
`f^((p¹²−1)/r)` itself (`ethFinalExp_eq_pow`, through `toGF_ofEth12_powNat`). A check that the
result is one loses nothing by the cube:

* `cube_lemma`: in `𝔽_{p¹²}`, for every `f`, `(f^((p¹²−1)/r))³ = 1 ↔ f^((p¹²−1)/r) = 1`. For
  `f ≠ 0`, `g = f^((p¹²−1)/r)` has `g^r = f^(p¹²−1) = 1` (Fermat in `𝔽_{p¹²}`,
  `pow_card_sub_one_GFp12`, and `r ∣ p¹² − 1`, `R_dvd`), so `g³ = 1` gives
  `g = g^gcd(3, r) = 1` (`R_coprime_three`); for `f = 0` both sides are false.
* `finalExp_isOne_iff`: if the runtime's `finalExp m` stands for the cube of EthLib's
  `finalExponentiation acc` (`FinalExpCube`), then the runtime's check `(finalExp m).isOne` is
  EthLib's `(finalExponentiation acc).isOne`. `FinalExpCube` was H_vec's hypothesis; the runtime's
  final exponentiation is now proved (`LeanLightProofs.Bls.FinalExpPow.finalExp_toGF`), so for a
  reduced `m` it holds exactly when `m` and `acc` agree after the final exponentiation
  (`finalExpCube_iff`), a statement about the Miller loops alone.

What it rests on: `p` and `r` prime (`LeanLightProofs.Bls.Primes`), `𝔽_{p¹²}` a field of `p¹²`
elements (`LeanLightProofs.Bls.Tower`).
-/

namespace LeanLight.Lc.Bls

open EthLib.Cryptography.Bls (finalExponentiation finalExpExponent)

/-- `(p¹² − 1)/r`, the final exponentiation's exponent. -/
abbrev finalExpExp : ℕ := (P ^ 12 - 1) / R

/-- The embedding degree: `r ∣ p¹² − 1`, by the kernel. -/
theorem R_dvd : R ∣ P ^ 12 - 1 := Nat.dvd_of_mod_eq_zero (by decide +kernel)

/-- EthLib's exponent is `(p¹² − 1)/r`. -/
theorem finalExpExponent_eq : finalExpExponent = finalExpExp := rfl

/-- **The cube lemma**: in `𝔽_{p¹²}`, `(f^((p¹²−1)/r))³ = 1` exactly when `f^((p¹²−1)/r) = 1`,
since `gcd(3, r) = 1` and `f^(p¹²−1) = 1` for `f ≠ 0`. -/
theorem cube_lemma (f : GFp12) : (f ^ finalExpExp) ^ 3 = 1 ↔ f ^ finalExpExp = 1 := by
  constructor
  · intro h3
    by_cases hf : f = 0
    · exfalso
      rw [hf, zero_pow (by decide), zero_pow (by decide)] at h3
      exact zero_ne_one h3
    have hr : (f ^ finalExpExp) ^ R = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel R_dvd]
      exact pow_card_sub_one_GFp12 hf
    have hg := pow_gcd_eq_one.mpr ⟨h3, hr⟩
    rwa [R_coprime_three, pow_one] at hg
  · intro h; rw [h, one_pow]

/-- EthLib's final exponentiation is the power `(p¹² − 1)/r`. -/
theorem ethFinalExp_eq_pow (acc : EthLib.Cryptography.Bls.Fp12) :
    (ofEth12 (finalExponentiation acc)).toGF = (ofEth12 acc).toGF ^ finalExpExp := by
  rw [finalExponentiation, toGF_ofEth12_powNat, finalExpExponent_eq]

/-- `Fp6.mul`'s result is reduced whatever its arguments: each coordinate ends in an `Fp2`
product or an operation of reduced ones. -/
theorem Fp6.reduced_mul' (a b : Fp6) : (a.mul b).Reduced := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Fp6.mul] <;> fp2_reduced

/-- `Fp12.mul`'s result is reduced whatever its arguments. -/
theorem Fp12.reduced_mul' (a b : Fp12) : (a.mul b).Reduced := by
  have := Fp6.reduced_mul' a.c0 b.c0; have := Fp6.reduced_mul' a.c1 b.c1
  have := Fp6.reduced_mul' (a.c0.add a.c1) (b.c0.add b.c1)
  refine ⟨?_, ?_⟩ <;> simp only [Fp12.mul] <;> fp6_reduced

/-- The runtime's final exponentiation ends in a product, so its result is reduced. -/
theorem reduced_finalExp (f : Fp12) : (finalExp f).Reduced := by
  unfold finalExp
  exact Fp12.reduced_mul' _ _

/-- The equation for one check: the runtime's `finalExp m` stands for the cube of EthLib's
`finalExponentiation acc`. Once H_vec's hypothesis; zkcrypto's chain is now proved
(`finalExp_toGF`), and for a reduced `m` this holds exactly when `m^((p¹²−1)/r)` and
`acc^((p¹²−1)/r)` agree (`finalExpCube_iff`), which the two Miller loops do on G2
(`millerLoopsCube`, `LeanLightProofs.Bls.FavEth`). -/
def FinalExpCube (m : Fp12) (acc : EthLib.Cryptography.Bls.Fp12) : Prop :=
  (finalExp m).toGF = (ofEth12 (finalExponentiation acc)).toGF ^ 3

/-- Given H_vec's equation, the runtime's check that the final exponentiation is one is
EthLib's: the cube is one exactly when the value is (`cube_lemma`). -/
theorem finalExp_isOne_iff {m : Fp12} {acc : EthLib.Cryptography.Bls.Fp12}
    (h : FinalExpCube m acc) :
    (finalExp m).isOne = true ↔ (finalExponentiation acc).isOne = true := by
  rw [Fp12.isOne_iff (reduced_finalExp m), h, isOne_ofEth12_iff, ethFinalExp_eq_pow]
  exact cube_lemma _

end LeanLight.Lc.Bls
