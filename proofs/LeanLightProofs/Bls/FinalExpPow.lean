import LeanLightProofs.Bls.Frobenius
import LeanLightProofs.Bls.FinalExp

/-!
# BLS12-381: the runtime's final exponentiation is the cube of the final exponentiation (25c)

`finalExp_toGF`: on every reduced `f`, the runtime's `finalExp f` (zkcrypto's chain: the easy
part by a conjugation, an inversion and the Frobenius, the hard part by five exponentiations by
`x` with Granger–Scott cyclotomic squarings) is `f^(3·(p¹²−1)/r)` in `𝔽_{p¹²}`. No hypothesis
beyond `f` reduced (each coordinate below `p`, which every value the runtime computes is): for
`f = 0` both sides are `0`.

The proof is gattaca-com/silver's (`Pairing/FinalModel.lean`, `FinalInvariant.lean`,
`FinalVerdict.lean`), ported to the runtime's values:

* each operation of the chain is a power on the values it meets (`LeanLightProofs.Bls.Frobenius`):
  `Fp12.mul` the product, `Fp12.inv` the inverse, `Fp12.frob` `f ↦ f^p`, `Fp12.conj`
  `f ↦ f^(p⁶)`, `cycSqr` the square on the cyclotomic subgroup `f^(p⁴−p²+1) = 1` (and on `0`),
  and `cycExpX` `f ↦ (f^x)^(p⁶)` there (`toGF_cycExpX`, its loop over the bits of `|x|`);
* the easy part lands in the cyclotomic subgroup (`easyPart_inCyc`), which every later step keeps
  (`InCyc`), so the chain (`hardChain`, the same schedule for values and for exponents) is
  `f^(easyExponent · hardExponent)`;
* `exponent_certificate`: `easyExponent · hardExponent ≡ 3·(p¹²−1)/r (mod p¹² − 1)`, by the
  kernel, and `f^(p¹²−1) = 1` for `f ≠ 0`.

Hence (`finalExpCube_iff`) H_vec's former hypothesis `FinalExpCube m acc` holds exactly when the
runtime's Miller value `m` and EthLib's accumulator `acc` agree after the final exponentiation,
`m^((p¹²−1)/r) = acc^((p¹²−1)/r)`: a statement about the two Miller loops alone, and
(`finalExp_isOne_iff_pow`) the runtime's check `(finalExp m).isOne` is `m^((p¹²−1)/r) = 1`.
-/

namespace LeanLight.Lc.Bls

open _root_.LeanLight.Lc.Bls.Cyclotomic

/-! ## The cyclotomic subgroup -/

/-- `p⁴ − p² + 1`, `Φ₁₂(p)`: the cyclotomic subgroup of `𝔽_{p¹²}` is `{f | f^(p⁴−p²+1) = 1}`. -/
abbrev cycOrder : ℕ := P ^ 4 - P ^ 2 + 1

/-- `y` is in the cyclotomic subgroup, or zero. -/
def InCyc (y : GFp12) : Prop := y = 0 ∨ y ^ cycOrder = 1

theorem InCyc.mul {x y : GFp12} (hx : InCyc x) (hy : InCyc y) : InCyc (x * y) := by
  rcases hx with hx | hx
  · exact Or.inl (by rw [hx, zero_mul])
  rcases hy with hy | hy
  · exact Or.inl (by rw [hy, mul_zero])
  exact Or.inr (by rw [mul_pow, hx, hy, one_mul])

theorem InCyc.pow {x : GFp12} (hx : InCyc x) (n : ℕ) : InCyc (x ^ n) := by
  rcases hx with hx | hx
  · subst x
    cases n with
    | zero => exact Or.inr (by simp)
    | succ n => exact Or.inl (by simp)
  · exact Or.inr (by rw [← pow_mul, Nat.mul_comm, pow_mul, hx, one_pow])

/-! ## `cycExpX`, the exponentiation by `x` -/

/-- A loop over `List.range' s n` in `Id` whose body always continues, with an invariant
indexed by the position. -/
theorem forIn_range'_inv {β : Type} (I : ℕ → β → Prop) (g : ℕ → β → Id (ForInStep β)) :
    ∀ (n s : ℕ) (b : β), (∀ k b, s ≤ k → k < s + n → I k b → ∃ c, g k b = .yield c ∧ I (k + 1) c) →
      I s b → I (s + n) (forIn (List.range' s n) b g).run := by
  intro n
  induction n with
  | zero => intro s b _ h; exact h
  | succ n ih =>
    intro s b hs h
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨c, hc, hI⟩ := hs s b (le_refl s) (by omega) h
    rw [hc]
    have := ih (s + 1) c (fun k b h1 h2 => hs k b (by omega) (by omega)) hI
    rwa [Nat.add_assoc, Nat.add_comm 1 n] at this

/-- The bits of `|x|` from the top: `⌊|x|/2^(63−k)⌋ = 2⌊|x|/2^(64−k)⌋ + bit`. -/
theorem X_shift_succ : ∀ k < 64, X >>> (63 - k) = 2 * (X >>> (64 - k)) + X >>> (63 - k) % 2 := by
  decide +kernel

/-- **The exponentiation by `x`**: on a reduced `f` in the cyclotomic subgroup (or zero),
`cycExpX f` is `(f^|x|)^(p⁶)` (which is `f^x` there, `x < 0`), and reduced. -/
theorem toGF_cycExpX {a : Fp12} (ha : a.Reduced) (hc : InCyc a.toGF) :
    (cycExpX a).Reduced ∧ (cycExpX a).toGF = (a.toGF ^ X) ^ (P ^ 6) := by
  unfold cycExpX
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have hX64 : X >>> 64 = 0 := by decide +kernel
  refine (fun H => ⟨Fp12.reduced_conj H.1, ?_⟩) (forIn_range'_inv (fun k (s : Fp12 × Bool) =>
      s.1.Reduced ∧ s.1.toGF = a.toGF ^ (X >>> (64 - k)) ∧ (s.2 = true ↔ X >>> (64 - k) ≠ 0))
      _ 64 0 (Fp12.one, false) ?_ ⟨Fp12.reduced_one, by simp [hX64], by simp [hX64]⟩)
  · intro k s _ hk ⟨hr, ht, hf⟩
    rw [Nat.zero_add] at hk
    · have hx := X_shift_succ k hk
      have hb : X >>> (63 - k) % 2 < 2 := Nat.mod_lt _ (by decide)
      rw [show 64 - (k + 1) = 63 - k by omega]
      have hcm : InCyc (a.toGF ^ (X >>> (64 - k))) := hc.pow _
      split
      · next h2 =>
        have hm : X >>> (64 - k) ≠ 0 := hf.mp h2
        rw [← ht] at hcm
        split
        · next hbit =>
          refine ⟨_, rfl, Fp12.reduced_mul (reduced_cycSqr hr) ha, ?_, ?_⟩
          · rw [Fp12.toGF_mul (reduced_cycSqr hr) ha, toGF_cycSqr hr hcm, ht, hx, hbit]; ring
          · simp only [h2, true_iff]; omega
        · next hbit =>
          refine ⟨_, rfl, reduced_cycSqr hr, ?_, ?_⟩
          · rw [toGF_cycSqr hr hcm, ht, hx, show X >>> (63 - k) % 2 = 0 by omega, Nat.add_zero]; ring
          · simp only [h2, true_iff]; omega
      · next h2 =>
        have hm : X >>> (64 - k) = 0 := by
          by_contra h; exact h2 (hf.mpr h)
        rw [hm, pow_zero] at ht
        split
        · next hbit =>
          refine ⟨_, rfl, Fp12.reduced_mul hr ha, ?_, ?_⟩
          · rw [Fp12.toGF_mul hr ha, ht, hx, hm, hbit, one_mul]; simp
          · simp only [hbit, decide_true, true_iff]; omega
        · next hbit =>
          refine ⟨_, rfl, hr, ?_, ?_⟩
          · rw [ht, hx, hm, show X >>> (63 - k) % 2 = 0 by omega]; simp
          · simp only [hbit, decide_false, Bool.false_eq_true, false_iff, not_not]; omega
  · exact (Fp12.toGF_conj_pow H.1).trans (by rw [H.2.1]; simp)

/-! ## The chain -/

/-- zkcrypto's hard-part schedule, over any operations: for the runtime's values
(`finalExp_eq_chain`) and for exponents (`hardExponent`). -/
def hardChain {α : Type} (mul : α → α → α) (square conjugate exp frobenius : α → α) (a : α) : α :=
  let t11 := conjugate (square a)
  let t3 := exp a
  let t4 := square t3
  let t5 := mul t11 t3
  let t12 := exp t5
  let t01 := exp t12
  let t6 := mul (exp t01) t4
  let t41 := exp t6
  let t42 := mul t41 (mul (conjugate t5) a)
  let t13 := frobenius (frobenius (frobenius (mul t12 a)))
  let t61 := frobenius (mul t6 (conjugate a))
  let t31 := frobenius (frobenius (mul t3 t01))
  mul (mul (mul t31 t13) t61) t42

/-- The runtime's easy part, `(f̄ · f⁻¹)^(p²) · (f̄ · f⁻¹)`. -/
def easyPart (f : Fp12) : Fp12 :=
  let t := f.conj.mul f.inv
  t.frob.frob.mul t

/-- `finalExp` is the hard part's schedule after the easy part. -/
theorem finalExp_eq_chain (f : Fp12) :
    finalExp f = hardChain Fp12.mul cycSqr Fp12.conj cycExpX Fp12.frob (easyPart f) := rfl

/-- The schedule commutes with a map that is a homomorphism on the values satisfying a predicate
the operations keep. -/
theorem hardChain_map_of {α β : Type} (Pr : α → Prop) (F : α → β)
    {mul : α → α → α} {sq cj ex fr : α → α} {mul' : β → β → β} {sq' cj' ex' fr' : β → β}
    (hm : ∀ a b, Pr a → Pr b → Pr (mul a b) ∧ F (mul a b) = mul' (F a) (F b))
    (hs : ∀ a, Pr a → Pr (sq a) ∧ F (sq a) = sq' (F a))
    (hc : ∀ a, Pr a → Pr (cj a) ∧ F (cj a) = cj' (F a))
    (he : ∀ a, Pr a → Pr (ex a) ∧ F (ex a) = ex' (F a))
    (hf : ∀ a, Pr a → Pr (fr a) ∧ F (fr a) = fr' (F a)) {a : α} (ha : Pr a) :
    F (hardChain mul sq cj ex fr a) = hardChain mul' sq' cj' ex' fr' (F a) := by
  simp only [hardChain]
  obtain ⟨p1, e1⟩ := hs a ha
  obtain ⟨p2, e2⟩ := hc _ p1
  obtain ⟨p3, e3⟩ := he a ha
  obtain ⟨p4, e4⟩ := hs _ p3
  obtain ⟨p5, e5⟩ := hm _ _ p2 p3
  obtain ⟨p6, e6⟩ := he _ p5
  obtain ⟨p7, e7⟩ := he _ p6
  obtain ⟨p8, e8⟩ := he _ p7
  obtain ⟨p9, e9⟩ := hm _ _ p8 p4
  obtain ⟨p10, e10⟩ := he _ p9
  obtain ⟨p11, e11⟩ := hc _ p5
  obtain ⟨p12, e12⟩ := hm _ _ p11 ha
  obtain ⟨p13, e13⟩ := hm _ _ p10 p12
  obtain ⟨p14, e14⟩ := hm _ _ p6 ha
  obtain ⟨p15, e15⟩ := hf _ p14
  obtain ⟨p16, e16⟩ := hf _ p15
  obtain ⟨p17, e17⟩ := hf _ p16
  obtain ⟨p18, e18⟩ := hc _ ha
  obtain ⟨p19, e19⟩ := hm _ _ p9 p18
  obtain ⟨p20, e20⟩ := hf _ p19
  obtain ⟨p21, e21⟩ := hm _ _ p3 p7
  obtain ⟨p22, e22⟩ := hf _ p21
  obtain ⟨p23, e23⟩ := hf _ p22
  obtain ⟨p24, e24⟩ := hm _ _ p23 p17
  obtain ⟨p25, e25⟩ := hm _ _ p24 p20
  obtain ⟨_, e26⟩ := hm _ _ p25 p13
  simp only [e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11,
    e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]

/-- The hard part's exponent: the schedule on exponents, with the square doubling, the conjugate
multiplying by `p⁶`, the exponentiation by `x` by `|x|·p⁶`, the Frobenius by `p`. -/
def hardExponent : ℕ := hardChain (· + ·) (· * 2) (· * P ^ 6) (fun n => n * X * P ^ 6) (· * P) 1

/-- The easy part's exponent, the inverse read as the power `p¹² − 2`. -/
def easyExponent : ℕ := (P ^ 6 + (P ^ 12 - 2)) * (P * P + 1)

theorem chain_power {K : Type} [CommMonoid K] (x : K) (p z : ℕ) :
    hardChain (· * ·) (· ^ 2) (· ^ (p ^ 6)) (fun a => (a ^ z) ^ (p ^ 6)) (· ^ p) x =
      x ^ (hardChain (· + ·) (· * 2) (· * p ^ 6) (fun n => n * z * p ^ 6) (· * p) 1) := by
  simp only [hardChain, ← pow_mul, ← pow_add, ← pow_succ, one_mul]

/-- **The exponent certificate**, by the kernel: the chain's exponent is `3·(p¹²−1)/r` modulo
`p¹² − 1`. -/
theorem exponent_certificate :
    easyExponent * hardExponent % (P ^ 12 - 1) = 3 * finalExpExp % (P ^ 12 - 1) := by
  decide +kernel

/-- The easy part lands in the cyclotomic subgroup, by the kernel: `p¹² − 1` divides
`easyExponent · (p⁴ − p² + 1)`. -/
theorem easy_certificate : easyExponent * cycOrder % (P ^ 12 - 1) = 0 := by
  decide +kernel

theorem inverse_power (x : GFp12) : x⁻¹ = x ^ (P ^ 12 - 2) := by
  by_cases hx : x = 0
  · subst x
    rw [inv_zero, zero_pow (by decide +kernel : P ^ 12 - 2 ≠ 0)]
  · symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show P ^ 12 - 2 + 1 = P ^ 12 - 1 from by decide +kernel]
    exact pow_card_sub_one_GFp12 hx

/-- `x^e = x^(e mod (p¹² − 1))` for `x ≠ 0`. -/
theorem pow_mod_period {x : GFp12} (hx : x ≠ 0) (e : ℕ) : x ^ e = x ^ (e % (P ^ 12 - 1)) :=
  pow_eq_pow_mod e (pow_card_sub_one_GFp12 hx)

theorem reduced_easyPart {f : Fp12} (hf : f.Reduced) : (easyPart f).Reduced :=
  Fp12.reduced_mul (Fp12.reduced_frob (Fp12.reduced_frob (Fp12.reduced_mul
    (Fp12.reduced_conj hf) (Fp12.reduced_inv hf)))) (Fp12.reduced_mul
    (Fp12.reduced_conj hf) (Fp12.reduced_inv hf))

theorem toGF_easyPart {f : Fp12} (hf : f.Reduced) :
    (easyPart f).toGF = f.toGF ^ easyExponent := by
  have hc := Fp12.reduced_conj hf
  have hi := Fp12.reduced_inv hf
  have ht := Fp12.reduced_mul hc hi
  simp only [easyPart]
  rw [Fp12.toGF_mul (Fp12.reduced_frob (Fp12.reduced_frob ht)) ht,
    Fp12.toGF_frob (Fp12.reduced_frob ht), Fp12.toGF_frob ht, Fp12.toGF_mul hc hi,
    Fp12.toGF_conj_pow hf, Fp12.toGF_inv hf, inverse_power, easyExponent, ← pow_add, ← pow_mul,
    ← pow_mul, ← pow_add, Nat.mul_add_one]

theorem easyPart_inCyc {f : Fp12} (hf : f.Reduced) : InCyc (easyPart f).toGF := by
  rw [toGF_easyPart hf]
  by_cases h : f.toGF = 0
  · exact Or.inl (by rw [h, zero_pow (by decide +kernel)])
  · exact Or.inr (by rw [← pow_mul, pow_mod_period h, easy_certificate, pow_zero])

/-- **The runtime's final exponentiation**: on every reduced `f` (each coordinate below `p`),
`finalExp f` is `f^(3·(p¹²−1)/r)` in `𝔽_{p¹²}`, the cube of the final exponentiation. -/
theorem finalExp_toGF {f : Fp12} (hf : f.Reduced) :
    (finalExp f).toGF = f.toGF ^ (3 * finalExpExp) := by
  have hmap := hardChain_map_of (fun a : Fp12 => a.Reduced ∧ InCyc a.toGF) Fp12.toGF
    (mul := Fp12.mul) (sq := cycSqr) (cj := Fp12.conj) (ex := cycExpX) (fr := Fp12.frob)
    (mul' := (· * ·)) (sq' := (· ^ 2)) (cj' := (· ^ (P ^ 6))) (ex' := fun y => (y ^ X) ^ (P ^ 6))
    (fr' := (· ^ P))
    (fun a b ha hb => by
      rw [Fp12.toGF_mul ha.1 hb.1]
      exact ⟨⟨Fp12.reduced_mul ha.1 hb.1, ha.2.mul hb.2⟩,
        rfl⟩)
    (fun a ha => by
      rw [toGF_cycSqr ha.1 ha.2]
      exact ⟨⟨reduced_cycSqr ha.1, ha.2.pow 2⟩, rfl⟩)
    (fun a ha => by
      rw [Fp12.toGF_conj_pow ha.1]
      exact ⟨⟨Fp12.reduced_conj ha.1, ha.2.pow _⟩, rfl⟩)
    (fun a ha => by
      obtain ⟨h1, h2⟩ := toGF_cycExpX ha.1 ha.2
      rw [h2]
      exact ⟨⟨h1, (ha.2.pow _).pow _⟩, rfl⟩)
    (fun a ha => by
      rw [Fp12.toGF_frob ha.1]
      exact ⟨⟨Fp12.reduced_frob ha.1, ha.2.pow _⟩, rfl⟩)
    ⟨reduced_easyPart hf, easyPart_inCyc hf⟩
  rw [finalExp_eq_chain, hmap, chain_power, toGF_easyPart hf, ← pow_mul]
  change f.toGF ^ (easyExponent * hardExponent) = _
  by_cases h : f.toGF = 0
  · rw [h, zero_pow (by decide +kernel), zero_pow (by decide +kernel)]
  · rw [pow_mod_period h, exponent_certificate, ← pow_mod_period h]

/-- The same, as the cube: `finalExp f` is `(f^((p¹²−1)/r))³` on every reduced `f`. -/
theorem finalExp_eq_cube {f : Fp12} (hf : f.Reduced) :
    (finalExp f).toGF = (f.toGF ^ finalExpExp) ^ 3 := by
  rw [finalExp_toGF hf, ← pow_mul, Nat.mul_comm]

/-! ## H_vec's former hypothesis -/

/-- `f^((p¹²−1)/r)` is `0` or an `r`-th root of unity. -/
theorem pow_finalExpExp_root (f : GFp12) :
    f ^ finalExpExp = 0 ∨ (f ^ finalExpExp) ^ R = 1 := by
  by_cases hf : f = 0
  · exact Or.inl (by rw [hf, zero_pow (by decide +kernel)])
  · exact Or.inr (by rw [← pow_mul, Nat.div_mul_cancel R_dvd]; exact pow_card_sub_one_GFp12 hf)

/-- The cube is injective on `0` and the `r`-th roots of unity (`gcd(3, r) = 1`). -/
theorem cube_inj {x y : GFp12} (hx : x = 0 ∨ x ^ R = 1) (hy : y = 0 ∨ y ^ R = 1)
    (h : x ^ 3 = y ^ 3) : x = y := by
  rcases hx with hx | hx
  · subst hx
    rw [zero_pow (by decide)] at h
    exact (pow_eq_zero_iff (by decide)).mp h.symm |>.symm
  rcases hy with hy | hy
  · subst hy
    rw [zero_pow (by decide)] at h
    exact (pow_eq_zero_iff (by decide)).mp h
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow (by decide +kernel)] at hy; exact zero_ne_one hy
  have h3 : (x * y⁻¹) ^ 3 = 1 := by rw [mul_pow, h, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hy0)]
  have hr : (x * y⁻¹) ^ R = 1 := by rw [mul_pow, hx, inv_pow, hy, inv_one, one_mul]
  have hg := pow_gcd_eq_one.mpr ⟨h3, hr⟩
  rw [R_coprime_three, pow_one] at hg
  exact mul_inv_eq_one₀ hy0 |>.mp hg

/-- **`FinalExpCube` is a statement about the Miller values alone**: for a reduced runtime
Miller value `m` and any EthLib accumulator `acc`, H_vec's former equation
`FinalExpCube m acc` holds exactly when `m` and `acc` agree after the final exponentiation,
`m^((p¹²−1)/r) = acc^((p¹²−1)/r)` in `𝔽_{p¹²}`. -/
theorem finalExpCube_iff {m : Fp12} (hm : m.Reduced) (acc : EthLib.Cryptography.Bls.Fp12) :
    FinalExpCube m acc ↔ m.toGF ^ finalExpExp = (ofEth12 acc).toGF ^ finalExpExp := by
  rw [FinalExpCube, finalExp_eq_cube hm, ethFinalExp_eq_pow]
  exact ⟨cube_inj (pow_finalExpExp_root _) (pow_finalExpExp_root _), fun h => by rw [h]⟩

/-- **The runtime's check**: for a reduced `m`, `(finalExp m).isOne` is `m^((p¹²−1)/r) = 1`, the
final exponentiation's verdict (`cube_lemma`). -/
theorem finalExp_isOne_iff_pow {m : Fp12} (hm : m.Reduced) :
    (finalExp m).isOne = true ↔ m.toGF ^ finalExpExp = 1 := by
  rw [Fp12.isOne_iff (reduced_finalExp m), finalExp_eq_cube hm]
  exact cube_lemma _

/-! ## The Miller loop's value is reduced -/

/-- A loop in `Id` whose body keeps an invariant keeps it. -/
theorem forIn_id_inv {α β : Type} (I : β → Prop) (l : List α) (b : β)
    (g : α → β → Id (ForInStep β)) (h0 : I b) (hs : ∀ a b, I b → I (g a b).run.value) :
    I (forIn l b g).run := by
  induction l generalizing b with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hs a b h0
    revert this
    cases g a b with
    | done c => intro h; exact h
    | yield c => intro h; exact ih c h

/-- A Miller-loop line product is reduced, whatever its arguments. -/
theorem reduced_ell (f : Fp12) (c0 c1 c2 : Fp2) (p : G1A) : (ell f c0 c1 c2 p).Reduced := by
  have h01 : ∀ (a : Fp6) (c0 c1 : Fp2), (a.mulBy01 c0 c1).Reduced := fun a c0 c1 => by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Fp6.mulBy01] <;> fp2_reduced
  have := h01 f.c0 c2 (c1.mulFp p.x)
  have := h01 (f.c1.add f.c0) c2 ((c1.mulFp p.x).add (c0.mulFp p.y))
  have : (f.c1.mulBy1 (c0.mulFp p.y)).Reduced := Fp6.reduced_mulBy1
  refine ⟨?_, ?_⟩ <;> simp only [ell, Fp12.mulBy014] <;> fp6_reduced

/-- `Fp12.sqr`'s result is reduced, whatever its argument. -/
theorem Fp12.reduced_sqr' (a : Fp12) : a.sqr.Reduced := by
  have := Fp6.reduced_mul' a.c0 a.c1
  have := Fp6.reduced_mul' (a.c0.add a.c1) (a.c0.add a.c1.mulV)
  refine ⟨?_, ?_⟩ <;> simp only [Fp12.sqr] <;> fp6_reduced

/-- The runtime's Miller loop returns a reduced value, on any list of pairs. -/
theorem reduced_millerLoop (ps : List (G1A × G2A)) : (millerLoop ps).Reduced := by
  unfold millerLoop
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  refine Fp12.reduced_conj (forIn_id_inv (fun s : Fp12 × List G2J => s.1.Reduced) _ _ _
    Fp12.reduced_one ?_)
  intro k s hs
  split
  all_goals
    generalize hA : forIn (m := Id) (_ : List (G2J × (G1A × G2A))) (_ : Fp12 × List G2J) _ = A
    have hA' : A.run.1.Reduced := by
      rw [← hA]
      refine forIn_id_inv (fun s : Fp12 × List G2J => s.1.Reduced) _ _ _ ?_ ?_
      · first | exact Fp12.reduced_sqr' _ | exact hs
      · intro x t _; exact reduced_ell _ _ _ _ _
    simp only [Id.run_bind]
    split
    · generalize hB : forIn (m := Id) (_ : List (G2J × (G1A × G2A))) (_ : Fp12 × List G2J) _ = B
      have hB' : B.run.1.Reduced := by
        rw [← hB]
        refine forIn_id_inv (fun s : Fp12 × List G2J => s.1.Reduced) _ _ _ hA' ?_
        intro x t _; exact reduced_ell _ _ _ _ _
      simp only [Id.run_bind]
      exact hB'
    · exact hA'

end LeanLight.Lc.Bls
