import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Granger–Scott squaring, over any commutative ring (25c)

The algebra behind the runtime's cyclotomic squaring (`LeanLight.Bls.cycSqr`, Granger and Scott,
eprint 2009/565), ported from gattaca-com/silver's `Spec/Cyclotomic/Cubic.lean` and
`Frobenius.lean`. Nothing here is about BLS12-381: `S` is any nontrivial commutative ring, `u`
any element of it, and `Cubic u = S[w]/(w³ − u)`, where `assemble u a b c = a + b·w + c·w²`.

* `granger_scott_of_frobenius_relation`: if `δ² − δ + 1 = 0` and
  `g · (a + δ²b·w + δ⁴c·w²) = ā + δ b̄·w + δ² c̄·w²` for `g = a + b·w + c·w²`, then
  `g² = (3a² − 2ā) + (3u c² + 2b̄)·w + (3b² − 2c̄)·w²`. With `ā, b̄, c̄` the conjugates over the
  quadratic subfield, the hypothesis is `g · g^(q²) = g^q` (`cyclotomic_relation`: what an element
  of order dividing `q² − q + 1` satisfies), and the conclusion is Granger–Scott's formula.
* `coefficient_frobenius`: in characteristic `p`, a `p^n`-th power of `Σ aⱼ xʲ` with `x⁶ = ξ`
  and `p^n = 6k + 1` is `Σ aⱼ^(p^n) ξ^(jk) xʲ`.
-/

namespace LeanLight.Lc.Bls.Cyclotomic

open Polynomial

section Cubic

variable {S : Type*} [CommRing S]

/-- `X³ − u`. -/
noncomputable abbrev cubicPolynomial (u : S) : S[X] := X ^ 3 - C u

/-- `S[w]/(w³ − u)`. -/
abbrev Cubic (u : S) := AdjoinRoot (cubicPolynomial u)

/-- `w`, the root of `X³ − u`. -/
noncomputable def w (u : S) : Cubic u := AdjoinRoot.root _

/-- `S` inside `S[w]/(w³ − u)`. -/
noncomputable def embed (u : S) : S →+* Cubic u := algebraMap S (Cubic u)

/-- `a + b·w + c·w²`. -/
noncomputable def assemble (u a b c : S) : Cubic u :=
  embed u a + embed u b * w u + embed u c * w u ^ 2

theorem w_cube (u : S) : w u ^ 3 = embed u u := by
  have h := AdjoinRoot.eval₂_root (cubicPolynomial u)
  rw [cubicPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h

theorem assemble_mul (u a b c d e f : S) :
    assemble u a b c * assemble u d e f =
      assemble u (a * d + u * (b * f + c * e))
        (a * e + b * d + u * c * f) (a * f + b * e + c * d) := by
  have h3 := w_cube u
  have h4 : w u ^ 4 = embed u u * w u := by rw [show 4 = 3 + 1 by rfl, pow_succ, h3]
  simp only [assemble, map_add, map_mul]
  ring_nf
  rw [h4, h3]
  ring

theorem assemble_square (u a b c : S) :
    assemble u a b c ^ 2 =
      assemble u (a ^ 2 + 2 * u * b * c) (2 * a * b + u * c ^ 2) (2 * a * c + b ^ 2) := by
  rw [sq, assemble_mul]
  congr 1 <;> ring

variable [Nontrivial S]

/-- The basis `1, w, w²` of `S[w]/(w³ − u)` over `S`. -/
noncomputable def basis (u : S) : Module.Basis (Fin 3) S (Cubic u) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C u (by decide : 3 ≠ 0))).basis.reindex
    (finCongr (natDegree_X_pow_sub_C (n := 3) (r := u)))

theorem basis_eq (u : S) (i : Fin 3) : basis u i = w u ^ i.val := by
  unfold basis
  simp only [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem assemble_eq (u a b c : S) :
    assemble u a b c = a • basis u 0 + b • basis u 1 + c • basis u 2 := by
  simp [basis_eq, assemble, Algebra.smul_def, embed]

/-- `1, w, w²` are independent over `S`. -/
theorem assemble_injective (u a b c d e f : S)
    (h : assemble u a b c = assemble u d e f) : a = d ∧ b = e ∧ c = f := by
  have h0 := congrArg (fun x => (basis u).repr x 0) h
  have h1 := congrArg (fun x => (basis u).repr x 1) h
  have h2 := congrArg (fun x => (basis u).repr x 2) h
  simp only [assemble_eq, map_add, map_smul, Module.Basis.repr_self,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at h0 h1 h2
  norm_num [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem embed_injective (u : S) : Function.Injective (embed u) := by
  intro a b h
  have ha : assemble u a 0 0 = embed u a := by simp [assemble]
  have hb : assemble u b 0 0 = embed u b := by simp [assemble]
  exact (assemble_injective u a 0 0 b 0 0 (by rw [ha, hb, h])).1

/-- The coefficients Granger–Scott's formula needs, from the Frobenius relation; no inverse or
cancellation in `S` is used. -/
theorem coefficient_constraints (u a b c abar bbar cbar delta : S)
    (hd : delta ^ 2 - delta + 1 = 0)
    (h : assemble u a b c * assemble u a (delta ^ 2 * b) (delta ^ 4 * c) =
      assemble u abar (delta * bbar) (delta ^ 2 * cbar)) :
    a ^ 2 - u * b * c = abar ∧ a * b - u * c ^ 2 = bbar ∧ b ^ 2 - a * c = cbar := by
  rw [assemble_mul] at h
  obtain ⟨ha, hb, hc⟩ := assemble_injective _ _ _ _ _ _ _ h
  constructor
  · linear_combination ha - u * b * c * (delta ^ 2 + delta + 1) * hd
  constructor
  · linear_combination (1 - delta) * hb +
      (a * b * delta + u * c ^ 2 * (delta ^ 3 - delta - 1) - bbar) * hd
  · linear_combination (-delta) * hc +
      (a * c * (delta ^ 3 + delta ^ 2 - 1) + (b ^ 2 - cbar) * (delta + 1)) * hd

/-- **Granger–Scott's squaring**, given the Frobenius relation `g · g^(q²) = g^q` in
coordinates (the module docstring). -/
theorem granger_scott_of_frobenius_relation (u a b c abar bbar cbar delta : S)
    (hd : delta ^ 2 - delta + 1 = 0)
    (h : assemble u a b c * assemble u a (delta ^ 2 * b) (delta ^ 4 * c) =
      assemble u abar (delta * bbar) (delta ^ 2 * cbar)) :
    assemble u a b c ^ 2 =
      assemble u (3 * a ^ 2 - 2 * abar) (3 * u * c ^ 2 + 2 * bbar) (3 * b ^ 2 - 2 * cbar) := by
  obtain ⟨ha, hb, hc⟩ := coefficient_constraints _ _ _ _ _ _ _ _ hd h
  rw [assemble_square]
  congr 1
  · linear_combination -2 * ha
  · linear_combination 2 * hb
  · linear_combination -2 * hc

end Cubic

/-- An element of order dividing `q² − q + 1` has `g · g^(q²) = g^q`. -/
theorem cyclotomic_relation {T : Type*} [Monoid T] (g : T) (q : ℕ) (hq : 1 ≤ q)
    (hphi : g ^ (q ^ 2 - q + 1) = 1) : g * g ^ (q ^ 2) = g ^ q := by
  have hle : q ≤ q ^ 2 := by nlinarith
  calc
    g * g ^ (q ^ 2) = g ^ (q ^ 2 + 1) := (pow_succ' g (q ^ 2)).symm
    _ = g ^ ((q ^ 2 - q + 1) + q) := by congr 1; omega
    _ = g ^ (q ^ 2 - q + 1) * g ^ q := pow_add _ _ _
    _ = g ^ q := by rw [hphi, one_mul]

section Frobenius

variable {R : Type*} [CommRing R]

theorem root_power (x xi : R) (n k : ℕ) (hn : n = 6 * k + 1) (hx : x ^ 6 = xi) :
    x ^ n = xi ^ k * x := by rw [hn, pow_succ, pow_mul, hx]

theorem monomial_frobenius (p n : ℕ) [Fact p.Prime] [CharP R p]
    (x xi a : R) (j k : ℕ) (hp : p ^ n = 6 * k + 1) (hx : x ^ 6 = xi) :
    (a * x ^ j) ^ (p ^ n) = a ^ (p ^ n) * xi ^ (j * k) * x ^ j := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm j (p ^ n), pow_mul, root_power x xi _ k hp hx,
    mul_pow, ← pow_mul]
  rw [Nat.mul_comm k j]
  ring

/-- The `p^n`-th power of `Σ aⱼ xʲ` with `x⁶ = ξ`, `p^n = 6k + 1`, in characteristic `p`. -/
theorem coefficient_frobenius (p n : ℕ) [Fact p.Prime] [CharP R p]
    (x xi : R) (a : Fin 6 → R) (k : ℕ) (hp : p ^ n = 6 * k + 1) (hx : x ^ 6 = xi) :
    (∑ j : Fin 6, a j * x ^ j.val) ^ (p ^ n) =
      ∑ j : Fin 6, a j ^ (p ^ n) * xi ^ (j.val * k) * x ^ j.val := by
  rw [sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro j _
  exact monomial_frobenius p n x xi (a j) j.val k hp hx

end Frobenius

/-! ## The squaring's schedule, before any representation -/

namespace Schedule

variable {R : Type*} [CommRing R]

/-- Six coordinates `c₀₀ + c₀₁·v + c₀₂·v² + (c₁₀ + c₁₁·v + c₁₂·v²)·w`, `v = w²`. -/
structure Coeffs (R : Type*) where
  c00 : R
  c01 : R
  c02 : R
  c10 : R
  c11 : R
  c12 : R

/-- `(a + b·y)²` in `R[y]/(y² − ξ)`. -/
def fp4Square (xi a b : R) : R × R :=
  let s0 := a * a
  let s1 := b * b
  (s0 + xi * s1, (a + b) * (a + b) - s0 - s1)

/-- `3t − 2a`, as `2(t − a) + t`. -/
def less (t a : R) := (t - a) + (t - a) + t

/-- `3t + 2a`, as `2(t + a) + t`. -/
def plus (t a : R) := (t + a) + (t + a) + t

/-- Granger–Scott's squaring on the six coordinates. -/
def raw (xi : R) (x : Coeffs R) : Coeffs R :=
  let t0 := fp4Square xi x.c00 x.c11
  let t1 := fp4Square xi x.c10 x.c02
  let t2 := fp4Square xi x.c01 x.c12
  ⟨less t0.1 x.c00, less t1.1 x.c01, less t2.1 x.c02,
    plus (xi * t2.2) x.c10, plus t0.2 x.c11, plus t1.2 x.c12⟩

/-- `R[y]/(y² − ξ)`. -/
abbrev Q (xi : R) := QuadraticAlgebra R xi 0

/-- `y`, with `y² = ξ`. -/
noncomputable abbrev omega (xi : R) : Q xi := QuadraticAlgebra.omega

/-- The coefficient of `1`: `c₀₀ + c₁₁·y` (`y = w³`). -/
def ca (xi : R) (x : Coeffs R) : Q xi := ⟨x.c00, x.c11⟩

/-- The coefficient of `w`: `c₁₀ + c₀₂·y`. -/
def cb (xi : R) (x : Coeffs R) : Q xi := ⟨x.c10, x.c02⟩

/-- The coefficient of `w²`: `c₀₁ + c₁₂·y`. -/
def cc (xi : R) (x : Coeffs R) : Q xi := ⟨x.c01, x.c12⟩

/-- The six coordinates as an element of `Q[w]/(w³ − y)`. -/
noncomputable def decode (xi : R) (x : Coeffs R) :=
  assemble (omega xi) (ca xi x) (cb xi x) (cc xi x)

theorem raw_a (xi : R) (x : Coeffs R) :
    ca xi (raw xi x) = 3 * (ca xi x) ^ 2 - 2 * star (ca xi x) := by
  ext <;> simp [ca, raw, fp4Square, less, plus, pow_two, QuadraticAlgebra.star_mk,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem raw_b (xi : R) (x : Coeffs R) :
    cb xi (raw xi x) = 3 * omega xi * (cc xi x) ^ 2 + 2 * star (cb xi x) := by
  ext <;> simp [cb, cc, raw, fp4Square, less, plus, pow_two, QuadraticAlgebra.star_mk,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem raw_c (xi : R) (x : Coeffs R) :
    cc xi (raw xi x) = 3 * (cb xi x) ^ 2 - 2 * star (cc xi x) := by
  ext <;> simp [cb, cc, raw, fp4Square, less, plus, pow_two, QuadraticAlgebra.star_mk,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem raw_decode (xi : R) (x : Coeffs R) :
    decode xi (raw xi x) = assemble (omega xi) (3 * (ca xi x) ^ 2 - 2 * star (ca xi x))
      (3 * omega xi * (cc xi x) ^ 2 + 2 * star (cb xi x))
      (3 * (cb xi x) ^ 2 - 2 * star (cc xi x)) := by
  simp only [decode, raw_a, raw_b, raw_c]

/-- The conjugate `c₀ − c₁·w` on coordinates. -/
def conjugate (x : Coeffs R) : Coeffs R :=
  ⟨x.c00, x.c01, x.c02, -x.c10, -x.c11, -x.c12⟩

/-- The six coordinates in the order of the powers `1, w, …, w⁵`. -/
def powers (x : Coeffs R) : Fin 6 → R := ![x.c00, x.c10, x.c01, x.c11, x.c02, x.c12]

end Schedule

end LeanLight.Lc.Bls.Cyclotomic
