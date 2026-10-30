import LeanLightProofs.Bls.Jacobian
import LeanLightProofs.Bls.Tower
import LeanLight.Bls.G1
import LeanLight.Bls.G2

/-!
# BLS12-381: G1 and G2, the group law of `Jac` (25c)

The runtime's points are read as Jacobian triples of `LeanLightProofs.Bls.Jacobian`: G1's
(`G1J.toJ`, `Nat`s below `P` cast to `𝔽_p`) on `E: y² = x³ + 4`, G2's (`G2J.toJ`, reduced `Fp2`s
read in `𝔽_{p²}`) on the twist `E': y² = x³ + 4(1 + u)`; an affine point `(x, y)` as
`(x, y, 1)` (`G1A.toJ`, `G2A.toJ`). On reduced values:

* **The formulas** (`G1J.toJ_dbl`, `toJ_add`, `toJ_addA`, `toJ_mulA`, and G2's): the runtime's
  doubling, addition, mixed addition and double-and-add are `Jac`'s, hence the group law
  (`G1J.dbl_spec` and the like, through `Jac.dbl_spec`, `Jac.add_spec`, `Jac.mulA_spec`).
* **The tests**: `G1A.onCurve` is the curve's equation, every point on the curve is nonsingular
  (the discriminant `−432·b²` is not zero), `G1J.isInf` is the identity (`G1J.isInf_iff`),
  `G1J.toAffine?` gives the affine point (`G1J.toAffine?_spec`), and likewise for G2.
* **The generators** are on their curves and `[r]G = O` (`g1Gen_order`, `g2Gen_order`), by
  the kernel running `G1J.mulA` and `G2J.mulA`.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

/-- Proves a runtime `Fp` value below `P` from its operations and the hypotheses in context. -/
syntax "fp_lt" : tactic
macro_rules
  | `(tactic| fp_lt) => `(tactic| with_reducible first
    | assumption | exact fmul_lt | exact fsqr_lt | exact fpow_lt _ | exact finv_lt
    | (apply fadd_lt <;> fp_lt) | (apply fsub_lt; fp_lt) | (apply fneg_lt; fp_lt)
    | (apply fdbl_lt; fp_lt) | exact (by decide : (4 : ℕ) < P) | exact (by decide : (0 : ℕ) < P)
    | exact (by decide : (1 : ℕ) < P))

/-- Pushes the cast `ℕ → 𝔽_p` through the runtime's `Fp` operations, proving the bounds. -/
macro "fp_push" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp (disch := exact le_of_lt (by fp_lt))
    only [cast_fadd, cast_fsub, cast_fneg, cast_fmul, cast_fsqr, cast_fdbl, cast_fpow,
      cast_finv] $(loc)?)

theorem two_ne_zero_GFp2 : (2 : GFp2) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.re_zero] at this
  exact two_ne_zero_GFp this

/-! ## G1 -/

/-- `E: y² = x³ + 4` over `𝔽_p`, in Jacobian coordinates. -/
abbrev E1 : WeierstrassCurve.Jacobian GFp := Jac.J 4

/-- On `E`, the curve's equation makes a point nonsingular: `E`'s discriminant is not zero. -/
theorem E1_nonsingular_iff {x y : GFp} : E1.Nonsingular ![x, y, 1] ↔ y ^ 2 = x ^ 3 + 4 := by
  rw [nonsingular_some, ← Affine.equation_iff_nonsingular_of_Δ_ne_zero, Affine.equation_iff]
  · constructor <;> intro h <;> linear_combination h
  · show (-432 * 16 : GFp) ≠ 0
    rw [show (-432 * 16 : GFp) = -((6912 : ℕ) : GFp) by push_cast; ring, neg_ne_zero, Ne,
      cast_eq_zero (by decide)]
    decide

/-- Equality of two runtime values below `P` is equality of their casts. -/
theorem nat_eq_iff_cast {a b : ℕ} (ha : a < P) (hb : b < P) : a = b ↔ (a : GFp) = b :=
  (cast_inj ha hb).symm

namespace G1J

/-- The triple of `𝔽_p` a runtime `G1J` stands for. -/
def toJ (p : G1J) : Fin 3 → GFp := ![(p.x : GFp), p.y, p.z]

/-- Every coordinate below `P`. -/
def Reduced (p : G1J) : Prop := p.x < P ∧ p.y < P ∧ p.z < P

@[simp] theorem toJ_0 (p : G1J) : p.toJ 0 = p.x := rfl
@[simp] theorem toJ_1 (p : G1J) : p.toJ 1 = p.y := rfl
@[simp] theorem toJ_2 (p : G1J) : p.toJ 2 = p.z := rfl

variable {p q : G1J}

theorem reduced_dbl (hp : p.Reduced) : p.dbl.Reduced := by
  obtain ⟨hx, hy, hz⟩ := hp
  unfold dbl
  split
  · exact ⟨hx, hy, hz⟩
  · exact ⟨by fp_lt, by fp_lt, by fp_lt⟩

theorem toJ_dbl (hp : p.Reduced) : p.dbl.toJ = Jac.dbl p.toJ := by
  obtain ⟨hx, hy, hz⟩ := hp
  unfold dbl Jac.dbl
  by_cases h : p.z = 0
  · rw [ite_eq_left h, ite_eq_left (show p.toJ 2 = 0 by simp [h])]
  have h' : ¬p.toJ 2 = 0 := by rw [toJ_2, cast_eq_zero hz]; exact h
  rw [ite_eq_right h, ite_eq_right h']
  funext i
  fin_cases i <;> simp only [toJ, Jac.dblF] <;> fp_push <;> simp <;> ring

theorem toJ_inf : inf.toJ = Jac.inf := by
  funext i; fin_cases i <;> simp [toJ, inf, Jac.inf]

theorem reduced_inf : inf.Reduced := ⟨by decide, by decide, by decide⟩

theorem reduced_add (hp : p.Reduced) (hq : q.Reduced) : (p.add q).Reduced := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy', hz'⟩ := hq
  unfold add
  split
  · exact ⟨hx', hy', hz'⟩
  split
  · exact ⟨hx, hy, hz⟩
  dsimp only
  split
  · split
    · exact reduced_dbl ⟨hx, hy, hz⟩
    · exact reduced_inf
  · exact ⟨by fp_lt, by fp_lt, by fp_lt⟩

theorem toJ_add (hp : p.Reduced) (hq : q.Reduced) : (p.add q).toJ = Jac.add p.toJ q.toJ := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy', hz'⟩ := hq
  unfold add Jac.add
  by_cases h1 : p.z = 0
  · rw [ite_eq_left h1, ite_eq_left (show p.toJ 2 = 0 by simp [h1])]
  have h1' : ¬p.toJ 2 = 0 := by rw [toJ_2, cast_eq_zero hz]; exact h1
  rw [ite_eq_right h1, ite_eq_right h1']
  by_cases h2 : q.z = 0
  · rw [ite_eq_left h2, ite_eq_left (show q.toJ 2 = 0 by simp [h2])]
  have h2' : ¬q.toJ 2 = 0 := by rw [toJ_2, cast_eq_zero hz']; exact h2
  rw [ite_eq_right h2, ite_eq_right h2']
  dsimp only
  by_cases h3 : fmul p.x (fsqr q.z) = fmul q.x (fsqr p.z)
  · have h3' : p.toJ 0 * (q.toJ 2 * q.toJ 2) = q.toJ 0 * (p.toJ 2 * p.toJ 2) := by
      rw [nat_eq_iff_cast fmul_lt fmul_lt] at h3; fp_push at h3; simpa using h3
    rw [ite_eq_left h3, ite_eq_left h3']
    by_cases h4 : fmul (fmul p.y q.z) (fsqr q.z) = fmul (fmul q.y p.z) (fsqr p.z)
    · have h4' : p.toJ 1 * q.toJ 2 * (q.toJ 2 * q.toJ 2) =
          q.toJ 1 * p.toJ 2 * (p.toJ 2 * p.toJ 2) := by
        rw [nat_eq_iff_cast fmul_lt fmul_lt] at h4; fp_push at h4; simpa using h4
      rw [ite_eq_left h4, ite_eq_left h4']
      exact toJ_dbl ⟨hx, hy, hz⟩
    · have h4' : ¬p.toJ 1 * q.toJ 2 * (q.toJ 2 * q.toJ 2) =
          q.toJ 1 * p.toJ 2 * (p.toJ 2 * p.toJ 2) := by
        rw [nat_eq_iff_cast fmul_lt fmul_lt] at h4; fp_push at h4; simpa using h4
      rw [ite_eq_right h4, ite_eq_right h4']
      exact toJ_inf
  · have h3' : ¬p.toJ 0 * (q.toJ 2 * q.toJ 2) = q.toJ 0 * (p.toJ 2 * p.toJ 2) := by
      rw [nat_eq_iff_cast fmul_lt fmul_lt] at h3; fp_push at h3; simpa using h3
    rw [ite_eq_right h3, ite_eq_right h3']
    funext i
    fin_cases i <;> simp only [toJ, Jac.addF] <;> fp_push <;> simp <;> ring

theorem reduced_addA (hp : p.Reduced) {q : G1A} (hq : q.x < P ∧ q.y < P) :
    (p.addA q).Reduced := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy'⟩ := hq
  unfold addA
  split
  · exact ⟨hx', hy', show 1 < P by decide⟩
  dsimp only
  split
  · split
    · exact reduced_dbl ⟨hx, hy, hz⟩
    · exact reduced_inf
  · exact ⟨by fp_lt, by fp_lt, by fp_lt⟩

theorem toJ_addA (hp : p.Reduced) {q : G1A} (hq : q.x < P ∧ q.y < P) :
    (p.addA q).toJ = Jac.addA p.toJ (q.x : GFp) q.y := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy'⟩ := hq
  unfold addA Jac.addA
  by_cases h1 : p.z = 0
  · rw [ite_eq_left h1, ite_eq_left (show p.toJ 2 = 0 by simp [h1])]
    funext i; fin_cases i <;> simp [toJ, ofAffine]
  have h1' : ¬p.toJ 2 = 0 := by rw [toJ_2, cast_eq_zero hz]; exact h1
  rw [ite_eq_right h1, ite_eq_right h1']
  dsimp only
  by_cases h3 : p.x = fmul q.x (fsqr p.z)
  · have h3' : p.toJ 0 = (q.x : GFp) * (p.toJ 2 * p.toJ 2) := by
      rw [nat_eq_iff_cast hx fmul_lt] at h3; fp_push at h3; simpa using h3
    rw [ite_eq_left h3, ite_eq_left h3']
    by_cases h4 : p.y = fmul (fmul q.y p.z) (fsqr p.z)
    · have h4' : p.toJ 1 = (q.y : GFp) * p.toJ 2 * (p.toJ 2 * p.toJ 2) := by
        rw [nat_eq_iff_cast hy fmul_lt] at h4; fp_push at h4; simpa using h4
      rw [ite_eq_left h4, ite_eq_left h4']
      exact toJ_dbl ⟨hx, hy, hz⟩
    · have h4' : ¬p.toJ 1 = (q.y : GFp) * p.toJ 2 * (p.toJ 2 * p.toJ 2) := by
        rw [nat_eq_iff_cast hy fmul_lt] at h4; fp_push at h4; simpa using h4
      rw [ite_eq_right h4, ite_eq_right h4']
      exact toJ_inf
  · have h3' : ¬p.toJ 0 = (q.x : GFp) * (p.toJ 2 * p.toJ 2) := by
      rw [nat_eq_iff_cast hx fmul_lt] at h3; fp_push at h3; simpa using h3
    rw [ite_eq_right h3, ite_eq_right h3']
    funext i
    fin_cases i <;> simp only [toJ] <;> fp_push <;> simp <;> ring

/-- A `for` loop in `Id` whose body yields one of two values is a fold. -/
theorem forIn_ite_yield {α β : Type} (l : List α) (init : β) (c : α → Prop) [DecidablePred c]
    (f g : α → β → β) :
    (forIn (m := Id) l init fun a b =>
        if c a then pure (ForInStep.yield (f a b)) else pure (ForInStep.yield (g a b))) =
      pure (l.foldl (fun b a => if c a then f a b else g a b) init) := by
  have : (fun a b => if c a then (pure (ForInStep.yield (f a b)) : Id (ForInStep β))
      else pure (ForInStep.yield (g a b))) =
      fun a b => pure (ForInStep.yield (if c a then f a b else g a b)) := by
    funext a b; split <;> rfl
  rw [this, List.forIn_pure_yield_eq_foldl]

/-- A fold of reduced values read through `toJ` is the fold of the read steps. -/
theorem foldl_toJ {β : Type} (f : G1J → β → G1J) (g : (Fin 3 → GFp) → β → Fin 3 → GFp)
    (hf : ∀ a i, a.Reduced → (f a i).Reduced) (hg : ∀ a i, a.Reduced → (f a i).toJ = g a.toJ i) :
    ∀ (l : List β) (a : G1J), a.Reduced →
      (l.foldl f a).Reduced ∧ (l.foldl f a).toJ = l.foldl g a.toJ := by
  intro l
  induction l with
  | nil => intro a ha; exact ⟨ha, rfl⟩
  | cons i l ih =>
    intro a ha
    rw [List.foldl_cons, List.foldl_cons, ← hg a i ha]
    exact ih _ (hf a i ha)

/-- The runtime's double-and-add from the top bit, with mixed additions, is `Jac.mulA`. -/
theorem toJ_mulA {q : G1A} (hq : q.x < P ∧ q.y < P) (k : ℕ) :
    (mulA q k).Reduced ∧ (mulA q k).toJ = Jac.mulA (q.x : GFp) q.y k := by
  unfold mulA Jac.mulA
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_ite_yield, ← List.range_eq_range']
  show (List.foldl _ inf _).Reduced ∧ (List.foldl _ inf _).toJ = _
  have := foldl_toJ (fun b i => if k >>> (k.log2 - i) % 2 = 1 then b.dbl.addA q else b.dbl)
    (Jac.mulStep (q.x : GFp) q.y k (k.log2 + 1))
    (fun a i ha => by
      split
      · exact reduced_addA (reduced_dbl ha) hq
      · exact reduced_dbl ha)
    (fun a i ha => by
      unfold Jac.mulStep
      rw [show k.log2 + 1 - 1 - i = k.log2 - i by omega]
      split
      · rw [toJ_addA (reduced_dbl ha) hq, toJ_dbl ha]
      · rw [toJ_dbl ha])
    (List.range (k.log2 + 1)) inf reduced_inf
  rw [toJ_inf] at this
  exact this

/-- `isInf` is `Z = 0`. -/
theorem isInf_iff : p.isInf = true ↔ p.z = 0 := by simp [isInf]

/-- For a nonsingular reduced triple, `isInf` is the identity. -/
theorem isInf_iff_zero (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    p.isInf = true ↔ Point.toAffine E1 p.toJ = 0 := by
  rw [isInf_iff]
  constructor
  · intro h; exact Point.toAffine_of_Z_eq_zero (by simp [h])
  · intro h
    by_contra hz
    have hz' : p.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hp.2.2]; exact hz
    rw [Point.toAffine_of_Z_ne_zero hn hz'] at h
    exact Affine.Point.some_ne_zero _ h

end G1J

namespace G1A

/-- The triple `(x, y, 1)` of a runtime affine point. -/
def toJ (p : G1A) : Fin 3 → GFp := ![(p.x : GFp), p.y, 1]

/-- Both coordinates below `P`. -/
def Reduced (p : G1A) : Prop := p.x < P ∧ p.y < P

theorem toJ_ofAffine (p : G1A) : (G1J.ofAffine p).toJ = p.toJ := by
  funext i; fin_cases i <;> simp [G1J.toJ, G1J.ofAffine, toJ]

/-- `onCurve` is `E`'s equation, which makes the point nonsingular. -/
theorem onCurve_iff (p : G1A) : p.onCurve = true ↔ E1.Nonsingular p.toJ := by
  rw [toJ, E1_nonsingular_iff, onCurve, decide_eq_true_iff,
    nat_eq_iff_cast fsqr_lt (fadd_lt fmul_lt (by decide))]
  fp_push
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- KeyValidate's subgroup check: `[r]P = O`. -/
theorem inSubgroup_iff {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    p.inSubgroup = true ↔ R • Point.toAffine E1 p.toJ = 0 := by
  obtain ⟨hr, hj⟩ := G1J.toJ_mulA hp R
  obtain ⟨hn', ha'⟩ := Jac.mulA_spec 4 two_ne_zero_GFp hn R
  rw [inSubgroup, G1J.isInf_iff_zero hr (by rw [hj]; exact hn'), hj, ha']; rfl

end G1A

namespace G1J

/-- `toAffine?` is `none` exactly on the identity, and otherwise gives a reduced affine point
standing for the same point. -/
theorem toAffine?_spec {p : G1J} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    match p.toAffine? with
    | none => p.z = 0
    | some a => a.Reduced ∧ E1.Nonsingular a.toJ ∧
        Point.toAffine E1 a.toJ = Point.toAffine E1 p.toJ := by
  unfold toAffine?
  by_cases hz : p.z = 0
  · rw [ite_eq_left hz]; exact hz
  rw [ite_eq_right hz]
  dsimp only
  have hz' : p.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hp.2.2]; exact hz
  have ha := (nonsingular_of_Z_ne_zero hz').mp hn
  have hx : ((fmul p.x (fsqr (finv p.z)) : ℕ) : GFp) = p.toJ 0 / p.toJ 2 ^ 2 := by
    rw [cast_fmul, cast_fsqr, cast_finv, toJ_0, toJ_2, div_eq_mul_inv, ← inv_pow, sq]
  have hy : ((fmul p.y (fmul (fsqr (finv p.z)) (finv p.z)) : ℕ) : GFp) =
      p.toJ 1 / p.toJ 2 ^ 3 := by
    rw [cast_fmul, cast_fmul, cast_fsqr, cast_finv, toJ_1, toJ_2, div_eq_mul_inv, ← inv_pow,
      pow_succ, sq]
  have e : G1A.toJ ⟨fmul p.x (fsqr (finv p.z)), fmul p.y (fmul (fsqr (finv p.z)) (finv p.z))⟩ =
      ![p.toJ 0 / p.toJ 2 ^ 2, p.toJ 1 / p.toJ 2 ^ 3, 1] := by
    funext i; fin_cases i <;> simp [G1A.toJ, hx, hy]
  have hna : E1.Nonsingular ![p.toJ 0 / p.toJ 2 ^ 2, p.toJ 1 / p.toJ 2 ^ 3, 1] := by
    rw [nonsingular_some]; exact ha
  refine ⟨⟨fmul_lt, fmul_lt⟩, by rw [e]; exact hna, ?_⟩
  rw [e, Point.toAffine_some hna, Point.toAffine_of_Z_ne_zero hn hz']

end G1J

/-- G1's generator is on `E`. -/
theorem g1Gen_onCurve : g1Gen.onCurve = true := by decide

theorem g1Gen_reduced : g1Gen.Reduced := ⟨by decide, by decide⟩

theorem g1Gen_nonsingular : E1.Nonsingular g1Gen.toJ :=
  (G1A.onCurve_iff g1Gen).mp g1Gen_onCurve

/-- `[r]G = O` for G1's generator, by the kernel running `G1J.mulA`. -/
theorem g1Gen_inSubgroup : g1Gen.inSubgroup = true := by decide +kernel

/-- G1's generator has order `r`. -/
theorem g1Gen_order : addOrderOf (Point.toAffine E1 g1Gen.toJ) = R := by
  apply addOrderOf_eq_prime
  · exact (G1A.inSubgroup_iff g1Gen_reduced g1Gen_nonsingular).mp g1Gen_inSubgroup
  · rw [show g1Gen.toJ = ![(g1Gen.x : GFp), g1Gen.y, 1] from rfl,
      Point.toAffine_some g1Gen_nonsingular]
    exact Affine.Point.some_ne_zero _

/-! ## G2 -/

/-- `4(1 + u)`, the twist's `b`, in `𝔽_{p²}`. -/
theorem toGF_bTwist : bTwist.toGF = ⟨4, 4⟩ := by ext <;> simp [bTwist, Fp2.toGF]

/-- `E': y² = x³ + 4(1 + u)` over `𝔽_{p²}`, in Jacobian coordinates. -/
abbrev E2 : WeierstrassCurve.Jacobian GFp2 := Jac.J ⟨4, 4⟩

/-- On `E'`, the curve's equation makes a point nonsingular: `E'`'s discriminant is not zero. -/
theorem E2_nonsingular_iff {x y : GFp2} : E2.Nonsingular ![x, y, 1] ↔ y ^ 2 = x ^ 3 + ⟨4, 4⟩ := by
  rw [nonsingular_some, ← Affine.equation_iff_nonsingular_of_Δ_ne_zero, Affine.equation_iff]
  · constructor <;> intro h <;> linear_combination h
  · show (-27 * (4 * (⟨4, 4⟩ : GFp2)) ^ 2 : GFp2) ≠ 0
    intro h
    have := congrArg QuadraticAlgebra.im h
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_zero] at this
    norm_num [sq, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] at this
    rw [show (13824 : GFp) = ((13824 : ℕ) : GFp) by norm_num, cast_eq_zero (by decide)] at this
    exact absurd this (by decide)

/-- No point of `E'` has `y = 0`: `x³ = −4(1 + u)` would make the norm `32` a cube, and so 2. -/
theorem E2_y_ne_zero {x y : GFp2} (h : y ^ 2 = x ^ 3 + ⟨4, 4⟩) : y ≠ 0 := by
  rintro rfl
  have hx : x ^ 3 = -⟨4, 4⟩ := by linear_combination -h
  have hn : (QuadraticAlgebra.norm x) ^ 3 = 32 := by
    rw [← map_pow, hx, QuadraticAlgebra.norm_def]; norm_num
  apply two_not_cube ((QuadraticAlgebra.norm x) ^ 2 * 8⁻¹)
  have h8 : (8 : GFp) ≠ 0 := by
    rw [show (8 : GFp) = ((8 : ℕ) : GFp) by norm_num, Ne, cast_eq_zero (by decide)]; decide
  rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hn, inv_pow]
  field_simp
  norm_num

namespace G2J

/-- The triple of `𝔽_{p²}` a runtime `G2J` stands for. -/
noncomputable def toJ (p : G2J) : Fin 3 → GFp2 := ![p.x.toGF, p.y.toGF, p.z.toGF]

/-- Every coordinate reduced. -/
def Reduced (p : G2J) : Prop := p.x.Reduced ∧ p.y.Reduced ∧ p.z.Reduced

@[simp] theorem toJ_0 (p : G2J) : p.toJ 0 = p.x.toGF := rfl
@[simp] theorem toJ_1 (p : G2J) : p.toJ 1 = p.y.toGF := rfl
@[simp] theorem toJ_2 (p : G2J) : p.toJ 2 = p.z.toGF := rfl

variable {p q : G2J}

theorem toJ_inf : inf.toJ = Jac.inf := by
  funext i; fin_cases i <;> simp [toJ, inf, Jac.inf]

theorem reduced_inf : inf.Reduced := ⟨Fp2.reduced_one, Fp2.reduced_one, Fp2.reduced_zero⟩

theorem reduced_dbl (hp : p.Reduced) : p.dbl.Reduced := by
  obtain ⟨hx, hy, hz⟩ := hp
  unfold dbl
  split
  · exact ⟨hx, hy, hz⟩
  · exact ⟨by fp2_reduced, by fp2_reduced, by fp2_reduced⟩

theorem toJ_dbl (hp : p.Reduced) : p.dbl.toJ = Jac.dbl p.toJ := by
  obtain ⟨hx, hy, hz⟩ := hp
  unfold dbl Jac.dbl
  by_cases h : p.z.isZero = true
  · rw [ite_eq_left h, ite_eq_left (show p.toJ 2 = 0 from (Fp2.isZero_iff hz).mp h)]
  have h' : ¬p.toJ 2 = 0 := fun e => h ((Fp2.isZero_iff hz).mpr e)
  rw [ite_eq_right h, ite_eq_right h']
  funext i
  fin_cases i <;> simp only [toJ, Jac.dblF] <;> fp2_push <;> simp <;> ring

theorem reduced_add (hp : p.Reduced) (hq : q.Reduced) : (p.add q).Reduced := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy', hz'⟩ := hq
  unfold add
  split
  · exact ⟨hx', hy', hz'⟩
  split
  · exact ⟨hx, hy, hz⟩
  dsimp only
  split
  · split
    · exact reduced_dbl ⟨hx, hy, hz⟩
    · exact reduced_inf
  · exact ⟨by fp2_reduced, by fp2_reduced, by fp2_reduced⟩

theorem toJ_add (hp : p.Reduced) (hq : q.Reduced) : (p.add q).toJ = Jac.add p.toJ q.toJ := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy', hz'⟩ := hq
  unfold add Jac.add
  by_cases h1 : p.z.isZero = true
  · rw [ite_eq_left h1, ite_eq_left (show p.toJ 2 = 0 from (Fp2.isZero_iff hz).mp h1)]
  have h1' : ¬p.toJ 2 = 0 := fun e => h1 ((Fp2.isZero_iff hz).mpr e)
  rw [ite_eq_right h1, ite_eq_right h1']
  by_cases h2 : q.z.isZero = true
  · rw [ite_eq_left h2, ite_eq_left (show q.toJ 2 = 0 from (Fp2.isZero_iff hz').mp h2)]
  have h2' : ¬q.toJ 2 = 0 := fun e => h2 ((Fp2.isZero_iff hz').mpr e)
  rw [ite_eq_right h2, ite_eq_right h2']
  dsimp only
  have hu : (p.x.mul q.z.sqr).eq (q.x.mul p.z.sqr) = true ↔
      p.toJ 0 * (q.toJ 2 * q.toJ 2) = q.toJ 0 * (p.toJ 2 * p.toJ 2) := by
    rw [Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul]; fp2_push; simp
  have hs : ((p.y.mul q.z).mul q.z.sqr).eq ((q.y.mul p.z).mul p.z.sqr) = true ↔
      p.toJ 1 * q.toJ 2 * (q.toJ 2 * q.toJ 2) = q.toJ 1 * p.toJ 2 * (p.toJ 2 * p.toJ 2) := by
    rw [Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul]; fp2_push; simp
  by_cases h3 : (p.x.mul q.z.sqr).eq (q.x.mul p.z.sqr) = true
  · rw [ite_eq_left h3, ite_eq_left (hu.mp h3)]
    by_cases h4 : ((p.y.mul q.z).mul q.z.sqr).eq ((q.y.mul p.z).mul p.z.sqr) = true
    · rw [ite_eq_left h4, ite_eq_left (hs.mp h4)]
      exact toJ_dbl ⟨hx, hy, hz⟩
    · rw [ite_eq_right h4, ite_eq_right (fun e => h4 (hs.mpr e))]
      exact toJ_inf
  · rw [ite_eq_right h3, ite_eq_right (fun e => h3 (hu.mpr e))]
    funext i
    fin_cases i <;> simp only [toJ, Jac.addF] <;> fp2_push <;> simp <;> ring

theorem reduced_addA (hp : p.Reduced) {q : G2A} (hq : q.x.Reduced ∧ q.y.Reduced) :
    (p.addA q).Reduced := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy'⟩ := hq
  unfold addA
  split
  · exact ⟨hx', hy', Fp2.reduced_one⟩
  dsimp only
  split
  · split
    · exact reduced_dbl ⟨hx, hy, hz⟩
    · exact reduced_inf
  · exact ⟨by fp2_reduced, by fp2_reduced, by fp2_reduced⟩

theorem toJ_addA (hp : p.Reduced) {q : G2A} (hq : q.x.Reduced ∧ q.y.Reduced) :
    (p.addA q).toJ = Jac.addA p.toJ q.x.toGF q.y.toGF := by
  obtain ⟨hx, hy, hz⟩ := hp; obtain ⟨hx', hy'⟩ := hq
  unfold addA Jac.addA
  by_cases h1 : p.z.isZero = true
  · rw [ite_eq_left h1, ite_eq_left (show p.toJ 2 = 0 from (Fp2.isZero_iff hz).mp h1)]
    funext i; fin_cases i <;> simp [toJ, ofAffine]
  have h1' : ¬p.toJ 2 = 0 := fun e => h1 ((Fp2.isZero_iff hz).mpr e)
  rw [ite_eq_right h1, ite_eq_right h1']
  dsimp only
  have hu : p.x.eq (q.x.mul p.z.sqr) = true ↔ p.toJ 0 = q.x.toGF * (p.toJ 2 * p.toJ 2) := by
    rw [Fp2.eq_iff hx Fp2.reduced_mul]; fp2_push; simp
  have hs : p.y.eq ((q.y.mul p.z).mul p.z.sqr) = true ↔
      p.toJ 1 = q.y.toGF * p.toJ 2 * (p.toJ 2 * p.toJ 2) := by
    rw [Fp2.eq_iff hy Fp2.reduced_mul]; fp2_push; simp
  by_cases h3 : p.x.eq (q.x.mul p.z.sqr) = true
  · rw [ite_eq_left h3, ite_eq_left (hu.mp h3)]
    by_cases h4 : p.y.eq ((q.y.mul p.z).mul p.z.sqr) = true
    · rw [ite_eq_left h4, ite_eq_left (hs.mp h4)]
      exact toJ_dbl ⟨hx, hy, hz⟩
    · rw [ite_eq_right h4, ite_eq_right (fun e => h4 (hs.mpr e))]
      exact toJ_inf
  · rw [ite_eq_right h3, ite_eq_right (fun e => h3 (hu.mpr e))]
    funext i
    fin_cases i <;> simp only [toJ] <;> fp2_push <;> simp <;> ring

/-- A fold of reduced values read through `toJ` is the fold of the read steps. -/
theorem foldl_toJ {β : Type} (f : G2J → β → G2J) (g : (Fin 3 → GFp2) → β → Fin 3 → GFp2)
    (hf : ∀ a i, a.Reduced → (f a i).Reduced) (hg : ∀ a i, a.Reduced → (f a i).toJ = g a.toJ i) :
    ∀ (l : List β) (a : G2J), a.Reduced →
      (l.foldl f a).Reduced ∧ (l.foldl f a).toJ = l.foldl g a.toJ := by
  intro l
  induction l with
  | nil => intro a ha; exact ⟨ha, rfl⟩
  | cons i l ih =>
    intro a ha
    rw [List.foldl_cons, List.foldl_cons, ← hg a i ha]
    exact ih _ (hf a i ha)

/-- The runtime's double-and-add from the top bit, with mixed additions, is `Jac.mulA`. -/
theorem toJ_mulA {q : G2A} (hq : q.x.Reduced ∧ q.y.Reduced) (k : ℕ) :
    (mulA q k).Reduced ∧ (mulA q k).toJ = Jac.mulA q.x.toGF q.y.toGF k := by
  unfold mulA Jac.mulA
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [G1J.forIn_ite_yield, ← List.range_eq_range']
  have := foldl_toJ (fun b i => if k >>> (k.log2 - i) % 2 = 1 then b.dbl.addA q else b.dbl)
    (Jac.mulStep q.x.toGF q.y.toGF k (k.log2 + 1))
    (fun a i ha => by
      split
      · exact reduced_addA (reduced_dbl ha) hq
      · exact reduced_dbl ha)
    (fun a i ha => by
      unfold Jac.mulStep
      rw [show k.log2 + 1 - 1 - i = k.log2 - i by omega]
      split
      · rw [toJ_addA (reduced_dbl ha) hq, toJ_dbl ha]
      · rw [toJ_dbl ha])
    (List.range (k.log2 + 1)) inf reduced_inf
  rw [toJ_inf] at this
  exact this

/-- `isInf` is `Z = 0`. -/
theorem isInf_iff (hp : p.Reduced) : p.isInf = true ↔ p.toJ 2 = 0 := Fp2.isZero_iff hp.2.2

/-- For a nonsingular reduced triple, `isInf` is the identity. -/
theorem isInf_iff_zero (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.isInf = true ↔ Point.toAffine E2 p.toJ = 0 := by
  rw [isInf_iff hp]
  constructor
  · intro h; exact Point.toAffine_of_Z_eq_zero h
  · intro h
    by_contra hz
    rw [Point.toAffine_of_Z_ne_zero hn hz] at h
    exact Affine.Point.some_ne_zero _ h

end G2J

namespace G2A

/-- The triple `(x, y, 1)` of a runtime affine point. -/
noncomputable def toJ (p : G2A) : Fin 3 → GFp2 := ![p.x.toGF, p.y.toGF, 1]

/-- Both coordinates reduced. -/
def Reduced (p : G2A) : Prop := p.x.Reduced ∧ p.y.Reduced

/-- `onCurve` is `E'`'s equation, which makes the point nonsingular. -/
theorem onCurve_iff {p : G2A} (hp : p.Reduced) : p.onCurve = true ↔ E2.Nonsingular p.toJ := by
  rw [toJ, E2_nonsingular_iff, onCurve, Fp2.eq_iff Fp2.reduced_sqr (Fp2.reduced_add
    Fp2.reduced_mul ⟨by decide, by decide⟩), Fp2.toGF_add, Fp2.toGF_sqr hp.2,
    Fp2.toGF_mul Fp2.reduced_sqr hp.1, Fp2.toGF_sqr hp.1, toGF_bTwist]
  constructor <;> intro h <;> linear_combination h

/-- The signature's subgroup check: `[r]Q = O`. -/
theorem inSubgroup_iff {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.inSubgroup = true ↔ R • Point.toAffine E2 p.toJ = 0 := by
  obtain ⟨hr, hj⟩ := G2J.toJ_mulA hp R
  obtain ⟨hn', ha'⟩ := Jac.mulA_spec (⟨4, 4⟩ : GFp2) two_ne_zero_GFp2 hn R
  have hn'' : E2.Nonsingular (G2J.mulA p R).toJ := by rw [hj]; exact hn'
  rw [inSubgroup, G2J.isInf_iff_zero hr hn'', hj]
  exact ⟨fun h => ha' ▸ h, fun h => ha'.symm ▸ h⟩

end G2A

namespace G2J

/-- `toAffine?` is `none` exactly on the identity, and otherwise gives a reduced affine point
standing for the same point. -/
theorem toAffine?_spec {p : G2J} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    match p.toAffine? with
    | none => p.toJ 2 = 0
    | some a => a.Reduced ∧ E2.Nonsingular a.toJ ∧
        Point.toAffine E2 a.toJ = Point.toAffine E2 p.toJ := by
  obtain ⟨hx, hy, hz⟩ := hp
  unfold toAffine?
  by_cases h : p.z.isZero = true
  · rw [ite_eq_left h]; exact (Fp2.isZero_iff hz).mp h
  rw [ite_eq_right h]
  dsimp only
  have hz' : p.toJ 2 ≠ 0 := fun e => h ((Fp2.isZero_iff hz).mpr e)
  have ha := (nonsingular_of_Z_ne_zero hz').mp hn
  have hx1 : (p.x.mul p.z.inv.sqr).toGF = p.toJ 0 / p.toJ 2 ^ 2 := by
    fp2_push; rw [toJ_0, toJ_2, div_eq_mul_inv, ← inv_pow, sq]
  have hy1 : (p.y.mul (p.z.inv.sqr.mul p.z.inv)).toGF = p.toJ 1 / p.toJ 2 ^ 3 := by
    fp2_push; rw [toJ_1, toJ_2, div_eq_mul_inv, ← inv_pow, pow_succ, sq]
  have e : G2A.toJ ⟨p.x.mul p.z.inv.sqr, p.y.mul (p.z.inv.sqr.mul p.z.inv)⟩ =
      ![p.toJ 0 / p.toJ 2 ^ 2, p.toJ 1 / p.toJ 2 ^ 3, 1] := by
    funext i; fin_cases i <;> simp [G2A.toJ, hx1, hy1]
  have hna : E2.Nonsingular ![p.toJ 0 / p.toJ 2 ^ 2, p.toJ 1 / p.toJ 2 ^ 3, 1] := by
    rw [nonsingular_some]; exact ha
  refine ⟨⟨Fp2.reduced_mul, Fp2.reduced_mul⟩, by rw [e]; exact hna, ?_⟩
  rw [e, Point.toAffine_some hna, Point.toAffine_of_Z_ne_zero hn hz']

end G2J

/-- G2's generator is on `E'`. -/
theorem g2Gen_onCurve : g2Gen.onCurve = true := by decide

theorem g2Gen_reduced : g2Gen.Reduced := ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem g2Gen_nonsingular : E2.Nonsingular g2Gen.toJ :=
  (G2A.onCurve_iff g2Gen_reduced).mp g2Gen_onCurve

/-- `[r]G = O` for G2's generator, by the kernel running `G2J.mulA`. -/
theorem g2Gen_inSubgroup : g2Gen.inSubgroup = true := by decide +kernel

/-- G2's generator has order `r`. -/
theorem g2Gen_order : addOrderOf (Point.toAffine E2 g2Gen.toJ) = R := by
  apply addOrderOf_eq_prime
  · exact (G2A.inSubgroup_iff g2Gen_reduced g2Gen_nonsingular).mp g2Gen_inSubgroup
  · rw [show g2Gen.toJ = ![g2Gen.x.toGF, g2Gen.y.toGF, 1] from rfl,
      Point.toAffine_some g2Gen_nonsingular]
    exact Affine.Point.some_ne_zero _

/-! ## The group law, in the domain's terms -/

/-- G1's runtime addition of two reduced points on `E` is the group law. -/
theorem G1J.add_spec {p q : G1J} (hp : p.Reduced) (hq : q.Reduced) (hpn : E1.Nonsingular p.toJ)
    (hqn : E1.Nonsingular q.toJ) :
    (p.add q).Reduced ∧ E1.Nonsingular (p.add q).toJ ∧
      Point.toAffine E1 (p.add q).toJ = Point.toAffine E1 p.toJ + Point.toAffine E1 q.toJ := by
  rw [G1J.toJ_add hp hq]
  exact ⟨G1J.reduced_add hp hq, Jac.add_spec 4 two_ne_zero_GFp hpn hqn⟩

/-- G1's runtime doubling of a reduced point on `E` is the group law's. -/
theorem G1J.dbl_spec {p : G1J} (hp : p.Reduced) (hpn : E1.Nonsingular p.toJ) :
    p.dbl.Reduced ∧ E1.Nonsingular p.dbl.toJ ∧
      Point.toAffine E1 p.dbl.toJ = 2 • Point.toAffine E1 p.toJ := by
  rw [G1J.toJ_dbl hp]
  exact ⟨G1J.reduced_dbl hp, Jac.dbl_spec 4 hpn⟩

/-- G1's runtime mixed addition of a reduced affine point on `E` is the group law. -/
theorem G1J.addA_spec {p : G1J} {q : G1A} (hp : p.Reduced) (hq : q.Reduced)
    (hpn : E1.Nonsingular p.toJ) (hqn : E1.Nonsingular q.toJ) :
    (p.addA q).Reduced ∧ E1.Nonsingular (p.addA q).toJ ∧
      Point.toAffine E1 (p.addA q).toJ = Point.toAffine E1 p.toJ + Point.toAffine E1 q.toJ := by
  rw [G1J.toJ_addA hp hq]
  exact ⟨G1J.reduced_addA hp hq, Jac.addA_spec 4 two_ne_zero_GFp hpn hqn⟩

/-- G1's runtime double-and-add `[k]q`, for a reduced affine point on `E`, is `k • q`. -/
theorem G1J.mulA_spec {q : G1A} (hq : q.Reduced) (hqn : E1.Nonsingular q.toJ) (k : ℕ) :
    (G1J.mulA q k).Reduced ∧ E1.Nonsingular (G1J.mulA q k).toJ ∧
      Point.toAffine E1 (G1J.mulA q k).toJ = k • Point.toAffine E1 q.toJ := by
  obtain ⟨hr, hj⟩ := G1J.toJ_mulA hq k
  rw [hj]
  exact ⟨hr, Jac.mulA_spec 4 two_ne_zero_GFp hqn k⟩

/-- G2's runtime addition of two reduced points on `E'` is the group law. -/
theorem G2J.add_spec {p q : G2J} (hp : p.Reduced) (hq : q.Reduced) (hpn : E2.Nonsingular p.toJ)
    (hqn : E2.Nonsingular q.toJ) :
    (p.add q).Reduced ∧ E2.Nonsingular (p.add q).toJ ∧
      Point.toAffine E2 (p.add q).toJ = Point.toAffine E2 p.toJ + Point.toAffine E2 q.toJ := by
  rw [G2J.toJ_add hp hq]
  exact ⟨G2J.reduced_add hp hq, Jac.add_spec _ two_ne_zero_GFp2 hpn hqn⟩

/-- G2's runtime doubling of a reduced point on `E'` is the group law's. -/
theorem G2J.dbl_spec {p : G2J} (hp : p.Reduced) (hpn : E2.Nonsingular p.toJ) :
    p.dbl.Reduced ∧ E2.Nonsingular p.dbl.toJ ∧
      Point.toAffine E2 p.dbl.toJ = 2 • Point.toAffine E2 p.toJ := by
  rw [G2J.toJ_dbl hp]
  exact ⟨G2J.reduced_dbl hp, Jac.dbl_spec _ hpn⟩

/-- G2's runtime mixed addition of a reduced affine point on `E'` is the group law. -/
theorem G2J.addA_spec {p : G2J} {q : G2A} (hp : p.Reduced) (hq : q.Reduced)
    (hpn : E2.Nonsingular p.toJ) (hqn : E2.Nonsingular q.toJ) :
    (p.addA q).Reduced ∧ E2.Nonsingular (p.addA q).toJ ∧
      Point.toAffine E2 (p.addA q).toJ = Point.toAffine E2 p.toJ + Point.toAffine E2 q.toJ := by
  rw [G2J.toJ_addA hp hq]
  exact ⟨G2J.reduced_addA hp hq, Jac.addA_spec _ two_ne_zero_GFp2 hpn hqn⟩

/-- G2's runtime double-and-add `[k]q`, for a reduced affine point on `E'`, is `k • q`. -/
theorem G2J.mulA_spec {q : G2A} (hq : q.Reduced) (hqn : E2.Nonsingular q.toJ) (k : ℕ) :
    (G2J.mulA q k).Reduced ∧ E2.Nonsingular (G2J.mulA q k).toJ ∧
      Point.toAffine E2 (G2J.mulA q k).toJ = k • Point.toAffine E2 q.toJ := by
  obtain ⟨hr, hj⟩ := G2J.toJ_mulA hq k
  rw [hj]
  exact ⟨hr, Jac.mulA_spec _ two_ne_zero_GFp2 hqn k⟩

end LeanLight.Lc.Bls
