import LeanLightProofs.Bls.Fav
import LeanLightProofs.Bls.PointCount
import LeanLightProofs.Bls.ValueEq
import LeanLight.Bls.HashToG2

/-!
# BLS12-381: what `hash_to_G2` returns is a point of `E'` (25c, `HashOnCurve`)

`LeanLight.Bls.H2C.hashToG2?` returns, on any message and DST, a reduced point of the twist
`E': y² = x³ + 4(1 + u)` (`hashOnCurve`, which discharges `HashOnCurve`, a hypothesis of
`fastAggregateVerify_iff`), and that point is in G2 (`hashInG2`, which discharges `HashInG2`:
`[h_eff]` maps every point of `E'(𝔽_{p²})` into G2, `hEff_smul_mem_G2`, from the group's order
`#E'(𝔽_{p²}) = r·h₂`, `LeanLightProofs.Bls.PointCount`). The proof of `hashOnCurve` is
structural: no SHA-256 output, square root or point is computed, so the kernel never evaluates
them on symbolic arguments.

* **SSWU** (`sswu?_some`): a point `sswu?` returns lies on SSWU's curve
  `E'': y² = x³ + A'x + B'` (`OnIso`), since `y` is a root `Fp2.sqrt?` returned of `g(x)` and
  `sgn0`'s choice of sign does not change `y²`.
* **The 3-isogeny** (`isoMap_good`): `isoMap` sends a point of `E''` to a triple on `E'`, the
  identity's (`Z = 0`) when a denominator vanishes. On `E''`,
  `Y² − X³ − b'Z⁶ = x_den³·y_den⁴·(g·y_num²·x_den³ − x_num³·y_den² − b'·x_den³·y_den²)` with
  `g = x³ + A'x + B'`, and that last polynomial of degree 15 is zero: its coefficients, computed
  from RFC 9380 E.3's constants by a small polynomial arithmetic on runtime `Fp2` values
  (`Poly`), are zero, by the kernel (`iso_identity`). That is RFC 9380's mathematics for these
  constants, checked, not assumed.
* **The sum and `clear_cofactor`** (`G2J.add_good`, `clearCofactor_spec`): the runtime's addition
  of two such triples is the group law (the identity's triple, whatever its `X` and `Y`, gives
  the other operand), and `clear_cofactor` is `[h_eff]P`, a nonsingular reduced triple.
* `toAffine?` of a nonsingular reduced triple is a reduced point of `E'` (`G2J.toAffine?_spec`).

`hashToG2?`, `sswu?` and `clearCofactor` are unfolded through their unapplied values
(`value_eq`, `LeanLightProofs.Bls.ValueEq`) and their matches rewritten to `if` and `Option.elim`
(`hashToG2?_eq` and the like): their equation lemmas, or reducing their matches in place, would
have the kernel evaluate SHA-256 and `Nat.powMod` on symbolic arguments.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

local notation "aff2" => Point.toAffine E2

/-! ## Polynomials over `𝔽_{p²}` with runtime coefficients -/

namespace Poly

/-- `Σ cᵢ·xⁱ` in `𝔽_{p²}`, the coefficients runtime `Fp2`s, the constant first. -/
noncomputable def eval : List Fp2 → GFp2 → GFp2
  | [], _ => 0
  | c :: cs, x => c.toGF + x * eval cs x

/-- Every coefficient reduced. -/
def Red (l : List Fp2) : Prop := ∀ c ∈ l, c.Reduced

/-- The sum of two polynomials, coefficient by coefficient. -/
def add : List Fp2 → List Fp2 → List Fp2
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => a.add b :: add p q

/-- `a·q`. -/
def smul (a : Fp2) (q : List Fp2) : List Fp2 := q.map a.mul

/-- The product of two polynomials, schoolbook. -/
def mul : List Fp2 → List Fp2 → List Fp2
  | [], _ => []
  | a :: p, q => add (smul a q) (Fp2.zero :: mul p q)

theorem eval_add : ∀ (p q : List Fp2) (x : GFp2), eval (add p q) x = eval p x + eval q x
  | [], q, x => by simp [add, eval]
  | a :: p, [], x => by simp [add, eval]
  | a :: p, b :: q, x => by simp only [add, eval, Fp2.toGF_add, eval_add p q x]; ring

theorem red_add : ∀ {p q : List Fp2}, Red p → Red q → Red (add p q)
  | [], q, _, hq => hq
  | a :: p, [], hp, _ => hp
  | a :: p, b :: q, hp, hq => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Fp2.reduced_add (hp a List.mem_cons_self) (hq b List.mem_cons_self)
    · exact red_add (fun c h => hp c (List.mem_cons_of_mem _ h))
        (fun c h => hq c (List.mem_cons_of_mem _ h)) c hc

theorem red_smul (a : Fp2) (q : List Fp2) : Red (smul a q) := by
  intro c hc
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
  exact Fp2.reduced_mul

theorem red_mul : ∀ (p q : List Fp2), Red (mul p q)
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | a :: p, q => by
    refine red_add (red_smul a q) ?_
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Fp2.reduced_zero
    · exact red_mul p q c hc

theorem eval_smul {a : Fp2} (ha : a.Reduced) : ∀ {q : List Fp2}, Red q → ∀ x : GFp2,
    eval (smul a q) x = a.toGF * eval q x
  | [], _, x => by simp [smul, eval]
  | b :: q, hq, x => by
    have := eval_smul ha (q := q) (fun c h => hq c (List.mem_cons_of_mem _ h)) x
    simp only [smul, List.map_cons, eval] at this ⊢
    rw [this, Fp2.toGF_mul ha (hq b List.mem_cons_self)]
    ring

theorem eval_mul : ∀ {p q : List Fp2}, Red p → Red q → ∀ x : GFp2,
    eval (mul p q) x = eval p x * eval q x
  | [], _, _, _, x => by simp [mul, eval]
  | a :: p, q, hp, hq, x => by
    rw [mul, eval_add, eval_smul (hp a List.mem_cons_self) hq, eval, Fp2.toGF_zero,
      eval_mul (fun c h => hp c (List.mem_cons_of_mem _ h)) hq, eval]
    ring

/-- A polynomial whose coefficients are all zero is zero. -/
theorem eval_of_all_isZero : ∀ {l : List Fp2}, Red l → l.all Fp2.isZero = true →
    ∀ x : GFp2, eval l x = 0
  | [], _, _, x => rfl
  | c :: l, hl, h, x => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [eval, (Fp2.isZero_iff (hl c List.mem_cons_self)).mp h.1,
      eval_of_all_isZero (fun c h => hl c (List.mem_cons_of_mem _ h)) h.2 x]
    ring

/-- `−1`. -/
def negOne : Fp2 := ⟨P - 1, 0⟩

theorem toGF_negOne : negOne.toGF = -1 := by
  ext
  · simp [negOne, Fp2.toGF, Nat.cast_sub one_lt_P.le]
  · simp [negOne, Fp2.toGF, QuadraticAlgebra.im_one]

/-- Two polynomials agree wherever `p − q`'s coefficients, computed, are all zero. -/
theorem eval_eq_of_check {p q : List Fp2} (hp : Red p) (hq : Red q)
    (h : (add p (smul negOne q)).all Fp2.isZero = true) (x : GFp2) : eval p x = eval q x := by
  have := eval_of_all_isZero (red_add hp (red_smul _ _)) h x
  rw [eval_add, eval_smul (show negOne.Reduced from ⟨by decide, by decide⟩) hq,
    toGF_negOne] at this
  linear_combination this

end Poly

/-! ## Horner's rule -/

theorem horner_eq_foldl (ks : Array Fp2) (x : Fp2) : H2C.horner ks x =
    (List.range ks.size).foldl
      (fun acc k => (acc.mul x).add (ks[ks.size - 1 - k]?.getD Fp2.zero)) Fp2.zero := by
  unfold H2C.horner
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  rfl

theorem foldl_horner (l : List Fp2) (hl : Poly.Red l) {x : Fp2} (hx : x.Reduced) :
    ∀ m, m ≤ l.length →
      ((List.range m).foldl (fun acc k => (acc.mul x).add (l[l.length - 1 - k]?.getD Fp2.zero))
          Fp2.zero).Reduced ∧
      ((List.range m).foldl (fun acc k => (acc.mul x).add (l[l.length - 1 - k]?.getD Fp2.zero))
          Fp2.zero).toGF = Poly.eval (l.drop (l.length - m)) x.toGF := by
  intro m
  induction m with
  | zero => intro _; simp [Poly.eval, Fp2.reduced_zero]
  | succ m ih =>
    intro hm
    obtain ⟨hr, he⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl _ Fp2.zero = acc at hr he
    have hi : l.length - 1 - m < l.length := by omega
    rw [List.getElem?_eq_getElem hi, Option.getD_some]
    have hc := hl _ (List.getElem_mem hi)
    refine ⟨Fp2.reduced_add Fp2.reduced_mul hc, ?_⟩
    rw [show l.length - (m + 1) = l.length - 1 - m by omega, List.drop_eq_getElem_cons hi,
      Poly.eval, show l.length - 1 - m + 1 = l.length - m by omega, ← he, Fp2.toGF_add,
      Fp2.toGF_mul hr hx]
    ring

/-- The runtime's Horner evaluation is the polynomial's value. -/
theorem horner_spec (ks : Array Fp2) (hk : Poly.Red ks.toList) {x : Fp2} (hx : x.Reduced) :
    (H2C.horner ks x).Reduced ∧ (H2C.horner ks x).toGF = Poly.eval ks.toList x.toGF := by
  rw [horner_eq_foldl]
  have := foldl_horner ks.toList hk hx ks.size (by simp)
  simp only [Array.length_toList, Nat.sub_self, List.drop_zero, Array.getElem?_toList] at this
  exact this

/-! ## The 3-isogeny `E'' → E'` -/

/-- SSWU's curve `E'': y² = x³ + A'x + B'` (RFC 9380 §8.8.2), for an affine runtime point. -/
def OnIso (q : G2A) : Prop :=
  q.y.toGF ^ 2 = q.x.toGF ^ 3 + H2C.sswuA.toGF * q.x.toGF + H2C.sswuB.toGF

/-- `g(x) = x³ + A'x + B'`, the right side of `E''`. -/
def isoG : List Fp2 := [H2C.sswuB, H2C.sswuA, Fp2.zero, Fp2.one]

/-- `g·y_num²·x_den³`, the left side of the isogeny's identity. -/
def isoLhs : List Fp2 :=
  Poly.mul (Poly.mul isoG (Poly.mul H2C.isoYNum.toList H2C.isoYNum.toList))
    (Poly.mul H2C.isoXDen.toList (Poly.mul H2C.isoXDen.toList H2C.isoXDen.toList))

/-- `x_num³·y_den² + b'·x_den³·y_den²`, its right side. -/
def isoRhs : List Fp2 :=
  Poly.add
    (Poly.mul (Poly.mul H2C.isoXNum.toList (Poly.mul H2C.isoXNum.toList H2C.isoXNum.toList))
      (Poly.mul H2C.isoYDen.toList H2C.isoYDen.toList))
    (Poly.mul [bTwist]
      (Poly.mul (Poly.mul H2C.isoXDen.toList (Poly.mul H2C.isoXDen.toList H2C.isoXDen.toList))
        (Poly.mul H2C.isoYDen.toList H2C.isoYDen.toList)))

/-- RFC 9380 E.3's isogeny maps `E''` to `E'`: the coefficients of
`g·y_num²·x_den³ − (x_num³·y_den² + b'·x_den³·y_den²)` are all zero, by the kernel. -/
theorem iso_identity : (Poly.add isoLhs (Poly.smul Poly.negOne isoRhs)).all Fp2.isZero = true := by
  decide +kernel

theorem red_isoXNum : Poly.Red H2C.isoXNum.toList := by
  intro c hc; simp only [H2C.isoXNum, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
theorem red_isoXDen : Poly.Red H2C.isoXDen.toList := by
  intro c hc; simp only [H2C.isoXDen, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
theorem red_isoYNum : Poly.Red H2C.isoYNum.toList := by
  intro c hc; simp only [H2C.isoYNum, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
theorem red_isoYDen : Poly.Red H2C.isoYDen.toList := by
  intro c hc; simp only [H2C.isoYDen, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
theorem red_isoG : Poly.Red isoG := by
  intro c hc; simp only [isoG, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- The isogeny's identity in `𝔽_{p²}`, at any `x`. -/
theorem iso_identity_eval (x : GFp2) :
    Poly.eval isoG x * (Poly.eval H2C.isoYNum.toList x) ^ 2 *
        (Poly.eval H2C.isoXDen.toList x) ^ 3 =
      (Poly.eval H2C.isoXNum.toList x) ^ 3 * (Poly.eval H2C.isoYDen.toList x) ^ 2 +
        bTwist.toGF * (Poly.eval H2C.isoXDen.toList x) ^ 3 *
          (Poly.eval H2C.isoYDen.toList x) ^ 2 := by
  have h := Poly.eval_eq_of_check (Poly.red_mul _ _) (Poly.red_add (Poly.red_mul _ _)
    (Poly.red_mul _ _)) iso_identity x
  have hb : Poly.Red [bTwist] := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨by decide, by decide⟩
  simp only [Poly.eval_add,
    Poly.eval_mul (Poly.red_mul _ _) (Poly.red_mul _ _),
    Poly.eval_mul red_isoG (Poly.red_mul _ _), Poly.eval_mul red_isoYNum red_isoYNum,
    Poly.eval_mul red_isoXDen (Poly.red_mul _ _), Poly.eval_mul red_isoXDen red_isoXDen,
    Poly.eval_mul red_isoXNum (Poly.red_mul _ _), Poly.eval_mul red_isoXNum red_isoXNum,
    Poly.eval_mul red_isoYDen red_isoYDen, Poly.eval_mul hb (Poly.red_mul _ _)] at h
  simp only [Poly.eval, mul_zero, add_zero] at h
  linear_combination h

/-- `g(x)` is `x³ + A'x + B'`. -/
theorem eval_isoG (x : GFp2) :
    Poly.eval isoG x = x ^ 3 + H2C.sswuA.toGF * x + H2C.sswuB.toGF := by
  simp only [isoG, Poly.eval, Fp2.toGF_zero, Fp2.toGF_one]; ring

/-- On `E'`'s equation, a triple with `Z ≠ 0` is nonsingular (`E'` is smooth). -/
theorem E2_nonsingular_of_equation {p : Fin 3 → GFp2} (h : E2.Equation p) (hz : p 2 ≠ 0) :
    E2.Nonsingular p := by
  rw [nonsingular_of_Z_ne_zero hz, ← nonsingular_some, E2_nonsingular_iff]
  rw [equation_of_Z_ne_zero hz, Affine.equation_iff] at h
  linear_combination h

/-- A reduced Jacobian triple standing for a point of `E'`: nonsingular, or `Z = 0`, which the
runtime takes for the identity whatever its `X` and `Y` (`isoMap`'s `(0, 0, 0)` included). -/
def G2J.Good (p : G2J) : Prop := p.Reduced ∧ (p.toJ 2 = 0 ∨ E2.Nonsingular p.toJ)

/-- `isoMap` sends a reduced point of `E''` to a triple on `E'`: the identity's (`Z = 0`) when a
denominator vanishes, a nonsingular one otherwise. -/
theorem isoMap_good {q : G2A} (hq : q.Reduced) (he : OnIso q) : (H2C.isoMap q).Good := by
  obtain ⟨hxn, exn⟩ := horner_spec _ red_isoXNum hq.1
  obtain ⟨hxd, exd⟩ := horner_spec _ red_isoXDen hq.1
  obtain ⟨hyn, eyn⟩ := horner_spec _ red_isoYNum hq.1
  obtain ⟨hyd, eyd⟩ := horner_spec _ red_isoYDen hq.1
  have hred : (H2C.isoMap q).Reduced := ⟨Fp2.reduced_mul, Fp2.reduced_mul, Fp2.reduced_mul⟩
  refine ⟨hred, ?_⟩
  have hx := hq.1
  have hy := hq.2
  have heq : E2.Equation (H2C.isoMap q).toJ := by
    rw [Jac.equation_iff']
    simp only [H2C.isoMap, G2J.toJ_0, G2J.toJ_1, G2J.toJ_2]
    fp2_push
    rw [exn, exd, eyn, eyd]
    have hid := iso_identity_eval q.x.toGF
    rw [eval_isoG, ← he, toGF_bTwist] at hid
    linear_combination
      (Poly.eval H2C.isoXDen.toList q.x.toGF) ^ 3 * (Poly.eval H2C.isoYDen.toList q.x.toGF) ^ 4 *
        hid
  by_cases hz : (H2C.isoMap q).toJ 2 = 0
  · exact Or.inl hz
  · exact Or.inr (E2_nonsingular_of_equation heq hz)

/-! ## SSWU -/

/-- SSWU's `x₁` for `u` (RFC 9380 §6.6.2), as `sswu?` computes it. -/
def sswuX1 (u : Fp2) : Fp2 :=
  if ((H2C.sswuZ.mul u.sqr).sqr.add (H2C.sswuZ.mul u.sqr)).isZero = true then
    H2C.sswuB.mul (H2C.sswuZ.mul H2C.sswuA).inv
  else (H2C.sswuB.neg.mul H2C.sswuA.inv).mul
    (Fp2.one.add ((H2C.sswuZ.mul u.sqr).sqr.add (H2C.sswuZ.mul u.sqr)).inv)

/-- SSWU's `x₂ = Z·u²·x₁`. -/
def sswuX2 (u : Fp2) : Fp2 := (H2C.sswuZ.mul u.sqr).mul (sswuX1 u)

/-- `y` or `−y`, the one whose `sgn0` is `u`'s. -/
def sgnAdj (u y : Fp2) : Fp2 := if (u.sgn0 == y.sgn0) = true then y else y.neg

set_option linter.auxLemma false in
theorem sswu?_match_1 {β : Type} (x : Option Fp2) (n : Unit → β) (f : Fp2 → β) :
    H2C.sswu?.match_1 (fun _ => β) x n f = x.elim (n ()) f := by cases x <;> rfl

set_option linter.auxLemma false in
theorem sswu?_match_3 {β : Type} (x : Fp2 × Fp2) (f : Fp2 → Fp2 → β) :
    H2C.sswu?.match_3 (fun _ => β) x f = f x.1 x.2 := by cases x; rfl

set_option linter.auxLemma false in
/-- The pair match of an `if` of pairs is the `if` of the matches (no projection of the `if`,
which the kernel would reduce by evaluating its condition). -/
theorem sswu?_match_3_ite {β : Type} (c : Prop) [Decidable c] (a b a' b' : Fp2)
    (f : Fp2 → Fp2 → β) :
    H2C.sswu?.match_3 (fun _ => β) (if c then (a, b) else (a', b')) f =
      if c then f a b else f a' b' := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

value_eq sswu?_value : H2C.sswu?

/-- `sswu?` with its matches as `if` and `Option.elim`: `x₁` when `g(x₁)` is a square, else
`x₂`, and the root of `g(x)` whose `sgn0` is `u`'s. -/
theorem sswu?_eq (u : Fp2) : H2C.sswu? u =
    if (H2C.gIso (sswuX1 u)).isSquare = true then
      (H2C.gIso (sswuX1 u)).sqrt?.elim none fun y => some ⟨sswuX1 u, sgnAdj u y⟩
    else (H2C.gIso (sswuX2 u)).sqrt?.elim none fun y => some ⟨sswuX2 u, sgnAdj u y⟩ := by
  rw [sswu?_value]
  unfold sswuX2 sswuX1 sgnAdj
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only [sswu?_match_1, sswu?_match_3_ite]

theorem reduced_gIso {x : Fp2} : (H2C.gIso x).Reduced := by
  unfold H2C.gIso; exact Fp2.reduced_add Fp2.reduced_mul ⟨by decide, by decide⟩

theorem toGF_gIso {x : Fp2} (hx : x.Reduced) :
    (H2C.gIso x).toGF = x.toGF ^ 3 + H2C.sswuA.toGF * x.toGF + H2C.sswuB.toGF := by
  unfold H2C.gIso
  rw [Fp2.toGF_add, Fp2.toGF_mul (Fp2.reduced_add Fp2.reduced_sqr ⟨by decide, by decide⟩) hx,
    Fp2.toGF_add, Fp2.toGF_sqr hx]
  ring

theorem reduced_sswuX1 (u : Fp2) : (sswuX1 u).Reduced := by
  unfold sswuX1; split <;> exact Fp2.reduced_mul

theorem reduced_sswuX2 (u : Fp2) : (sswuX2 u).Reduced := Fp2.reduced_mul

/-- `sgn0`'s choice of sign keeps the root reduced and its square. -/
theorem sgnAdj_spec (u : Fp2) {y : Fp2} (hy : y.Reduced) :
    (sgnAdj u y).Reduced ∧ (sgnAdj u y).toGF ^ 2 = y.toGF ^ 2 := by
  unfold sgnAdj
  split
  · exact ⟨hy, rfl⟩
  · exact ⟨Fp2.reduced_neg hy, by rw [Fp2.toGF_neg hy]; ring⟩

/-- A point `x`, `±√g(x)` is a reduced point of `E''`. -/
theorem sswu_elim_some {u x : Fp2} {q : G2A} (hx : x.Reduced)
    (h : (H2C.gIso x).sqrt?.elim none (fun y => some ⟨x, sgnAdj u y⟩) = some q) :
    q.Reduced ∧ OnIso q := by
  cases hy : (H2C.gIso x).sqrt? with
  | none => rw [hy, Option.elim_none] at h; cases h
  | some y =>
    rw [hy, Option.elim_some] at h
    cases h
    obtain ⟨hyr, hyy⟩ := Fp2.sqrt?_some reduced_gIso hy
    obtain ⟨har, hay⟩ := sgnAdj_spec u hyr
    refine ⟨⟨hx, har⟩, ?_⟩
    show (sgnAdj u y).toGF ^ 2 = _
    rw [hay, sq, hyy, toGF_gIso hx]

/-- What SSWU returns is a reduced point of `E''`. -/
theorem sswu?_some {u : Fp2} {q : G2A} (h : H2C.sswu? u = some q) : q.Reduced ∧ OnIso q := by
  rw [sswu?_eq] at h
  by_cases hs : (H2C.gIso (sswuX1 u)).isSquare = true
  · rw [ite_eq_left hs] at h; exact sswu_elim_some (reduced_sswuX1 u) h
  · rw [ite_eq_right hs] at h; exact sswu_elim_some (reduced_sswuX2 u) h

/-! ## The sum and `clear_cofactor` -/

/-- The runtime's addition of two triples standing for points of `E'` is the group law, the
identity's triples included. -/
theorem G2J.add_good {p q : G2J} (hp : p.Good) (hq : q.Good) :
    (p.add q).Good ∧ aff2 (p.add q).toJ = aff2 p.toJ + aff2 q.toJ := by
  by_cases hpz : p.toJ 2 = 0
  · have e : p.add q = q := by
      unfold G2J.add; rw [ite_eq_left ((Fp2.isZero_iff hp.1.2.2).mpr hpz)]
    rw [e, Point.toAffine_of_Z_eq_zero hpz, zero_add]; exact ⟨hq, rfl⟩
  by_cases hqz : q.toJ 2 = 0
  · have e : p.add q = p := by
      unfold G2J.add
      rw [ite_eq_right (fun h => hpz ((Fp2.isZero_iff hp.1.2.2).mp h)),
        ite_eq_left ((Fp2.isZero_iff hq.1.2.2).mpr hqz)]
    rw [e, Point.toAffine_of_Z_eq_zero hqz, add_zero]; exact ⟨hp, rfl⟩
  have hpn := hp.2.resolve_left hpz
  have hqn := hq.2.resolve_left hqz
  obtain ⟨hr, hn, ha⟩ := G2J.add_spec hp.1 hq.1 hpn hqn
  exact ⟨⟨hr, Or.inr hn⟩, ha⟩

set_option linter.auxLemma false in
theorem clearCofactor_match_1 {β : Type} (x : Option G2A) (f : G2A → β) (n : Unit → β) :
    H2C.clearCofactor.match_1 (fun _ => β) x f n = x.elim (n ()) f := by cases x <;> rfl

value_eq clearCofactor_value : H2C.clearCofactor

/-- `clear_cofactor` is `[h_eff]P`: of a triple standing for a point `P` of `E'`, a reduced,
nonsingular triple standing for `[h_eff]P`. -/
theorem clearCofactor_spec {p : G2J} (hp : p.Good) :
    (H2C.clearCofactor p).Reduced ∧ E2.Nonsingular (H2C.clearCofactor p).toJ ∧
      aff2 (H2C.clearCofactor p).toJ = hEff • aff2 p.toJ := by
  rw [clearCofactor_value]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only [clearCofactor_match_1]
  by_cases hz : p.toJ 2 = 0
  · have e : p.toAffine? = none := by
      unfold G2J.toAffine?; rw [ite_eq_left ((Fp2.isZero_iff hp.1.2.2).mpr hz)]
    rw [e, Option.elim_none, Point.toAffine_of_Z_eq_zero hz, smul_zero, G2J.toJ_inf]
    exact ⟨G2J.reduced_inf, (Jac.inf_spec _).1, (Jac.inf_spec _).2⟩
  have hn := hp.2.resolve_left hz
  have hs := G2J.toAffine?_spec hp.1 hn
  revert hs
  cases p.toAffine? with
  | none => intro hs; exact absurd hs hz
  | some a =>
    intro hs
    obtain ⟨har, han, hae⟩ := hs
    rw [Option.elim_some, ← hae]
    exact G2J.mulA_spec har han hEff

/-! ## `hash_to_G2` -/

set_option linter.auxLemma false in
theorem hashToG2?_match_1 {β : Type} (x y : Option G2A) (f : G2A → G2A → β) (n : β) :
    H2C.hashToG2?.match_1 (fun _ _ => β) x y f (fun _ _ => n) =
      x.elim n fun a => y.elim n fun b => f a b := by
  cases x <;> cases y <;> rfl

value_eq hashToG2?_value : H2C.hashToG2?

/-- `hashToG2?` with its matches as `Option.elim`. -/
theorem hashToG2?_eq (msg dst : ByteArray) : H2C.hashToG2? msg dst =
    (H2C.sswu? (H2C.hashToField msg dst).1).elim none fun q0 =>
      (H2C.sswu? (H2C.hashToField msg dst).2).elim none fun q1 =>
        (H2C.clearCofactor ((H2C.isoMap q0).add (H2C.isoMap q1))).toAffine? := by
  rw [hashToG2?_value]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only [sswu?_match_3, hashToG2?_match_1]

theorem reduced_hashToField (msg dst : ByteArray) :
    (H2C.hashToField msg dst).1.Reduced ∧ (H2C.hashToField msg dst).2.Reduced :=
  ⟨⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩,
    ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩⟩

/-- The sum of the two isogeny images and its cofactor clearing, as `hashToG2?` computes them,
from two points of `E''`: a reduced nonsingular triple standing for
`[h_eff](iso(q₀) + iso(q₁))`. -/
theorem hashSum_spec {q0 q1 : G2A} (h0 : q0.Reduced ∧ OnIso q0) (h1 : q1.Reduced ∧ OnIso q1) :
    (H2C.clearCofactor ((H2C.isoMap q0).add (H2C.isoMap q1))).Reduced ∧
      E2.Nonsingular (H2C.clearCofactor ((H2C.isoMap q0).add (H2C.isoMap q1))).toJ ∧
      aff2 (H2C.clearCofactor ((H2C.isoMap q0).add (H2C.isoMap q1))).toJ =
        hEff • (aff2 (H2C.isoMap q0).toJ + aff2 (H2C.isoMap q1).toJ) := by
  obtain ⟨hg, ha⟩ := G2J.add_good (isoMap_good h0.1 h0.2) (isoMap_good h1.1 h1.2)
  rw [← ha]
  exact clearCofactor_spec hg

/-- **`HashOnCurve` holds**: what `hash_to_G2` returns, on any message and DST, is a reduced
point of `E'` (so not the identity: an affine point). Structural: SSWU's points lie on `E''`, the
isogeny maps them to `E'` (RFC 9380 E.3's identity, checked by the kernel on the constants), the
group law and `[h_eff]` keep them there. -/
theorem hashOnCurve : HashOnCurve := by
  intro msg dst h hh
  rw [hashToG2?_eq] at hh
  obtain ⟨hu0, hu1⟩ := reduced_hashToField msg dst
  cases h0 : H2C.sswu? (H2C.hashToField msg dst).1 with
  | none => rw [h0, Option.elim_none] at hh; cases hh
  | some q0 =>
    rw [h0, Option.elim_some] at hh
    cases h1 : H2C.sswu? (H2C.hashToField msg dst).2 with
    | none => rw [h1, Option.elim_none] at hh; cases hh
    | some q1 =>
      rw [h1, Option.elim_some] at hh
      obtain ⟨hr, hn, -⟩ := hashSum_spec (sswu?_some h0) (sswu?_some h1)
      have hs := G2J.toAffine?_spec hr hn
      rw [hh] at hs
      exact ⟨hs.1, hs.2.1⟩

/-- **`HashInG2` holds**: what `hash_to_G2` returns, on any message and DST, is in G2,
`[r]H = O`. It is `[h_eff]` of a point of `E'` (`hashSum_spec`), and `[r][h_eff]` kills every
point of `E'(𝔽_{p²})` (`hEff_smul_mem_G2`: `r·h_eff = 3(x² − 1)·#E'(𝔽_{p²})`, the group's order
`card_E2` from Hasse's bound and two points of prime order). -/
theorem hashInG2 : HashInG2 := by
  intro msg dst h hh
  rw [hashToG2?_eq] at hh
  cases h0 : H2C.sswu? (H2C.hashToField msg dst).1 with
  | none => rw [h0, Option.elim_none] at hh; cases hh
  | some q0 =>
    rw [h0, Option.elim_some] at hh
    cases h1 : H2C.sswu? (H2C.hashToField msg dst).2 with
    | none => rw [h1, Option.elim_none] at hh; cases hh
    | some q1 =>
      rw [h1, Option.elim_some] at hh
      obtain ⟨hr, hn, ha⟩ := hashSum_spec (sswu?_some h0) (sswu?_some h1)
      have hs := G2J.toAffine?_spec hr hn
      rw [hh] at hs
      rw [hs.2.2, ha]
      exact hEff_smul_mem_G2 _

section Pairing

open WeierstrassCurve.Jacobian

variable {GT : Type} [CommGroup GT]
  (e : E1.toAffine.Point → E2.toAffine.Point → GT)
  (he1 : ∀ a a' b, R • a = 0 → R • a' = 0 → R • b = 0 → e (a + a') b = e a b * e a' b)

include he1 in
/-- **FastAggregateVerify**, `fastAggregateVerify_iff` with `HashOnCurve` and `HashInG2`
discharged (`hashOnCurve`, `hashInG2`): over keys KeyValidate accepted (points of G1), given only
H_vec's pairing on G1 × G2 (`PairingCheckIs e`, for an `e` additive in its first argument on
G1 × G2), true exactly when the keys' sum `A` is not the identity, the signature's bytes pass
its checks as a point `σ`, `hash_to_G2(msg)` under Ethereum's DST is a point `H`, and
`e(g₁, σ) = e(A, H)`. -/
theorem fastAggregateVerify_iff_pairing (hcheck : PairingCheckIs e) (pks : Array G1A)
    (hpks : ∀ p ∈ pks.toList, p.Reduced ∧ E1.Nonsingular p.toJ ∧ R • Point.toAffine E1 p.toJ = 0)
    (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig = true ↔
      (pks.toList.map fun p => Point.toAffine E1 p.toJ).sum ≠ 0 ∧
      ∃ σ h, sigValidate? sig = some σ ∧ H2C.hashToG2? msg ethDst = some h ∧
        e (Point.toAffine E1 g1Gen.toJ) (aff2 σ.toJ) =
          e (pks.toList.map fun p => Point.toAffine E1 p.toJ).sum (aff2 h.toJ) :=
  fastAggregateVerify_iff e he1 hcheck hashOnCurve hashInG2 pks hpks msg sig

include he1 in
/-- **FastAggregateVerify over the keys' bytes**, `fastAggregateVerifyBytes_iff` with
`HashOnCurve` and `HashInG2` discharged: given only `PairingCheckIs e` (on G1 × G2), true
exactly when every key passes KeyValidate, as points `pkᵢ` of G1, `Σ pkᵢ ≠ O`, the signature is
a point `σ`, `hash_to_G2(msg)` a point `H`, and `e(g₁, σ) = e(Σ pkᵢ, H)`. -/
theorem fastAggregateVerifyBytes_iff_pairing (hcheck : PairingCheckIs e)
    (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerifyBytes pks msg sig = true ↔
      ∃ keys, pks.mapM keyValidate? = some keys ∧
        (keys.toList.map fun p => Point.toAffine E1 p.toJ).sum ≠ 0 ∧
        ∃ σ h, sigValidate? sig = some σ ∧ H2C.hashToG2? msg ethDst = some h ∧
          e (Point.toAffine E1 g1Gen.toJ) (aff2 σ.toJ) =
            e (keys.toList.map fun p => Point.toAffine E1 p.toJ).sum (aff2 h.toJ) :=
  fastAggregateVerifyBytes_iff e he1 hcheck hashOnCurve hashInG2 pks msg sig

end Pairing

end LeanLight.Lc.Bls
