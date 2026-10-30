import LeanLightProofs.Bls.Decompress
import LeanLight.Bls.Fav

/-!
# BLS12-381: FastAggregateVerify is the verification equation, given a pairing (25c)

`LeanLight.Bls.fastAggregateVerify pks msg sig`, over keys KeyValidate accepted (points of the
order-`r` subgroup G1), is true exactly when the sum of the keys is not the identity, the
signature passes its checks as a point `σ` (on `E'`, `[r]σ = O`, not the identity),
`hash_to_G2(msg)` under Ethereum's DST is a point `H`, and

  `e(g₁, σ) = e(Σ pkᵢ, H)`

(`fastAggregateVerify_iff`, and `fastAggregateVerifyBytes_iff` over the keys' bytes), for any
map `e` from the points of `E` and `E'` to a commutative group that is additive in its first
argument on G1 × G2, given three hypotheses, never axioms (the first and third H_vec's,
`docs/spec-16-light-client.md`; the second proved since):

* `PairingCheckIs e`: on reduced points of the subgroups G1 of `E` and G2 of `E'` (`[r]P = O`,
  `[r]Q = O`), the runtime's `pairingCheck` of two pairs is true exactly when the product of
  their values under `e` is one. That the Miller loop and the final exponentiation compute such
  an `e`, bilinear and non-degenerate (the reduced optimal ate pairing on G1 × G2), is checked by
  vectors, not proved; the cube lemma (`finalExp_isOne_iff`) and the final exponentiation's
  value (`finalExp_toGF`) are the parts that are. The hypothesis
  and the additivity of `e` are over the subgroups only: over every point of `E(𝔽_p)` and
  `E'(𝔽_{p²})` no `e` satisfies both (the runtime's check is not bilinear off G2), and a theorem
  taking them there would be vacuous.
* `HashOnCurve`: what `hash_to_G2` returns is a reduced point of `E'`. Since LC4b's rest a
  theorem (`hashOnCurve`, `LeanLightProofs.Bls.HashCurve`), so `fastAggregateVerify_iff_pairing`
  and `fastAggregateVerifyBytes_iff_pairing` there state these without it.
* `HashInG2`: that point is in G2, `[r]H = O` (`clear_cofactor`'s `[h_eff]` lands in G2). Since
  proved too (`hashInG2`, `LeanLightProofs.Bls.HashCurve`, from `#E'(𝔽_{p²}) = r·h₂`,
  `LeanLightProofs.Bls.PointCount`), so `fastAggregateVerify_iff_pairing` and
  `fastAggregateVerifyBytes_iff_pairing` there take `PairingCheckIs e` alone.

The hypotheses take `Spec.Bn254`'s shape for a pairing (reuse rule D18): the map and its laws are
variables of the theorem.

Also here: the aggregate is the sum of the keys (`aggregate?_spec`), and the negation of an
affine point is the group's (`G1A.neg_spec`).
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

local notation "aff1" => Point.toAffine E1
local notation "aff2" => Point.toAffine E2

/-! ## The aggregate -/

/-- The fold of `aggregate?` over reduced points of `E` stays a reduced point of `E` standing
for the running sum. -/
theorem foldl_addA_spec : ∀ (l : List G1A) (acc : G1J), acc.Reduced → E1.Nonsingular acc.toJ →
    (∀ p ∈ l, p.Reduced ∧ E1.Nonsingular p.toJ) →
    (l.foldl (fun acc p => acc.addA p) acc).Reduced ∧
      E1.Nonsingular (l.foldl (fun acc p => acc.addA p) acc).toJ ∧
      aff1 (l.foldl (fun acc p => acc.addA p) acc).toJ =
        aff1 acc.toJ + (l.map fun p => aff1 p.toJ).sum := by
  intro l
  induction l with
  | nil => intro acc hr hn _; simp [hr, hn]
  | cons p l ih =>
    intro acc hr hn hl
    have hp := hl p (List.mem_cons_self ..)
    obtain ⟨hr', hn', ha'⟩ := G1J.addA_spec hr hp.1 hn hp.2
    obtain ⟨h1, h2, h3⟩ := ih _ hr' hn' fun q hq => hl q (List.mem_cons_of_mem _ hq)
    refine ⟨h1, h2, ?_⟩
    rw [List.foldl_cons, h3, ha', List.map_cons, List.sum_cons, add_assoc]

/-- The aggregate of reduced points of `E` is their sum: `none` exactly when the sum is the
identity, else a reduced point of `E` standing for it. -/
theorem aggregate?_spec (pks : Array G1A) (hpks : ∀ p ∈ pks.toList, p.Reduced ∧ E1.Nonsingular p.toJ) :
    match aggregate? pks with
    | none => (pks.toList.map fun p => aff1 p.toJ).sum = 0
    | some a => a.Reduced ∧ E1.Nonsingular a.toJ ∧
        aff1 a.toJ = (pks.toList.map fun p => aff1 p.toJ).sum := by
  have hinf : E1.Nonsingular G1J.inf.toJ := by rw [G1J.toJ_inf]; exact (Jac.inf_spec 4).1
  obtain ⟨hr, hn, ha⟩ := foldl_addA_spec pks.toList G1J.inf G1J.reduced_inf hinf hpks
  rw [G1J.toJ_inf, (Jac.inf_spec 4).2, zero_add] at ha
  have e : aggregate? pks = (pks.toList.foldl (fun acc p => acc.addA p) G1J.inf).toAffine? := by
    unfold aggregate?; rw [Array.foldl_toList]
  rw [e]
  have hs := G1J.toAffine?_spec hr hn
  revert hs
  cases (pks.toList.foldl (fun acc p => acc.addA p) G1J.inf).toAffine? with
  | none =>
    intro hs
    have hz : (pks.toList.foldl (fun acc p => acc.addA p) G1J.inf).z = 0 := hs
    rw [← ha]
    exact Point.toAffine_of_Z_eq_zero (by rw [G1J.toJ_2, hz, Nat.cast_zero])
  | some a =>
    intro hs
    obtain ⟨har, han, hae⟩ := hs
    exact ⟨har, han, hae.trans ha⟩

/-- The negation of a reduced affine point of `E` is the group's negation. -/
theorem G1A.neg_spec {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    p.neg.Reduced ∧ E1.Nonsingular p.neg.toJ ∧ aff1 p.neg.toJ = -aff1 p.toJ := by
  have he : p.neg.toJ = ![(p.x : GFp), -(p.y : GFp), 1] := by
    funext i; fin_cases i <;> simp [G1A.toJ, G1A.neg, cast_fneg hp.2.le]
  have hn' : E1.Nonsingular p.neg.toJ := by
    rw [he, E1_nonsingular_iff]
    rw [G1A.toJ, E1_nonsingular_iff] at hn
    linear_combination hn
  refine ⟨⟨hp.1, fneg_lt hp.2⟩, hn', ?_⟩
  rw [he] at hn' ⊢
  rw [Point.toAffine_some hn', G1A.toJ, Point.toAffine_some hn, Affine.Point.neg_some]
  congr 1
  simp [Affine.negY]

/-! ## `hash_to_G2`'s output -/

/-- `G2J.toAffine?`'s points are reduced: their coordinates are products. -/
theorem G2J.toAffine?_reduced {p : G2J} {a : G2A} (h : p.toAffine? = some a) : a.Reduced := by
  unfold G2J.toAffine? at h
  split at h
  · cases h
  · cases h; exact ⟨Fp2.reduced_mul, Fp2.reduced_mul⟩

/-! ## FastAggregateVerify -/

/-- H_vec's pairing, for the check of two pairs: on reduced points of the order-`r` subgroups,
G1 of `E` (`[r]P = O`) and G2 of `E'` (`[r]Q = O`), the runtime's `pairingCheck` is true exactly
when the product of the pairs' values under `e` is one. The reduced ate pairing on G1 × G2 is a
witness. Over every point of the curves the hypothesis, with `e` additive in its first argument,
has none: off G2 the runtime's check is not bilinear, so it is stated on the subgroups only. -/
def PairingCheckIs {GT : Type} [CommGroup GT] (e : E1.toAffine.Point → E2.toAffine.Point → GT) :
    Prop :=
  ∀ (p1 p2 : G1A) (q1 q2 : G2A), p1.Reduced → E1.Nonsingular p1.toJ → R • aff1 p1.toJ = 0 →
    p2.Reduced → E1.Nonsingular p2.toJ → R • aff1 p2.toJ = 0 →
    q1.Reduced → E2.Nonsingular q1.toJ → R • aff2 q1.toJ = 0 →
    q2.Reduced → E2.Nonsingular q2.toJ → R • aff2 q2.toJ = 0 →
    (pairingCheck [(p1, q1), (p2, q2)] = true ↔
      e (aff1 p1.toJ) (aff2 q1.toJ) * e (aff1 p2.toJ) (aff2 q2.toJ) = 1)

/-- What `hash_to_G2` returns is a reduced point of `E'`. A hypothesis of
`fastAggregateVerify_iff` when LC4b stated it; proved since (`hashOnCurve`,
`LeanLightProofs.Bls.HashCurve`: SSWU's points lie on `E''`, RFC 9380 E.3's isogeny maps them to
`E'`, by a polynomial identity the kernel checks on the constants, and the group law and
`[h_eff]` keep them there). -/
def HashOnCurve : Prop :=
  ∀ msg dst h, H2C.hashToG2? msg dst = some h → h.Reduced ∧ E2.Nonsingular h.toJ

/-- What `hash_to_G2` returns is in G2, `[r]H = O`. `clear_cofactor` is `[h_eff]` of a point of
`E'` (`hashSum_spec`, `LeanLightProofs.Bls.HashCurve`), and RFC 9380 chooses `h_eff` so that
`[h_eff]` maps `E'(𝔽_{p²})` into G2. A hypothesis of the theorems here, never an axiom; proved
since (`hashInG2`, `LeanLightProofs.Bls.HashCurve`: `[r][h_eff]` kills every point of `E'`, whose
group has `r·h₂` elements, `card_E2`). -/
def HashInG2 : Prop :=
  ∀ msg dst h, H2C.hashToG2? msg dst = some h → R • aff2 h.toJ = 0

set_option linter.auxLemma false in
theorem fastAggregateVerify_match_3 (x : Option G1A) (n : Unit → Bool) (f : G1A → Bool) :
    verifyAggregate.match_3 (fun _ => Bool) x n f = x.elim (n ()) f := by cases x <;> rfl

set_option linter.auxLemma false in
theorem fastAggregateVerify_match_1 (x : Option G2A) (n : Unit → Bool) (f : G2A → Bool) :
    verifyAggregate.match_1 (fun _ => Bool) x n f = x.elim (n ()) f := by cases x <;> rfl

section Pairing

variable {GT : Type} [CommGroup GT] (e : E1.toAffine.Point → E2.toAffine.Point → GT)
  (he1 : ∀ a a' b, R • a = 0 → R • a' = 0 → R • b = 0 → e (a + a') b = e a b * e a' b)

include he1 in
/-- `e(−a, b) = e(a, b)⁻¹` for `a` in G1 and `b` in G2, from `e`'s additivity there. -/
theorem pair_neg_left (a : E1.toAffine.Point) (b : E2.toAffine.Point) (ha : R • a = 0)
    (hb : R • b = 0) : e (-a) b = (e a b)⁻¹ := by
  have h0 : e 0 b = 1 := by
    have := he1 0 0 b (nsmul_zero R) (nsmul_zero R) hb
    rw [add_zero] at this
    exact left_eq_mul.mp this
  rw [eq_inv_iff_mul_eq_one, ← he1 _ _ _ (by rw [neg_nsmul, ha, neg_zero]) ha hb, neg_add_cancel,
    h0]

/-- A sum of points of G1 is in G1. -/
theorem sum_mem_G1 (l : List G1A) (hl : ∀ p ∈ l, R • aff1 p.toJ = 0) :
    R • (l.map fun p => aff1 p.toJ).sum = 0 := by
  rw [List.smul_sum, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact hl p hp

include he1 in
/-- **FastAggregateVerify** over keys KeyValidate accepted (reduced points of `E` in G1), given
H_vec's pairing on G1 × G2 and hash-to-curve (`PairingCheckIs e`, `HashOnCurve`, `HashInG2`) for
an `e` additive in its first argument on G1 × G2: true exactly when the keys' sum `A` is not the
identity, the signature's bytes pass its checks as a point `σ`, `hash_to_G2(msg)` under
Ethereum's DST is a point `H`, and `e(g₁, σ) = e(A, H)`. -/
theorem fastAggregateVerify_iff (hcheck : PairingCheckIs e) (hhash : HashOnCurve)
    (hg2 : HashInG2) (pks : Array G1A)
    (hpks : ∀ p ∈ pks.toList, p.Reduced ∧ E1.Nonsingular p.toJ ∧ R • aff1 p.toJ = 0)
    (msg sig : ByteArray) :
    fastAggregateVerify pks msg sig = true ↔
      (pks.toList.map fun p => aff1 p.toJ).sum ≠ 0 ∧
      ∃ σ h, sigValidate? sig = some σ ∧ H2C.hashToG2? msg ethDst = some h ∧
        e (aff1 g1Gen.toJ) (aff2 σ.toJ) = e (pks.toList.map fun p => aff1 p.toJ).sum (aff2 h.toJ) := by
  have hagg := aggregate?_spec pks fun p hp => ⟨(hpks p hp).1, (hpks p hp).2.1⟩
  have hsum := sum_mem_G1 pks.toList fun p hp => (hpks p hp).2.2
  unfold fastAggregateVerify verifyAggregate
  rw [fastAggregateVerify_match_3]
  revert hagg
  cases aggregate? pks with
  | none =>
    intro hagg
    rw [Option.elim_none]
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd hagg h
  | some agg =>
    intro hagg
    obtain ⟨har, han, hae⟩ := hagg
    rw [Option.elim_some]
    simp only [fastAggregateVerify_match_1]
    cases hs : sigValidate? sig with
    | none =>
      rw [Option.elim_none]
      simp
    | some s =>
      rw [Option.elim_some]
      obtain ⟨-, hsr, hsn, -, hss⟩ := sigValidate?_some hs
      cases hh : H2C.hashToG2? msg ethDst with
      | none =>
        rw [Option.elim_none]
        simp
      | some h =>
        rw [Option.elim_some]
        obtain ⟨hhr, hhn⟩ := hhash _ _ _ hh
        have hhs := hg2 _ _ _ hh
        obtain ⟨hnr, hnn, hne⟩ := G1A.neg_spec har han
        have has : R • aff1 agg.toJ = 0 := hae ▸ hsum
        have hns : R • aff1 agg.neg.toJ = 0 := by rw [hne, neg_nsmul, has, neg_zero]
        have hgs := (G1A.inSubgroup_iff g1Gen_reduced g1Gen_nonsingular).mp g1Gen_inSubgroup
        rw [hcheck _ _ _ _ g1Gen_reduced g1Gen_nonsingular hgs hnr hnn hns hsr hsn hss hhr hhn hhs,
          hne, pair_neg_left e he1 _ _ has hhs, ← hae]
        constructor
        · intro h1
          refine ⟨?_, s, h, rfl, rfl, ?_⟩
          · rw [G1A.toJ, Point.toAffine_some (by rw [← G1A.toJ]; exact han)]
            exact Affine.Point.some_ne_zero _
          · exact mul_inv_eq_one.mp h1
        · rintro ⟨-, σ, h', hσ, hh', heq⟩
          cases hσ; cases hh'
          exact mul_inv_eq_one.mpr heq

/-- Every key `mapM keyValidate?` returns is one KeyValidate accepted. -/
theorem mapM_keyValidate?_mem : ∀ (l : List ByteArray) (keys : List G1A),
    l.mapM keyValidate? = some keys → ∀ p ∈ keys, p.Reduced ∧ E1.Nonsingular p.toJ := by
  intro l
  induction l with
  | nil => intro keys h; simp at h; subst h; simp
  | cons b l ih =>
    intro keys h p hp
    rw [List.mapM_cons] at h
    cases hk : keyValidate? b with
    | none => simp [hk] at h
    | some k =>
      cases hks : l.mapM keyValidate? with
      | none => simp [hk, hks] at h
      | some ks =>
        simp only [hk, hks, Option.bind_some, Option.pure_def, Option.some.injEq,
          Option.bind_eq_bind] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · obtain ⟨-, hr, hn, -⟩ := keyValidate?_some hk; exact ⟨hr, hn⟩
        · exact ih ks hks p hp

/-- Every key `mapM keyValidate?` returns has `[r]P = O`. -/
theorem mapM_keyValidate?_sub : ∀ (l : List ByteArray) (keys : List G1A),
    l.mapM keyValidate? = some keys → ∀ p ∈ keys, R • aff1 p.toJ = 0 := by
  intro l
  induction l with
  | nil => intro keys h; simp at h; subst h; simp
  | cons b l ih =>
    intro keys h p hp
    rw [List.mapM_cons] at h
    cases hk : keyValidate? b with
    | none => simp [hk] at h
    | some k =>
      cases hks : l.mapM keyValidate? with
      | none => simp [hk, hks] at h
      | some ks =>
        simp only [hk, hks, Option.bind_some, Option.pure_def, Option.some.injEq,
          Option.bind_eq_bind] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (keyValidate?_some hk).2.2.2.2
        · exact ih ks hks p hp

include he1 in
/-- **FastAggregateVerify over the keys' bytes** (IRTF BLS's, as the light client calls it), given
H_vec's pairing on G1 × G2 and hash-to-curve: true exactly when every key passes KeyValidate, as
points `pkᵢ` of the order-`r` subgroup of `E` other than the identity, and
`fastAggregateVerify_iff`'s conditions hold for them: `Σ pkᵢ ≠ O`, the signature is a point `σ`,
`hash_to_G2(msg)` a point `H`, and `e(g₁, σ) = e(Σ pkᵢ, H)`. -/
theorem fastAggregateVerifyBytes_iff (hcheck : PairingCheckIs e) (hhash : HashOnCurve)
    (hg2 : HashInG2) (pks : Array ByteArray) (msg sig : ByteArray) :
    fastAggregateVerifyBytes pks msg sig = true ↔
      ∃ keys, pks.mapM keyValidate? = some keys ∧
        (keys.toList.map fun p => aff1 p.toJ).sum ≠ 0 ∧
        ∃ σ h, sigValidate? sig = some σ ∧ H2C.hashToG2? msg ethDst = some h ∧
          e (aff1 g1Gen.toJ) (aff2 σ.toJ) =
            e (keys.toList.map fun p => aff1 p.toJ).sum (aff2 h.toJ) := by
  unfold fastAggregateVerifyBytes
  cases hm : pks.mapM keyValidate? with
  | none => simp
  | some keys =>
    have hk : ∀ p ∈ keys.toList, p.Reduced ∧ E1.Nonsingular p.toJ ∧ R • aff1 p.toJ = 0 := by
      rw [Array.mapM_eq_mapM_toList] at hm
      cases hl : pks.toList.mapM keyValidate? with
      | none => simp [hl] at hm
      | some l =>
        simp only [hl, Functor.map, Option.map_some, Option.some.injEq] at hm
        subst hm
        intro p hp
        simp only at hp
        exact ⟨(mapM_keyValidate?_mem _ _ hl p hp).1, (mapM_keyValidate?_mem _ _ hl p hp).2,
          mapM_keyValidate?_sub _ _ hl p hp⟩
    simp only [Option.some.injEq, exists_eq_left']
    exact fastAggregateVerify_iff e he1 hcheck hhash hg2 keys hk msg sig

end Pairing

end LeanLight.Lc.Bls
