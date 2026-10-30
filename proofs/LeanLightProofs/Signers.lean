import LeanLightProofs.Store
import LeanLightProofs.Bls.FavEth
import LeanLightProofs.Bls.HashCurve

/-!
# The participants' key: the committee's aggregate less the absent (25c, 25d)

The store does not validate a committee's keys, as the consensus specification's light client and
Helios do not: it keeps their encodings and the committee's `aggregate_pubkey` (`Committee.ofSync`)
and, per signature, decodes what it needs (`Store.signersKey?`): when more than half signed, the
aggregate key less the absent keys, else the participants' keys, summed.

What that rests on is the chain's, stated as a hypothesis, never an axiom: `Committee.Consistent`,
that the committee's keys decode to points of G1 and its aggregate key to their sum. The beacon
state's committees are such: each key passed KeyValidate when its deposit was processed, and
`get_next_sync_committee` sets `aggregate_pubkey` to `eth_aggregate_pubkeys` of the keys. The
light client holds a committee only under a root the previous committee signed (`ofSync_keys`,
`receive_committees`), so the hypothesis is the trust it already places in that committee.

* `signersSum?_eq`: when every key decodes, the readable path (`signersSum?`) is `aggregate?` of
  the participants' decoded keys, the sum `fastAggregateVerify` takes. No hypothesis on the
  aggregate.
* `signersKey?_eq`: on a consistent committee the store's key is that sum, whichever path ran.
* `verifySignature_consistent`: on a consistent committee the store's signature check is
  `fastAggregateVerify` over the participants' keys, as `verifySignature_iff` stated it before.
* `verifySignature_iff_pairing`: with H_vec's pairing (`HashInG2` is proved, `hashInG2`), on a
  consistent committee,
  the check is true exactly when the participants' keys sum to a point `A ≠ O`, the signature is a
  point `σ`, the signing root hashes to `H`, and `e(g₁, σ) = e(A, H)`.
-/

namespace LeanLight.Lc.Store

open LeanLight.Lc.Bls
open WeierstrassCurve WeierstrassCurve.Jacobian
open LeanLight.Lc.Forks (Chain computeDomain signingRoot domainSyncCommittee)

local notation "aff1" => Point.toAffine E1
local notation "aff2" => Point.toAffine E2

/-- **A committee as the chain holds one** (a hypothesis, never an axiom): its keys' encodings
decode (`g1Decompress?`) to `keys`, each in G1 (`[r]P = O`), and its aggregate key's to their
sum. The beacon state's are: each key passed KeyValidate at deposit, and the aggregate is
`eth_aggregate_pubkeys` of the keys. It fails only for a committee whose keys sum to the identity,
whose aggregate does not decode: the store then refuses its signatures (liveness, not
soundness). `signersKey?_eq` needs `decode` and `aggregate`; `inG1` is for the pairing. -/
structure Committee.Consistent (com : Committee) (keys : Array G1A) : Prop where
  decode : com.pubkeys.mapM g1Decompress? = some keys
  inG1 : ∀ p ∈ keys.toList, R • aff1 p.toJ = 0
  aggregate : ∃ a, g1Decompress? com.aggregate = some a ∧
    aff1 a.toJ = (keys.toList.map fun p => aff1 p.toJ).sum

/-! ## Lists selected by index -/

theorem getElem?_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      l'.length = l.length ∧ ∀ i : ℕ, l'[i]? = l[i]?.bind f
  | [], l', h => by simp at h; subst h; simp
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some t =>
        simp only [ha, hl, Option.bind_some, Option.pure_def, Option.some.injEq,
          Option.bind_eq_bind] at h
        subst h
        obtain ⟨hlen, hi⟩ := getElem?_of_mapM hl
        refine ⟨by simp [hlen], fun i => ?_⟩
        cases i with
        | zero => simp [ha]
        | succ i => simpa using hi i

/-- Selecting by index commutes with a `mapM` that succeeds. -/
theorem mapM_select {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') (q : ℕ → Bool) : ∀ L : List ℕ,
    (L.filterMap fun i => if q i then l[i]? else none).mapM f =
      some (L.filterMap fun i => if q i then l'[i]? else none)
  | [] => rfl
  | i :: L => by
    obtain ⟨hlen, hi⟩ := getElem?_of_mapM h
    have ih := mapM_select h q L
    rw [List.filterMap_cons, List.filterMap_cons]
    by_cases hq : q i
    · simp only [hq, ite_true]
      rw [hi i]
      cases hli : l[i]? with
      | none => simpa using ih
      | some b =>
        cases hb : f b with
        | none =>
          exfalso
          have hlt : i < l'.length := by
            rw [hlen]; exact (List.getElem?_eq_some_iff.mp hli).1
          have := hi i
          rw [hli, Option.bind_some, hb, List.getElem?_eq_none_iff] at this
          omega
        | some b' => simp [List.mapM_cons, hb, ih]
    · simpa [hq] using ih

/-- A list splits into the elements whose index `q` selects and the others. -/
theorem sum_select {β M : Type} [AddCommMonoid M] (v : β → M) :
    ∀ (q : ℕ → Bool) (l : List β), (l.map v).sum =
      (((List.range l.length).filterMap fun i => if q i then l[i]? else none).map v).sum +
      (((List.range l.length).filterMap fun i => if q i then none else l[i]?).map v).sum
  | _, [] => by simp
  | q, a :: l => by
    have ih := sum_select v (fun i => q (i + 1)) l
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_cons,
      List.filterMap_map, List.filterMap_map]
    simp only [Function.comp_def, List.getElem?_cons_succ, List.getElem?_cons_zero,
      List.map_cons, List.sum_cons]
    cases hq : q 0
    · simp only [Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons, ih]
      abel
    · simp only [ite_true, List.map_cons, List.sum_cons, ih]
      abel

theorem mem_of_select {α : Type} {l : List α} {q : ℕ → Bool} {L : List ℕ} {p : α}
    (h : p ∈ L.filterMap fun i => if q i then l[i]? else none) : p ∈ l := by
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp h
  split at hi
  · exact List.mem_of_getElem? hi
  · cases hi

theorem participants_toList {α : Type} (keys : Array α) (bits : ByteArray) :
    (participants keys bits).toList =
      (List.range keys.toList.length).filterMap fun i => if bit bits i then keys.toList[i]? else none := by
  simp [participants]

theorem absent_eq {α : Type} (keys : Array α) (bits : ByteArray) :
    absent keys bits =
      (List.range keys.toList.length).filterMap fun i => if !bit bits i then keys.toList[i]? else none := by
  unfold absent
  simp only [Array.length_toList, Array.getElem?_toList]
  congr 1
  funext i
  cases bit bits i <;> rfl

theorem toList_of_mapM {α β : Type} {f : α → Option β} {a : Array α} {b : Array β}
    (h : a.mapM f = some b) : a.toList.mapM f = some b.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : a.toList.mapM f with
  | none => simp [hl] at h
  | some l =>
    simp only [hl, Functor.map, Option.map_some, Option.some.injEq] at h
    subst h
    rfl

/-! ## The decoded keys -/

theorem mapM_decode_mem {l : List ByteArray} {ks : List G1A} (h : l.mapM g1Decompress? = some ks)
    {p : G1A} (hp : p ∈ ks) : p.Reduced ∧ E1.Nonsingular p.toJ := by
  obtain ⟨-, hi⟩ := getElem?_of_mapM h
  obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
  rw [hi i] at hpi
  cases hb : l[i]? with
  | none => rw [hb] at hpi; cases hpi
  | some b =>
    rw [hb, Option.bind_some] at hpi
    obtain ⟨hr, hn, -⟩ := g1Decompress?_some hpi
    exact ⟨hr, hn⟩

theorem G1J.ofAffine_reduced {a : G1A} (ha : a.Reduced) : (G1J.ofAffine a).Reduced :=
  ⟨ha.1, ha.2, (by decide : (1 : ℕ) < P)⟩

theorem G1J.ofAffine_toJ (a : G1A) : (G1J.ofAffine a).toJ = a.toJ := by
  funext i; fin_cases i <;> simp [G1J.toJ, G1A.toJ, G1J.ofAffine]

/-- Two reduced points of `E` standing for the same point have the same affine form. -/
theorem G1J.toAffine?_congr {p q : G1J} (hp : p.Reduced) (hpn : E1.Nonsingular p.toJ)
    (hq : q.Reduced) (hqn : E1.Nonsingular q.toJ) (h : aff1 p.toJ = aff1 q.toJ) :
    p.toAffine? = q.toAffine? := by
  have zero_of : ∀ {r : G1J}, r.z = 0 → aff1 r.toJ = 0 := fun hz =>
    Point.toAffine_of_Z_eq_zero (by rw [G1J.toJ_2, hz, Nat.cast_zero])
  have ne_of : ∀ {a : G1A}, E1.Nonsingular a.toJ → aff1 a.toJ ≠ 0 := fun han => by
    rw [G1A.toJ, Point.toAffine_some (by rw [← G1A.toJ]; exact han)]
    exact Affine.Point.some_ne_zero _
  have sp := G1J.toAffine?_spec hp hpn
  have sq := G1J.toAffine?_spec hq hqn
  revert sp sq
  cases p.toAffine? with
  | none =>
    cases q.toAffine? with
    | none => intros; rfl
    | some b =>
      rintro hz ⟨-, hbn, hb⟩
      exact absurd (hb.trans (h.symm.trans (zero_of hz))) (ne_of hbn)
  | some a =>
    cases q.toAffine? with
    | none =>
      rintro ⟨-, han, ha⟩ hz
      exact absurd (ha.trans (h.trans (zero_of hz))) (ne_of han)
    | some b =>
      rintro ⟨har, han, ha⟩ ⟨hbr, hbn, hb⟩
      rw [G1A.eq_of_aff har hbr han hbn (ha.trans (h.trans hb.symm))]

theorem aggregate?_eq_foldl (pks : Array G1A) :
    aggregate? pks = (pks.toList.foldl (fun acc p => acc.addA p) G1J.inf).toAffine? := by
  unfold aggregate?; rw [Array.foldl_toList]

/-! ## The participants' key -/

/-- **The readable path.** When every key of the committee decodes, `signersSum?` is the sum
`fastAggregateVerify` takes: `aggregate?` of the participants' decoded keys. -/
theorem signersSum?_eq {com : Committee} {keys : Array G1A}
    (hd : com.pubkeys.mapM g1Decompress? = some keys) (bits : ByteArray) :
    signersSum? com bits = aggregate? (participants keys bits) := by
  have hl := toList_of_mapM hd
  obtain ⟨hlen, -⟩ := getElem?_of_mapM hl
  have hm := mapM_select hl (bit bits) (List.range com.pubkeys.toList.length)
  have hp : participants keys bits = ((List.range com.pubkeys.toList.length).filterMap
      fun i => if bit bits i then keys.toList[i]? else none).toArray := by
    apply Array.toList_inj.mp
    rw [participants_toList, hlen, List.toList_toArray]
  unfold signersSum?
  rw [Array.mapM_eq_mapM_toList, participants_toList, hm, hp]
  rfl

/-- **The store's key is the participants' sum.** On a committee as the chain holds one
(`Committee.Consistent`), `signersKey?`, which takes the committee's aggregate key less the
absent keys when more than half signed, is `aggregate?` of the participants' decoded keys: the
aggregate `fastAggregateVerify` checks. -/
theorem signersKey?_eq {com : Committee} {keys : Array G1A} (h : com.Consistent keys)
    (bits : ByteArray) : signersKey? com bits = aggregate? (participants keys bits) := by
  unfold signersKey?
  dsimp only
  split
  · obtain ⟨a, ha, hsum⟩ := h.aggregate
    have hl := toList_of_mapM h.decode
    obtain ⟨hlen, -⟩ := getElem?_of_mapM hl
    have hks : (absent com.pubkeys bits).mapM g1Decompress? = some (absent keys bits) := by
      rw [absent_eq, absent_eq, ← hlen]
      exact mapM_select hl (fun i => !bit bits i) _
    rw [ha, hks]
    dsimp only
    have hkeys := fun p (hp : p ∈ keys.toList) => mapM_decode_mem hl hp
    have hout : ∀ p ∈ absent keys bits, p.Reduced ∧ E1.Nonsingular p.toJ := fun p hp =>
      hkeys p (mem_of_select (by rw [absent_eq] at hp; exact hp))
    have hin : ∀ p ∈ (participants keys bits).toList, p.Reduced ∧ E1.Nonsingular p.toJ :=
      fun p hp => hkeys p (mem_of_select (by rw [participants_toList] at hp; exact hp))
    have hneg : ∀ p ∈ (absent keys bits).map G1A.neg, p.Reduced ∧ E1.Nonsingular p.toJ := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      obtain ⟨h1, h2, -⟩ := G1A.neg_spec (hout k hk).1 (hout k hk).2
      exact ⟨h1, h2⟩
    obtain ⟨har, han, -⟩ := g1Decompress?_some ha
    have hinf : E1.Nonsingular G1J.inf.toJ := by rw [G1J.toJ_inf]; exact (Jac.inf_spec 4).1
    obtain ⟨hfr, hfn, hfa⟩ := foldl_addA_spec ((absent keys bits).map G1A.neg) (G1J.ofAffine a)
      (G1J.ofAffine_reduced har) (by rw [G1J.ofAffine_toJ]; exact han) hneg
    obtain ⟨hgr, hgn, hga⟩ := foldl_addA_spec (participants keys bits).toList G1J.inf
      G1J.reduced_inf hinf hin
    have hf : (absent keys bits).foldl (fun acc k => acc.addA k.neg) (G1J.ofAffine a) =
        ((absent keys bits).map G1A.neg).foldl (fun acc k => acc.addA k) (G1J.ofAffine a) := by
      rw [List.foldl_map]
    rw [aggregate?_eq_foldl, hf]
    refine G1J.toAffine?_congr hfr hfn hgr hgn ?_
    rw [hfa, hga, G1J.toJ_inf, (Jac.inf_spec 4).2, zero_add, G1J.ofAffine_toJ, hsum,
      sum_select (fun p => aff1 p.toJ) (bit bits) keys.toList, ← participants_toList,
      List.map_map]
    have hn : ∀ k ∈ absent keys bits, ((fun p => aff1 p.toJ) ∘ G1A.neg) k = -aff1 k.toJ :=
      fun k hk => (G1A.neg_spec (hout k hk).1 (hout k hk).2).2.2
    have hs : ((absent keys bits).map fun k => -aff1 k.toJ).sum =
        -((absent keys bits).map fun k => aff1 k.toJ).sum := by
      rw [List.sum_neg, List.map_map]; rfl
    rw [List.map_congr_left hn, hs]
    have habs : ((List.range keys.toList.length).filterMap fun i =>
        if bit bits i then none else keys.toList[i]?) = absent keys bits := by
      rw [absent_eq]; congr 1; funext i; cases bit bits i <;> rfl
    rw [habs]
    abel
  · exact signersSum?_eq h.decode bits

/-- **The signature check, on a committee as the chain holds one**: `verifySignature_iff` with
the store's key replaced by FastAggregateVerify over the participants' decoded keys, as it read
when the store validated every key. -/
theorem verifySignature_consistent (c : Chain) {com : Committee} {keys : Array G1A}
    (h : com.Consistent keys) (u : Update) :
    verifySignature c com u = true ↔
      ∃ v, c.versionAt (c.epochAt (max u.signatureSlot 1 - 1)) = some v ∧
        fastAggregateVerify (participants keys u.aggregate.bits)
          (signingRoot u.attested.root (computeDomain domainSyncCommittee v c.genesisValidatorsRoot))
          u.aggregate.signature = true := by
  rw [verifySignature_iff, signersKey?_eq h]
  rfl

section Pairing

variable {GT : Type} [CommGroup GT] (e : E1.toAffine.Point → E2.toAffine.Point → GT)
  (he1 : ∀ a a' b, R • a = 0 → R • a' = 0 → R • b = 0 → e (a + a') b = e a b * e a' b)

include he1 in
/-- **The signature check is the verification equation (25c, 25d).** On a committee as the
chain holds one (`Committee.Consistent`: its keys decode to points of G1, its aggregate key to
their sum), given H_vec's pairing on G1 × G2 (`PairingCheckIs e`, for an `e` additive in its
first argument there; `HashInG2` is a theorem, `hashInG2`): the store's signature check of `u`
is true exactly when the fork table gives a version `v` at the epoch of `max(signature_slot, 1) − 1`, the keys
whose bit is set sum to a point `A` other than the identity, the signature's bytes pass its
checks as a point `σ`, the signing root of the attested header's root under
`compute_domain(DOMAIN_SYNC_COMMITTEE, v, genesis_validators_root)` hashes to a point `H`, and
`e(g₁, σ) = e(A, H)`. -/
theorem verifySignature_iff_pairing (hcheck : PairingCheckIs e) (c : Chain)
    {com : Committee} {keys : Array G1A} (h : com.Consistent keys) (u : Update) :
    verifySignature c com u = true ↔
      ∃ v, c.versionAt (c.epochAt (max u.signatureSlot 1 - 1)) = some v ∧
        ((participants keys u.aggregate.bits).toList.map fun p => aff1 p.toJ).sum ≠ 0 ∧
        ∃ σ H, sigValidate? u.aggregate.signature = some σ ∧
          H2C.hashToG2? (signingRoot u.attested.root
            (computeDomain domainSyncCommittee v c.genesisValidatorsRoot)) ethDst = some H ∧
          e (aff1 g1Gen.toJ) (aff2 σ.toJ) =
            e ((participants keys u.aggregate.bits).toList.map fun p => aff1 p.toJ).sum
              (aff2 H.toJ) := by
  have hl := toList_of_mapM h.decode
  have hp : ∀ p ∈ (participants keys u.aggregate.bits).toList,
      p.Reduced ∧ E1.Nonsingular p.toJ ∧ R • aff1 p.toJ = 0 := by
    intro p hp
    have hk : p ∈ keys.toList := mem_of_select (by rw [participants_toList] at hp; exact hp)
    exact ⟨(mapM_decode_mem hl hk).1, (mapM_decode_mem hl hk).2, h.inG1 p hk⟩
  rw [verifySignature_consistent c h u]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  exact fastAggregateVerify_iff_pairing e he1 hcheck _ hp _ _

end Pairing

end LeanLight.Lc.Store
