import LeanLightProofs.Bls.FavEth

/-!
# BLS12-381: FastAggregateVerify is EthLib's, the identity's signature included (25c)

`fastAggregateVerifyBytes_eq_eth` (`LeanLightProofs.Bls.FavEth`) leaves out one signature, the
identity's canonical encoding: there the runtime refuses (`fastAggregateVerifyBytes_identitySig`)
and EthLib accepts exactly when the runtime's check of the one pair `(−Σ pkᵢ, H(m))` passes
(`fastAggregateVerify_eth_identitySig`). With `H(m)` now known to be in G2 (`hashInG2`), the
two agree there as soon as that check fails on every pair of G1 × G2 points, the pairing's
non-degeneracy as the runtime computes it (`PairingNonDegenerate`), which no theorem here proves
(H_vec): so `fastAggregateVerifyBytes_eq_eth_of_nonDegenerate` drops the signature's condition
for that hypothesis.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

local notation "aff1" => Point.toAffine E1
local notation "aff2" => Point.toAffine E2

/-- H_vec's non-degeneracy, as the runtime computes the pairing: on reduced points of the
order-`r` subgroups, G1 of `E` (`[r]P = O`) and G2 of `E'` (`[r]Q = O`), both affine (so not
the identity), the runtime's check of the one pair `(P, Q)` fails: `e(P, Q) ≠ 1` for the reduced
ate pairing, which is non-degenerate on G1 × G2. A hypothesis, checked by vectors, not proved. -/
def PairingNonDegenerate : Prop :=
  ∀ (p : G1A) (q : G2A), p.Reduced → E1.Nonsingular p.toJ → R • aff1 p.toJ = 0 →
    q.Reduced → E2.Nonsingular q.toJ → R • aff2 q.toJ = 0 → pairingCheck [(p, q)] = false

/-- **FastAggregateVerify is EthLib's, on every signature**, given the pairing's non-degeneracy
on G1 × G2 as the runtime computes it (`PairingNonDegenerate`), when EthLib's `hash_to_G2(msg)`
under Ethereum's DST is not the identity: the runtime's `fastAggregateVerifyBytes` is EthLib's
`fastAggregateVerify`, on every key list, message and signature, the identity's encoding included
(`fastAggregateVerifyBytes_eq_eth` without its condition on the signature). -/
theorem fastAggregateVerifyBytes_eq_eth_of_nonDegenerate (hnd : PairingNonDegenerate)
    (pks : Array ByteArray) (msg sig : ByteArray)
    (hH : ∀ q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
      EthLib.Cryptography.Bls.Signatures.DST = .ok q → q.isInfinity = false) :
    fastAggregateVerifyBytes pks msg sig =
      EthLib.Cryptography.Bls.Signatures.fastAggregateVerify pks msg sig := by
  by_cases hsig : sig = EthLib.Cryptography.Bls.G2.infinityBytes
  swap
  · exact fastAggregateVerifyBytes_eq_eth pks msg sig hH hsig
  subst hsig
  rw [fastAggregateVerifyBytes_identitySig, fastAggregateVerify_eth_identitySig pks msg hH]
  cases hm : pks.mapM keyValidate? with
  | none => rfl
  | some keys =>
    rw [Option.elim_some]
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
    have hagg := aggregate?_spec keys fun p hp => ⟨(hk p hp).1, (hk p hp).2.1⟩
    have hsum := sum_mem_G1 keys.toList fun p hp => (hk p hp).2.2
    revert hagg
    cases aggregate? keys with
    | none => intro _; rfl
    | some agg =>
      intro hagg
      obtain ⟨har, han, hae⟩ := hagg
      rw [Option.elim_some]
      cases hh : H2C.hashToG2? msg ethDst with
      | none => rfl
      | some h =>
        rw [Option.elim_some]
        obtain ⟨hhr, hhn⟩ := hashOnCurve _ _ _ hh
        obtain ⟨hnr, hnn, hne⟩ := G1A.neg_spec har han
        have hns : R • aff1 agg.neg.toJ = 0 := by
          rw [hne, smul_neg, hae, hsum, neg_zero]
        exact (hnd _ _ hnr hnn hns hhr hhn (hashInG2 _ _ _ hh)).symm

end LeanLight.Lc.Bls
