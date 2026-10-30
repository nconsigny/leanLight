import LeanLightProofs.Bls.Roundtrip
import LeanLightProofs.Bls.HashEth
import LeanLightProofs.Bls.FinalExp
import LeanLightProofs.Bls.FinalExpPow
import LeanLightProofs.Bls.Miller

/-!
# BLS12-381: FastAggregateVerify is EthLib's, where `H(m)` is not the identity (25c)

EthLib's `fastAggregateVerify` decodes each key with its own `G1.uncompress` and `keyValidate`,
sums them with its own formulas, re-encodes the sum with `G1.compress` and runs `coreVerify` on
it: KeyValidate again, `G2.uncompress` and the subgroup check of the signature, its `hashToG2`,
and its naive `pairingCheck`. Each is related to the runtime's here:

* `Eth.G1.uncompress_eq`, `Eth.G2.uncompress_eq`: with the identity flag clear, EthLib's decoders
  are the runtime's (`g1Decompress?`, `g2Decompress?`), as EthLib points `(x, y, 1)`; with it
  set, EthLib's give an error or the identity (the latter only for the canonical encoding, for
  G2);
* `Eth.G1.keyValidate_eq`: EthLib's KeyValidate accepts exactly what `keyValidate?` does;
* `Eth.G1.compress_eq`: EthLib's `G1.compress` of a point of `E` other than the identity is the
  runtime's compression of its affine point;
* `Eth.pairingCheck_eq`: EthLib's `pairingCheck` is its naive final exponentiation of an
  accumulator (`Eth.pairingAcc`) that skips identity pairs and depends on each point only
  through its affine coordinates.

* `millerLoopsCube`: on pairs whose G2 point is in G2 (`[r]Q = O`), the runtime's Miller loop and
  EthLib's accumulator agree after the final exponentiation (`LeanLightProofs.Bls.Miller`); the
  runtime's final exponentiation is proved (`finalExp_toGF`), so this is LC4b's `FinalExpCube`
  for each such list of pairs (`millerLoopsCube_iff`), and the runtime's `pairingCheck` is
  EthLib's on them (`pairingCheck_eq_eth`).

`fastAggregateVerifyBytes_eq_eth`: when EthLib's `hashToG2 msg` is not the identity and the
signature is not the identity's encoding, the runtime's `fastAggregateVerifyBytes` is EthLib's
`fastAggregateVerify`, on every key list, message and signature. The signature its checks accept
is in G2 (`[r]σ = O`) and so is `H(m)` (`hashInG2`), so `pairingCheck_eq_eth` applies.

The identity's encoding as the signature is the one case left, and it is characterized
(`fastAggregateVerify_eth_identitySig`): EthLib decodes it to the identity and skips its pair,
so it accepts exactly when the runtime's check of the one pair `(−Σ pkᵢ, H(m))` passes,
`e(Σ pkᵢ, H(m)) = 1`, where the runtime refuses (`fastAggregateVerifyBytes_identitySig`). They
agree there exactly when that check fails, which the pairing's non-degeneracy gives, `H(m)`
being in G2 (`hashInG2`); non-degeneracy is not proved (`LeanLightProofs.Bls.FavEthG2`).

The unfoldings follow `LeanLightProofs.Bls.HashEth`'s rules: values through `value_eq`, EthLib's
private helpers by `delta_private`, matches rewritten (or their discriminants generalized) before
anything is zeta-reduced or compared, so the kernel never evaluates SHA-256 or a square root.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian
open LeanLight.Lc.Bls.Provenance (ofEth)
open EthLib.Cryptography.Bls (Fp)

local notation "aff1" => Point.toAffine E1
local notation "aff2" => Point.toAffine E2

/-! ## Reading a field element -/

theorem bytesBEToNat_eq (c : ByteArray) : Fp.bytesBEToNat c = beNat c 0 c.size := by
  unfold Fp.bytesBEToNat
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range', beNat_eq_foldl, Nat.zero_add]
  apply List.foldl_ext
  intro v i _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (UInt8.toNat_lt _), Nat.shiftLeft_eq]

/-- `beNat` of `n + 1` bytes from `off`: the first, then the `n` after it. -/
theorem beNat_succ (b : ByteArray) (off n acc : ℕ) :
    beNat b off (n + 1) acc = beNat b (off + 1) n (acc * 256 + (b[off]?.getD 0).toNat) := by
  rw [beNat_eq_foldl, beNat_eq_foldl, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [Nat.add_zero]
  apply List.foldl_ext
  intro v i _
  rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- `beNat` depends only on the bytes it reads. -/
theorem beNat_congr {b c : ByteArray} {off off' n : ℕ} (acc : ℕ)
    (h : ∀ i < n, b[off + i]?.getD 0 = c[off' + i]?.getD 0) :
    beNat b off n acc = beNat c off' n acc := by
  rw [beNat_eq_foldl, beNat_eq_foldl]
  apply List.foldl_ext
  intro v i hi
  rw [h i (List.mem_range.mp hi)]

theorem signBit_eq (y : Fp) : y.signBit = fLarge y.val := by
  have hP : P % 2 = 1 := by decide
  have hy := val_lt y
  unfold EthLib.Cryptography.Bls.Fp.signBit fLarge
  show decide (y.val > P - y.val) = _
  by_cases h : y.val > (P - 1) / 2
  · simp [h]; omega
  · simp [h]; omega

theorem fp_ofNat_val (a : Fp) : Fp.ofNat a.val = a := by
  apply Fin.ext; simp [EthLib.Cryptography.Bls.Fp.ofNat, Fin.ofNat, Nat.mod_eq_of_lt a.isLt]

theorem size_set0 (b : ByteArray) (v : UInt8) (h : 0 < b.size) : (b.set 0 v h).size = b.size := by
  show (b.set 0 v h).data.size = b.data.size
  rw [ByteArray.data_set, Array.size_set]

theorem set0_getD (b : ByteArray) (v : UInt8) (h : 0 < b.size) (j : ℕ) :
    (b.set 0 v h)[j]?.getD 0 = if j = 0 then v else b[j]?.getD 0 := by
  by_cases hj : j < b.size
  · rw [getElem?_pos _ j (by rw [size_set0]; exact hj), getElem?_pos b j hj, Option.getD_some,
      Option.getD_some]
    simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]
    by_cases h0 : j = 0
    · subst h0; simp
    · rw [ite_eq_right (Ne.symm h0), ite_eq_right h0]
  · rw [getElem?_neg _ j (by rw [size_set0]; exact hj), getElem?_neg b j hj,
      ite_eq_right (by omega)]

/-- EthLib's `Fp.fromBytesBE` of 48 bytes whose first is replaced by `v` (the flags cleared):
the big-endian number `v ‖ b[1..48)`, when below `p`. -/
theorem fromBytesBE_set0 (b : ByteArray) (v : UInt8) (hs : b.size = 48) :
    (Fp.fromBytesBE (if h : 0 < b.size then b.set 0 v h else b)).toOption =
      if h : beNat b 1 47 v.toNat < P then some ⟨_, h⟩ else none := by
  have h0 : 0 < b.size := by omega
  rw [dite_eq_left h0]
  unfold Fp.fromBytesBE
  rw [ite_eq_right (by rw [size_set0, hs]; exact fun h => h rfl)]
  have hn : Fp.bytesBEToNat (b.set 0 v h0) = beNat b 1 47 v.toNat := by
    rw [bytesBEToNat_eq, size_set0, hs, beNat_succ, set0_getD, ite_eq_left rfl]
    simp only [Nat.zero_mul, Nat.zero_add]
    apply beNat_congr
    intro i _
    rw [set0_getD, ite_eq_right (by omega)]
  simp only [hn]
  by_cases hlt : beNat b 1 47 v.toNat < P
  · rw [dite_eq_left (show beNat b 1 47 v.toNat < Fp.modulus from hlt), dite_eq_left hlt]; rfl
  · rw [dite_eq_right (show ¬beNat b 1 47 v.toNat < Fp.modulus from hlt), dite_eq_right hlt]; rfl

namespace Eth

/-- A runtime affine point of `E` as an EthLib point `(x, y, 1)`. -/
def G1.ofA (p : G1A) : EthLib.Cryptography.Bls.G1 :=
  ⟨Fp.ofNat p.x, Fp.ofNat p.y, EthLib.Cryptography.Bls.Fp.one⟩

/-- A runtime affine point of `E'` as an EthLib point `(x, y, 1)`. -/
noncomputable def G2.ofA (q : G2A) : EthLib.Cryptography.Bls.G2 :=
  ⟨q.x.toEth, q.y.toEth, EthLib.Cryptography.Bls.Fp2.one⟩

end Eth

value_eq g1Uncompress_value : EthLib.Cryptography.Bls.G1.uncompress

/-- With the identity flag clear, EthLib's `G1.uncompress` is the runtime's `g1Decompress?`, as
EthLib points `(x, y, 1)`. -/
theorem Eth.G1.uncompress_eq (b : ByteArray) (h64 : (b[0]?.getD 0) &&& 64 = 0) :
    EthLib.Cryptography.Bls.G1.uncompress b =
      (g1Decompress? b).elim (.error .invalidG1Point) fun p => .ok (G1.ofA p) := by
  rw [g1Uncompress_value, g1Decompress?_eq]
  -- `G1.uncompress`'s `let`s are dependent, which `simp` does not enter with `zeta := false`:
  -- the `let`s first here (its matches' discriminants are stuck on `b.size` for the kernel).
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  simp (config := { iota := false, zeta := false, beta := true, proj := false, decide := false })
    only [ethFp2Sqrt_match_3]
  delta_private
  by_cases hs : b.size ≠ 48
  · rw [ite_eq_left hs, ite_eq_left hs]; rfl
  rw [ite_eq_right hs, ite_eq_right hs]
  by_cases h1 : (b[0]?.getD 0) &&& 128 = 0
  · rw [ite_eq_left (by simp [h1]), ite_eq_left h1]; rfl
  rw [ite_eq_right (by simp [h1]), ite_eq_right h1, ite_eq_right (fun h => h h64),
    ite_eq_right (fun h => h h64)]
  have hs' : b.size = 48 := by omega
  rw [fromBytesBE_set0 b _ hs']
  generalize beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = X
  by_cases hX : X < P
  · rw [dite_eq_left hX, Option.elim_some, ite_eq_right (by omega)]
    have hv : fadd (fmul (fsqr X) X) 4 =
        ((⟨X, hX⟩ : Fp) * ⟨X, hX⟩ * ⟨X, hX⟩ + Fp.ofNat 4).val := by
      rw [← cast_inj (fadd_lt fmul_lt (by decide)) (val_lt _)]
      simp only [cast_fadd, cast_fmul, cast_fsqr, cast_val_add, cast_val_mul, cast_val_ofNat]
    rw [hv, fsqrt?_val]
    generalize (Fp.sqrt ((⟨X, hX⟩ : Fp) * ⟨X, hX⟩ * ⟨X, hX⟩ + Fp.ofNat 4)).toOption = o
    cases o with
    | none => rfl
    | some yP =>
      rw [Option.map_some, Option.elim_some, Option.elim_some, Option.elim_some]
      unfold G1.ofA
      have hx : Fp.ofNat X = ⟨X, hX⟩ := Fin.ext (by
        simp [EthLib.Cryptography.Bls.Fp.ofNat, Fin.ofNat, Nat.mod_eq_of_lt (modulus_eq ▸ hX)])
      rw [hx, signBit_eq]
      congr 2
      by_cases hsg : (b[0]?.getD 0) &&& 32 ≠ 0
      · cases hf : fLarge yP.val
        · rw [ite_eq_right (by simp [hsg]), ite_eq_right (by simp [hsg]), fneg_val, fp_ofNat_val]
        · rw [ite_eq_left (by simp [hsg]), ite_eq_left (by simp [hsg]), fp_ofNat_val]
      · cases hf : fLarge yP.val
        · rw [ite_eq_left (by simp [hsg]), ite_eq_left (by simp [hsg]), fp_ofNat_val]
        · rw [ite_eq_right (by simp [hsg]), ite_eq_right (by simp [hsg]), fneg_val, fp_ofNat_val]
  · rw [dite_eq_right hX, ite_eq_left (by omega)]; rfl

/-- With the identity flag set, EthLib's `G1.uncompress` errs or gives the identity. -/
theorem Eth.G1.uncompress_inf (b : ByteArray) (h64 : (b[0]?.getD 0) &&& 64 ≠ 0) :
    EthLib.Cryptography.Bls.G1.uncompress b = .error .invalidG1Point ∨
      EthLib.Cryptography.Bls.G1.uncompress b = .ok EthLib.Cryptography.Bls.G1.zero := by
  rw [g1Uncompress_value]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  by_cases hs : b.size ≠ 48
  · rw [ite_eq_left hs]; exact Or.inl rfl
  rw [ite_eq_right hs]
  by_cases h1 : (!decide ((b[0]?.getD 0) &&& 128 ≠ 0)) = true
  · rw [ite_eq_left h1]; exact Or.inl rfl
  rw [ite_eq_right h1, ite_eq_left h64]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem Eth.G1.g1J_ofA (p : G1A) (hp : p.Reduced) : g1J (G1.ofA p) = p.toJ := by
  funext i
  fin_cases i <;> simp [g1J, G1.ofA, G1A.toJ, EthLib.Cryptography.Bls.Fp.one,
    EthLib.Cryptography.Bls.Fp.ofNat, Fin.ofNat, Nat.mod_eq_of_lt (modulus_eq ▸ hp.1),
    Nat.mod_eq_of_lt (modulus_eq ▸ hp.2)]

theorem Eth.G1.isInfinity_ofA (p : G1A) : (G1.ofA p).isInfinity = false := by
  simp [G1.ofA, EthLib.Cryptography.Bls.G1.isInfinity, EthLib.Cryptography.Bls.Fp.isZero,
    EthLib.Cryptography.Bls.Fp.one]

/-- EthLib's subgroup check of a point of `E` is the runtime's: `[r]P = O`. -/
theorem Eth.G1.inSubgroup_ofA {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    EthLib.Cryptography.Bls.G1.inSubgroup (G1.ofA p) = p.inSubgroup := by
  have hn' : E1.Nonsingular (g1J (G1.ofA p)) := by rw [g1J_ofA p hp]; exact hn
  rw [Bool.eq_iff_iff, G1A.inSubgroup_iff hp hn, EthLib.Cryptography.Bls.G1.inSubgroup,
    isInfinity_ofA, ite_eq_right Bool.false_ne_true]
  obtain ⟨hmn, hma⟩ := mulNat_spec EthLib.Cryptography.Bls.Fr.modulus hn'
  rw [isInfinity_iff_zero hmn, hma, g1J_ofA p hp, ← Provenance.R_eq]

theorem Eth.G1.keyValidate_ok_of {b : ByteArray} {p : G1A}
    (h : EthLib.Cryptography.Bls.G1.uncompress b = .ok (G1.ofA p)) :
    EthLib.Cryptography.Bls.G1.keyValidate b =
      if (EthLib.Cryptography.Bls.G1.inSubgroup (G1.ofA p)) then .ok () else .error .notInSubgroup := by
  unfold EthLib.Cryptography.Bls.G1.keyValidate
  rw [h, except_bind_ok]
  simp only [isInfinity_ofA, Bool.false_eq_true, ↓reduceIte]
  by_cases hs : EthLib.Cryptography.Bls.G1.inSubgroup (G1.ofA p) = true
  · rw [ite_eq_right (by simp [hs]), ite_eq_left hs]; rfl
  · rw [ite_eq_left (by simp [hs]), ite_eq_right hs]; rfl

/-- **EthLib's KeyValidate is the runtime's**: it accepts exactly the keys `keyValidate?`
accepts. -/
theorem Eth.G1.keyValidate_isOk (b : ByteArray) :
    (EthLib.Cryptography.Bls.G1.keyValidate b).isOk = (keyValidate? b).isSome := by
  by_cases h64 : (b[0]?.getD 0) &&& 64 = 0
  · have hu := uncompress_eq b h64
    unfold keyValidate?
    rw [G1J.compress_match_1]
    cases hd : g1Decompress? b with
    | none =>
      rw [hd, Option.elim_none] at hu
      unfold EthLib.Cryptography.Bls.G1.keyValidate
      rw [hu, Option.elim_none]; rfl
    | some p =>
      rw [hd, Option.elim_some] at hu
      obtain ⟨hr, hn, -⟩ := g1Decompress?_some hd
      rw [keyValidate_ok_of hu, inSubgroup_ofA hr hn, Option.elim_some,
        G1A.inSubgroupFast_eq hr hn]
      cases p.inSubgroup <;> rfl
  · have hd : g1Decompress? b = none := by
      rw [g1Decompress?_eq]
      by_cases hs : b.size ≠ 48
      · rw [ite_eq_left hs]
      rw [ite_eq_right hs]
      by_cases h1 : (b[0]?.getD 0) &&& 128 = 0
      · rw [ite_eq_left h1]
      rw [ite_eq_right h1, ite_eq_left h64]
    have hk : keyValidate? b = none := by
      unfold keyValidate?; rw [G1J.compress_match_1, hd, Option.elim_none]
    rw [hk]
    unfold EthLib.Cryptography.Bls.G1.keyValidate
    rcases uncompress_inf b h64 with h | h <;> rw [h] <;> rfl

/-- What `keyValidate?` accepts, EthLib's `G1.uncompress` decodes to the same point. -/
theorem Eth.G1.uncompress_of_keyValidate? {b : ByteArray} {p : G1A} (h : keyValidate? b = some p) :
    EthLib.Cryptography.Bls.G1.uncompress b = .ok (G1.ofA p) := by
  have hd := (keyValidate?_some h).1
  obtain ⟨-, -, h64, -⟩ := g1Decompress?_parts hd
  rw [uncompress_eq b h64, hd, Option.elim_some]

/-! ## EthLib's `G1.compress` -/

value_eq g1Compress_value : EthLib.Cryptography.Bls.G1.compress

set_option linter.auxLemma false in
theorem g1Compress_match_1 {β : Type} (x : Fp × Fp) (f : Fp → Fp → β) :
    EthLib.Cryptography.Bls.G1.compress.match_1 (fun _ => β) x f = f x.1 x.2 := by
  cases x; rfl

theorem dite0_size (b : ByteArray) (v : UInt8) :
    (if h : 0 < b.size then b.set 0 v h else b).size = b.size := by
  split
  · exact size_set0 _ _ _
  · rfl

theorem dite0_getD (b : ByteArray) (v : UInt8) (j : ℕ) (hb : 0 < b.size) :
    (if h : 0 < b.size then b.set 0 v h else b)[j]?.getD 0 = if j = 0 then v else b[j]?.getD 0 := by
  rw [dite_eq_left hb, set0_getD]

theorem size_toBytesBE (x : Fp) : x.toBytesBE.size = 48 := by
  unfold EthLib.Cryptography.Bls.Fp.toBytesBE
  exact Array.size_ofFn

theorem toBytesBE_getD (x : Fp) {i : ℕ} (hi : i < 48) :
    (x.toBytesBE)[i]?.getD 0 = (x.val >>> (8 * (48 - 1 - i))).toUInt8 := by
  rw [getElem?_pos _ i (by rw [size_toBytesBE]; exact hi), Option.getD_some]
  unfold EthLib.Cryptography.Bls.Fp.toBytesBE
  rw [ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn, uint8_ofNat_and, Nat.mul_comm]

/-- **EthLib's `G1.compress` is the runtime's**, on a point other than the identity: the
compression of its affine point. -/
theorem Eth.G1.compress_eq {P : EthLib.Cryptography.Bls.G1} (hi : P.isInfinity = false) :
    EthLib.Cryptography.Bls.G1.compress P =
      (⟨P.toAffine.1.val, P.toAffine.2.val⟩ : G1A).compress := by
  rw [g1Compress_value]
  simp (config := { iota := false, zeta := false, beta := true, proj := false, decide := false })
    only [g1Compress_match_1]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  delta_private
  rw [hi]
  generalize P.toAffine.1 = x
  generalize P.toAffine.2 = y
  rw [ite_eq_right Bool.false_ne_true, signBit_eq]
  have hT : 0 < x.toBytesBE.size := by rw [size_toBytesBE]; decide
  have hT1 : 0 < (if h : 0 < x.toBytesBE.size then x.toBytesBE.set 0 (x.toBytesBE[0]?.getD 0 ||| 128) h
      else x.toBytesBE).size := by rw [dite0_size]; exact hT
  have hc0 : ∀ v : UInt8, (⟨x.val, y.val⟩ : G1A).compress[0]?.getD 0 =
      ((x.val >>> 376).toUInt8 ||| (0x80 ||| (if fLarge y.val then 0x20 else 0))) := fun _ => by
    rw [G1A.compress, natBe_getD _ _ _ (by decide : 0 < 48)]; rfl
  have hsz : (⟨x.val, y.val⟩ : G1A).compress.size = 48 := by rw [G1A.compress, size_natBe]
  by_cases hf : fLarge y.val = true
  · rw [ite_eq_left hf, Id.run_pure]
    apply byteArray_ext
    · rw [dite0_size, dite0_size, size_toBytesBE, hsz]
    · intro i hi
      rw [dite0_size, dite0_size, size_toBytesBE] at hi
      rw [dite0_getD _ _ _ hT1]
      by_cases hz : i = 0
      · subst hz
        rw [ite_eq_left rfl, dite0_getD _ _ _ hT, ite_eq_left rfl, hc0 0,
          toBytesBE_getD _ (by decide), ite_eq_left hf, UInt8.or_assoc]
      · rw [ite_eq_right hz, dite0_getD _ _ _ hT, ite_eq_right hz, toBytesBE_getD _ hi,
          G1A.compress, natBe_getD _ _ _ hi, ite_eq_right hz]
  · rw [ite_eq_right hf, Id.run_pure]
    apply byteArray_ext
    · rw [dite0_size, size_toBytesBE, hsz]
    · intro i hi
      rw [dite0_size, size_toBytesBE] at hi
      rw [dite0_getD _ _ _ hT]
      by_cases hz : i = 0
      · subst hz
        rw [ite_eq_left rfl, hc0 0, toBytesBE_getD _ (by decide), ite_eq_right hf, UInt8.or_zero]
      · rw [ite_eq_right hz, toBytesBE_getD _ hi, G1A.compress, natBe_getD _ _ _ hi,
          ite_eq_right hz]

/-! ## EthLib's `G2.uncompress` -/

/-- EthLib's `Fp.fromBytesBE` of 48 bytes: their big-endian number, when below `p`. -/
theorem fromBytesBE_toOption (c : ByteArray) (hs : c.size = 48) :
    (Fp.fromBytesBE c).toOption = if h : beNat c 0 48 < P then some ⟨_, h⟩ else none := by
  unfold Fp.fromBytesBE
  rw [ite_eq_right (by rw [hs]; exact fun h => h rfl)]
  simp only [bytesBEToNat_eq, hs]
  by_cases hlt : beNat c 0 48 < P
  · rw [dite_eq_left (show beNat c 0 48 < Fp.modulus from hlt), dite_eq_left hlt]; rfl
  · rw [dite_eq_right (show ¬beNat c 0 48 < Fp.modulus from hlt), dite_eq_right hlt]; rfl

theorem extract_getD' (u : ByteArray) {s e i : ℕ} (hi : i < e - s) (hs : e ≤ u.size) :
    (u.extract s e)[i]?.getD 0 = u[s + i]?.getD 0 := by
  have h1 : i < (u.extract s e).size := by rw [ByteArray.size_extract]; omega
  rw [getElem?_pos _ i h1, getElem?_pos u (s + i) (by omega), Option.getD_some, Option.getD_some,
    ByteArray.getElem_extract]

set_option linter.auxLemma false in
theorem g2Uncompress_match_3 {β : Type}
    (x y : Except EthLib.Cryptography.Bls.BlsError Fp) (f : Fp → Fp → β) (g : β) :
    EthLib.Cryptography.Bls.G2.uncompress.match_3 (fun _ _ => β) x y f (fun _ _ => g) =
      x.toOption.elim g fun a => y.toOption.elim g fun c => f a c := by
  cases x <;> cases y <;> rfl

set_option linter.auxLemma false in
theorem g2Uncompress_match_1 {β : Type}
    (x : Except EthLib.Cryptography.Bls.BlsError EthLib.Cryptography.Bls.Fp2) (g : β)
    (f : EthLib.Cryptography.Bls.Fp2 → β) :
    EthLib.Cryptography.Bls.G2.uncompress.match_1 (fun _ => β) x (fun _ => g) f =
      x.toOption.elim g f := by
  cases x <;> rfl

value_eq g2Uncompress_value : EthLib.Cryptography.Bls.G2.uncompress

theorem Fp2.toEth_ofEth (a : EthLib.Cryptography.Bls.Fp2) : (ofEth a).toEth = a := by
  obtain ⟨a0, a1⟩ := a
  simp only [Fp2.toEth, ofEth, fp_ofNat_val]

theorem Eth.signBit2_eq (y : EthLib.Cryptography.Bls.Fp2) :
    EthLib.Cryptography.Bls.Fp2.signBit y = (ofEth y).large := by
  unfold EthLib.Cryptography.Bls.Fp2.signBit Fp2.large
  simp only [ofEth, EthLib.Cryptography.Bls.Fp.isZero, signBit_eq]
  by_cases h : y.c1.val = 0 <;> simp [h]

/-- With the identity flag clear, EthLib's `G2.uncompress` is the runtime's `g2Decompress?`, as
EthLib points `(x, y, 1)`. -/
theorem Eth.G2.uncompress_eq (b : ByteArray) (h64 : (b[0]?.getD 0) &&& 64 = 0) :
    EthLib.Cryptography.Bls.G2.uncompress b =
      (g2Decompress? b).elim (.error .invalidG2Point) fun q => .ok (G2.ofA q) := by
  rw [g2Uncompress_value, g2Decompress?_eq]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  simp (config := { iota := false, zeta := false, beta := true, proj := false, decide := false })
    only [g2Uncompress_match_3, g2Uncompress_match_1]
  delta_private
  by_cases hs : b.size ≠ 96
  · rw [ite_eq_left hs, ite_eq_left hs]; rfl
  rw [ite_eq_right hs, ite_eq_right hs]
  by_cases h1 : (b[0]?.getD 0) &&& 128 = 0
  · rw [ite_eq_left (by simp [h1]), ite_eq_left h1]; rfl
  rw [ite_eq_right (by simp [h1]), ite_eq_right h1, ite_eq_right (fun h => h h64),
    ite_eq_right (fun h => h h64)]
  have hs' : b.size = 96 := by omega
  have hb0 : 0 < b.size := by omega
  have hd : (if h : 0 < b.size then b.set 0 ((b[0]?.getD 0) &&& 31) h else b).size = 96 := by
    rw [dite0_size, hs']
  have e1 : (Fp.fromBytesBE ((if h : 0 < b.size then b.set 0 ((b[0]?.getD 0) &&& 31) h else b).extract
      0 48)).toOption = if h : beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat < P then some ⟨_, h⟩
      else none := by
    rw [fromBytesBE_toOption _ (by rw [ByteArray.size_extract, hd]; rfl)]
    have : beNat ((if h : 0 < b.size then b.set 0 ((b[0]?.getD 0) &&& 31) h else b).extract 0 48)
        0 48 = beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat := by
      rw [beNat_succ, extract_getD' _ (by decide) (by rw [hd]; decide), dite0_getD _ _ _ hb0,
        ite_eq_left rfl]
      simp only [Nat.zero_mul, Nat.zero_add]
      apply beNat_congr
      intro i hi
      rw [extract_getD' _ (by omega) (by rw [hd]; decide), dite0_getD _ _ _ hb0,
        ite_eq_right (by omega), Nat.zero_add]
    simp only [this]
  have e0 : (Fp.fromBytesBE ((if h : 0 < b.size then b.set 0 ((b[0]?.getD 0) &&& 31) h else b).extract
      48 96)).toOption = if h : beNat b 48 48 < P then some ⟨_, h⟩ else none := by
    rw [fromBytesBE_toOption _ (by rw [ByteArray.size_extract, hd]; rfl)]
    have : beNat ((if h : 0 < b.size then b.set 0 ((b[0]?.getD 0) &&& 31) h else b).extract 48 96)
        0 48 = beNat b 48 48 := by
      apply beNat_congr
      intro i hi
      rw [extract_getD' _ (by omega) (by rw [hd]), dite0_getD _ _ _ hb0, ite_eq_right (by omega),
        Nat.zero_add]
    simp only [this]
  rw [e1, e0]
  generalize beNat b 1 47 ((b[0]?.getD 0) &&& 31).toNat = X1
  generalize beNat b 48 48 = X0
  by_cases h1 : X1 < P
  · by_cases h0 : X0 < P
    · rw [dite_eq_left h1, dite_eq_left h0, Option.elim_some, Option.elim_some,
        ite_eq_right (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; omega)]
      have hx : (⟨X0, X1⟩ : Fp2) = ofEth ⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ := rfl
      have hr : ((⟨X0, X1⟩ : Fp2).sqr.mul ⟨X0, X1⟩).add bTwist = ofEth (⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ *
          ⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ * ⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ + EthLib.Cryptography.Bls.G2.bTwist) := by
        rw [hx, Fp2.sqr_ofEth, Fp2.mul_ofEth, Provenance.bTwist_eq, Fp2.add_ofEth]
      rw [hr, sqrt?_ofEth]
      generalize (EthLib.Cryptography.Bls.Fp2.sqrt (⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ * ⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ *
        ⟨⟨X0, h0⟩, ⟨X1, h1⟩⟩ + EthLib.Cryptography.Bls.G2.bTwist)).toOption = o
      cases o with
      | none => rfl
      | some yP =>
        rw [Option.map_some, Option.elim_some, Option.elim_some, Option.elim_some]
        unfold G2.ofA
        rw [hx, Fp2.toEth_ofEth, signBit2_eq]
        congr 2
        by_cases hsg : (b[0]?.getD 0) &&& 32 ≠ 0
        · cases hf : (ofEth yP).large
          · rw [ite_eq_right (by simp [hsg]), ite_eq_right (by simp [hsg]), Fp2.neg_ofEth,
              Fp2.toEth_ofEth]
          · rw [ite_eq_left (by simp [hsg]), ite_eq_left (by simp [hsg]), Fp2.toEth_ofEth]
        · cases hf : (ofEth yP).large
          · rw [ite_eq_left (by simp [hsg]), ite_eq_left (by simp [hsg]), Fp2.toEth_ofEth]
          · rw [ite_eq_right (by simp [hsg]), ite_eq_right (by simp [hsg]), Fp2.neg_ofEth,
              Fp2.toEth_ofEth]
    · rw [dite_eq_left h1, dite_eq_right h0, Option.elim_some, Option.elim_none,
        ite_eq_left (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]; rfl
  · rw [dite_eq_right h1, Option.elim_none,
      ite_eq_left (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]; rfl

/-- EthLib decodes the identity's canonical encoding to a point at infinity, by the kernel. -/
theorem G2.uncompress_infinityBytes :
    (EthLib.Cryptography.Bls.G2.uncompress EthLib.Cryptography.Bls.G2.infinityBytes).toOption.map
      (·.isInfinity) = some true := by
  decide +kernel

theorem foldl_allZero (f : ℕ → UInt8) : ∀ (l : List ℕ) (s : Bool),
    l.foldl (fun s i => if f i ≠ 0 then false else s) s = true → s = true ∧ ∀ i ∈ l, f i = 0
  | [], s, h => ⟨h, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, s, h => by
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_allZero f l _ h
    by_cases ha : f a ≠ 0
    · rw [ite_eq_left ha] at h1; cases h1
    · rw [ite_eq_right ha] at h1
      refine ⟨h1, fun i hi => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact not_not.mp ha
      · exact h2 i hi

theorem forIn_allZero (f : ℕ → UInt8) (l : List ℕ) (s : Bool) :
    (do
      let r ← forIn l s fun i s => if ¬f i = 0 then pure (ForInStep.yield false)
        else pure (ForInStep.yield s)
      pure r : Id Bool) = l.foldl (fun s i => if f i ≠ 0 then false else s) s := by
  have : (fun i (s : Bool) => if ¬f i = 0 then (pure (ForInStep.yield false) : Id _)
      else pure (ForInStep.yield s)) =
      fun i s => pure (ForInStep.yield (if f i ≠ 0 then false else s)) := by
    funext i s; split <;> rfl
  rw [this, List.forIn_pure_yield_eq_foldl]
  rfl

theorem G2.infinityBytes_bytes :
    EthLib.Cryptography.Bls.G2.infinityBytes.size = 96 ∧
      EthLib.Cryptography.Bls.G2.infinityBytes[0]?.getD 0 = 192 ∧
      ∀ i : Fin 96, i.val ≠ 0 → EthLib.Cryptography.Bls.G2.infinityBytes[i.val]?.getD 0 = 0 := by
  decide +kernel

/-- With the identity flag set, EthLib's `G2.uncompress` errs, or the bytes are the identity's
canonical encoding, which it decodes to the identity. -/
theorem Eth.G2.uncompress_inf (b : ByteArray) (h64 : (b[0]?.getD 0) &&& 64 ≠ 0) :
    EthLib.Cryptography.Bls.G2.uncompress b = .error .invalidG2Point ∨
      b = EthLib.Cryptography.Bls.G2.infinityBytes := by
  rw [g2Uncompress_value]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  delta_private
  by_cases hs : b.size ≠ 96
  · rw [ite_eq_left hs]; exact Or.inl rfl
  rw [ite_eq_right hs]
  by_cases h1 : (!decide ((b[0]?.getD 0) &&& 128 ≠ 0)) = true
  · rw [ite_eq_left h1]; exact Or.inl rfl
  rw [ite_eq_right h1, ite_eq_left h64]
  split
  · exact Or.inl rfl
  · rename_i hc
    right
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Bool.not_eq_false,
      ne_eq, not_not] at hc
    obtain ⟨⟨-, h192⟩, hz⟩ := hc
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] at hz
    have e := forIn_allZero (fun i => b[i]?.getD 0) (List.range' 1 ((b.size - 1 + 1 - 1) / 1)) true
    beta_reduce at e
    rw [e] at hz
    obtain ⟨-, hzero⟩ := foldl_allZero (fun i => b[i]?.getD 0) _ true hz
    obtain ⟨hsz, h0, hrest⟩ := G2.infinityBytes_bytes
    apply byteArray_ext (by rw [hsz]; omega)
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0; rw [h0, h192]
    · rw [hzero i (List.mem_range'_1.mpr (by omega)), hrest ⟨i, by omega⟩ hi0]

/-! ## Subgroup checks, the aggregate -/

theorem Eth.G2.g2J_ofA (q : G2A) (hq : q.Reduced) : g2J (G2.ofA q) = q.toJ := by
  funext i
  fin_cases i <;> simp [g2J, G2.ofA, G2A.toJ, Fp2.ofEth_toEth hq.1, Fp2.ofEth_toEth hq.2]

theorem Eth.G2.isInfinity_ofA (q : G2A) : (G2.ofA q).isInfinity = false := by
  simp [G2.ofA, EthLib.Cryptography.Bls.G2.isInfinity, EthLib.Cryptography.Bls.Fp2.isZero,
    EthLib.Cryptography.Bls.Fp2.one, EthLib.Cryptography.Bls.Fp.isZero, EthLib.Cryptography.Bls.Fp.one]

/-- EthLib's subgroup check of a point of `E'` is the runtime's: `[r]Q = O`. -/
theorem Eth.G2.inSubgroup_ofA {q : G2A} (hq : q.Reduced) (hn : E2.Nonsingular q.toJ) :
    EthLib.Cryptography.Bls.G2.inSubgroup (G2.ofA q) = q.inSubgroup := by
  have hn' : E2.Nonsingular (g2J (G2.ofA q)) := by rw [g2J_ofA q hq]; exact hn
  rw [Bool.eq_iff_iff, G2A.inSubgroup_iff hq hn, EthLib.Cryptography.Bls.G2.inSubgroup,
    isInfinity_ofA, ite_eq_right Bool.false_ne_true]
  obtain ⟨hmn, hma⟩ := mulNat_spec EthLib.Cryptography.Bls.Fr.modulus hn'
  rw [isInfinity_iff_zero hmn, hma, g2J_ofA q hq, ← Provenance.R_eq]

/-- Two reduced affine points of `E` standing for the same point are equal. -/
theorem G1A.eq_of_aff {a b : G1A} (ha : a.Reduced) (hb : b.Reduced) (han : E1.Nonsingular a.toJ)
    (hbn : E1.Nonsingular b.toJ) (h : aff1 a.toJ = aff1 b.toJ) : a = b := by
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, by'⟩ := b
  simp only [G1A.toJ] at han hbn h
  rw [Point.toAffine_some han, Point.toAffine_some hbn, Affine.Point.some.injEq] at h
  rw [cast_inj ha.1 hb.1, cast_inj ha.2 hb.2] at h
  exact (G1A.mk.injEq _ _ _ _).mpr h

/-- EthLib's running sum of the keys, with its own formulas, stands for their sum. -/
theorem Eth.G1.foldl_add_spec : ∀ (l : List G1A) (acc : EthLib.Cryptography.Bls.G1),
    E1.Nonsingular (g1J acc) → (∀ p ∈ l, p.Reduced ∧ E1.Nonsingular p.toJ) →
    E1.Nonsingular (g1J (l.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (G1.ofA k)) acc)) ∧
      aff1 (g1J (l.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (G1.ofA k)) acc)) =
        aff1 (g1J acc) + (l.map fun p => aff1 p.toJ).sum
  | [], acc, h, _ => by simp [h]
  | k :: l, acc, h, hl => by
    have hk := hl k List.mem_cons_self
    have hkn : E1.Nonsingular (g1J (G1.ofA k)) := by rw [g1J_ofA k hk.1]; exact hk.2
    obtain ⟨han, haa⟩ := add_spec h hkn
    obtain ⟨h1, h2⟩ := foldl_add_spec l _ han fun p hp => hl p (List.mem_cons_of_mem _ hp)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, haa, g1J_ofA k hk.1, List.map_cons, List.sum_cons, add_assoc]

/-! ## EthLib's pairing check -/

/-- EthLib's `pairingCheck` accumulator: the product of the conjugated Miller loops over the
pairs with no identity point. -/
noncomputable def Eth.pairingAcc
    (pairs : Array (EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2)) :
    EthLib.Cryptography.Bls.Fp12 :=
  pairs.foldl (fun acc pq => if (pq.1.isInfinity || pq.2.isInfinity) = true then acc else
    acc * (EthLib.Cryptography.Bls.millerLoop EthLib.Cryptography.Bls.blsX
      (EthLib.Cryptography.Bls.Embedded.ofG2 pq.2)
      (EthLib.Cryptography.Bls.Embedded.ofG1 pq.1)).conjugate) EthLib.Cryptography.Bls.Fp12.one

set_option linter.auxLemma false in
theorem pairingCheck_match_1 {β : Type}
    (x : EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2)
    (f : EthLib.Cryptography.Bls.G1 → EthLib.Cryptography.Bls.G2 → β) :
    EthLib.Cryptography.Bls.pairingCheck.match_1 (fun _ => β) x f = f x.1 x.2 := by
  cases x; rfl

value_eq ethPairingCheck_value : EthLib.Cryptography.Bls.pairingCheck

/-- EthLib's `pairingCheck` is its naive final exponentiation of `pairingAcc`. -/
theorem Eth.pairingCheck_eq
    (pairs : Array (EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2)) :
    EthLib.Cryptography.Bls.pairingCheck pairs =
      (EthLib.Cryptography.Bls.finalExponentiation (pairingAcc pairs)).isOne := by
  rw [ethPairingCheck_value]
  simp (config := { iota := false, zeta := false, beta := true, proj := false, decide := false })
    only [pairingCheck_match_1]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  have hb : (fun (x : EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2)
      (s : EthLib.Cryptography.Bls.Fp12) =>
      if (x.1.isInfinity || x.2.isInfinity) = true then (pure (ForInStep.yield s) : Id _) else
        pure (ForInStep.yield (s * (EthLib.Cryptography.Bls.millerLoop EthLib.Cryptography.Bls.blsX
          (EthLib.Cryptography.Bls.Embedded.ofG2 x.2)
          (EthLib.Cryptography.Bls.Embedded.ofG1 x.1)).conjugate))) =
      fun x s => pure (ForInStep.yield (if (x.1.isInfinity || x.2.isInfinity) = true then s else
        s * (EthLib.Cryptography.Bls.millerLoop EthLib.Cryptography.Bls.blsX
          (EthLib.Cryptography.Bls.Embedded.ofG2 x.2)
          (EthLib.Cryptography.Bls.Embedded.ofG1 x.1)).conjugate)) := by
    funext x s; split <;> rfl
  rw [hb, ← Array.forIn_toList, List.forIn_pure_yield_eq_foldl, Array.foldl_toList]
  rfl

theorem Eth.ofG2_congr {q q' : EthLib.Cryptography.Bls.G2} (hi : q.isInfinity = q'.isInfinity)
    (ha : q.toAffine = q'.toAffine) :
    EthLib.Cryptography.Bls.Embedded.ofG2 q = EthLib.Cryptography.Bls.Embedded.ofG2 q' := by
  unfold EthLib.Cryptography.Bls.Embedded.ofG2; rw [hi, ha]

/-! ## The two Miller loops -/

theorem Eth.fp2_mul_one_inverse (a : EthLib.Cryptography.Bls.Fp2) :
    a * (EthLib.Cryptography.Bls.Fp2.one.inverse * EthLib.Cryptography.Bls.Fp2.one.inverse) = a ∧
      a * (EthLib.Cryptography.Bls.Fp2.one.inverse * EthLib.Cryptography.Bls.Fp2.one.inverse *
        EthLib.Cryptography.Bls.Fp2.one.inverse) = a := by
  constructor <;>
  · rw [← Fp2.ofEth_inj, ← Fp2.toGF_inj (Fp2.reduced_ofEth _) (Fp2.reduced_ofEth _)]
    simp only [Fp2.toGF_ofEth_mul, Fp2.toGF_ofEth_inverse, toGF_ofEth_one, inv_one, mul_one]

theorem Eth.fp_one_inverse_val :
    ((EthLib.Cryptography.Bls.Fp.one.inverse.val : ℕ) : GFp) = 1 := by
  rw [EthLib.Cryptography.Bls.Fp.inverse, cast_val_powNat]
  simp [EthLib.Cryptography.Bls.Fp.one]

/-- EthLib's affine point of `G1.ofA p` is `p`'s coordinates, read in `𝔽_p`. -/
theorem Eth.G1.toAffine_ofA (p : G1A) :
    (((G1.ofA p).toAffine.1.val : ℕ) : GFp) = p.x ∧
      (((G1.ofA p).toAffine.2.val : ℕ) : GFp) = p.y := by
  unfold EthLib.Cryptography.Bls.G1.toAffine
  rw [ite_eq_right (by
    rw [show (G1.ofA p).z.isZero = false from rfl]; exact Bool.false_ne_true)]
  refine ⟨?_, ?_⟩ <;>
    simp only [G1.ofA, cast_val_mul, cast_val_ofNat, Eth.fp_one_inverse_val, mul_one]

/-- EthLib's affine point of `G2.ofA q` is `q`'s coordinates. -/
theorem Eth.G2.toAffine_ofA_eq (q : G2A) : (G2.ofA q).toAffine = (q.x.toEth, q.y.toEth) := by
  unfold G2.ofA EthLib.Cryptography.Bls.G2.toAffine
  rw [ite_eq_right (by rw [show EthLib.Cryptography.Bls.Fp2.one.isZero = false from rfl]; exact
    Bool.false_ne_true)]
  simp only [(fp2_mul_one_inverse _).1, (fp2_mul_one_inverse _).2]

/-- EthLib's embedding of a runtime affine point `p` of `E` into `E(𝔽_{p¹²})` stands for `p`. -/
theorem Eth.embeds_ofG1 (p : G1A) :
    Embeds (EthLib.Cryptography.Bls.Embedded.ofG1 (G1.ofA p)) p := by
  obtain ⟨hx, hy⟩ := Eth.G1.toAffine_ofA p
  unfold EthLib.Cryptography.Bls.Embedded.ofG1
  rw [Eth.G1.isInfinity_ofA, ite_eq_right Bool.false_ne_true]
  constructor
  · show (ofEth12 ⟨EthLib.Cryptography.Bls.Fp6.ofFp2 (EthLib.Cryptography.Bls.Fp2.ofFp
      (G1.ofA p).toAffine.1), EthLib.Cryptography.Bls.Fp6.zero⟩).toGF = _
    rw [toGF_ofEth12_ofFp2, toGF_ofEth_ofFp, hx]
  · show (ofEth12 ⟨EthLib.Cryptography.Bls.Fp6.ofFp2 (EthLib.Cryptography.Bls.Fp2.ofFp
      (G1.ofA p).toAffine.2), EthLib.Cryptography.Bls.Fp6.zero⟩).toGF = _
    rw [toGF_ofEth12_ofFp2, toGF_ofEth_ofFp, hy]

/-- EthLib's untwist of a reduced runtime affine point `q` of `E'` into `E(𝔽_{p¹²})` is
`(x·w⁻², y·w⁻³)`. -/
theorem Eth.untwists_ofG2 {q : G2A} (hq : q.Reduced) :
    Untwists (EthLib.Cryptography.Bls.Embedded.ofG2 (G2.ofA q)) q.x.toGF q.y.toGF := by
  unfold EthLib.Cryptography.Bls.Embedded.ofG2
  rw [Eth.G2.isInfinity_ofA, ite_eq_right Bool.false_ne_true, Eth.G2.toAffine_ofA_eq]
  refine ⟨rfl, ?_, ?_⟩
  · show (ofEth12 (⟨EthLib.Cryptography.Bls.Fp6.ofFp2 q.x.toEth, EthLib.Cryptography.Bls.Fp6.zero⟩ *
      EthLib.Cryptography.Bls.Embedded.wInv2)).toGF = _
    rw [toGF_ofEth12_mul, toGF_ofEth12_ofFp2, toGF_wInv2, Fp2.ofEth_toEth hq.1]
  · show (ofEth12 (⟨EthLib.Cryptography.Bls.Fp6.ofFp2 q.y.toEth, EthLib.Cryptography.Bls.Fp6.zero⟩ *
      EthLib.Cryptography.Bls.Embedded.wInv3)).toGF = _
    rw [toGF_ofEth12_mul, toGF_ofEth12_ofFp2, toGF_wInv3, Fp2.ofEth_toEth hq.2]

/-- EthLib's accumulator over runtime affine points is the product of its conjugated Miller loops
(no point is the identity). -/
theorem Eth.pairingAcc_toGF (ps : List (G1A × G2A)) :
    (ofEth12 (pairingAcc (ps.map fun pq => (G1.ofA pq.1, G2.ofA pq.2)).toArray)).toGF =
      (ps.map fun pq => star (ofEth12 (EthLib.Cryptography.Bls.millerLoop
        EthLib.Cryptography.Bls.blsX (EthLib.Cryptography.Bls.Embedded.ofG2 (G2.ofA pq.2))
        (EthLib.Cryptography.Bls.Embedded.ofG1 (G1.ofA pq.1)))).toGF).prod := by
  unfold pairingAcc
  simp only [List.foldl_toArray', List.foldl_map, G1.isInfinity_ofA, G2.isInfinity_ofA,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  suffices h : ∀ (l : List (G1A × G2A)) (a : EthLib.Cryptography.Bls.Fp12),
      (ofEth12 (l.foldl (fun acc pq => acc * (EthLib.Cryptography.Bls.millerLoop
        EthLib.Cryptography.Bls.blsX (EthLib.Cryptography.Bls.Embedded.ofG2 (G2.ofA pq.2))
        (EthLib.Cryptography.Bls.Embedded.ofG1 (G1.ofA pq.1))).conjugate) a)).toGF =
      (ofEth12 a).toGF * (l.map fun pq => star (ofEth12 (EthLib.Cryptography.Bls.millerLoop
        EthLib.Cryptography.Bls.blsX (EthLib.Cryptography.Bls.Embedded.ofG2 (G2.ofA pq.2))
        (EthLib.Cryptography.Bls.Embedded.ofG1 (G1.ofA pq.1)))).toGF).prod by
    rw [h, toGF_ofEth12_one, one_mul]
  intro l
  induction l with
  | nil => intro a; simp
  | cons pq l ih =>
    intro a
    rw [List.foldl_cons, ih, toGF_ofEth12_mul, toGF_ofEth12_conjugate, List.map_cons,
      List.prod_cons, mul_assoc]

/-- **The runtime's Miller loop and EthLib's agree after the final exponentiation, on G2**: for
every list of pairs `(P, Q)`, `P` any runtime `G1A` (only its coordinates mod `p` are used) and
`Q` a reduced point of `E'` with `[r]Q = O`, the runtime's Miller value `millerLoop ps` and
EthLib's naive `pairingCheck` accumulator over the same pairs, `P` and `Q` as EthLib points
`(x, y, 1)`, give the same value raised to `(p¹²−1)/r` in `𝔽_{p¹²}`. Once
H_vec's hypothesis, now a theorem (`millerLoopsCube`): the two loops' lines differ by factors
`s·w³`, `s` in `𝔽_{p²}`, which that power kills, as long as neither loop meets an exceptional
case, which `[r]Q = O` rules out (`LeanLightProofs.Bls.Miller`). Off G2 the statement fails: for `Q`
of order 13 EthLib's addition meets `T = −Q` and computes a point off the curve, where the
runtime's reaches the identity. The name is LC4b's, when the equation also carried the runtime's
final exponentiation (`FinalExpCube` for each list); that part is proved (`finalExp_toGF`), and
this statement is `FinalExpCube` for each list of such pairs (`millerLoopsCube_iff`). -/
def MillerLoopsCube : Prop :=
  ∀ ps : List (G1A × G2A), (∀ pq ∈ ps, pq.2.Reduced ∧ E2.Nonsingular pq.2.toJ ∧
    R • aff2 pq.2.toJ = 0) →
    (millerLoop ps).toGF ^ finalExpExp =
      (ofEth12 (Eth.pairingAcc
        (ps.map fun pq => (Eth.G1.ofA pq.1, Eth.G2.ofA pq.2)).toArray)).toGF ^ finalExpExp

/-- **H_vec's Miller-loop equation, proved**: `MillerLoopsCube` holds (`millerLoop_pow_eq`,
`Eth.pairingAcc_toGF`). -/
theorem millerLoopsCube : MillerLoopsCube := by
  intro ps hps
  rw [Eth.pairingAcc_toGF]
  exact millerLoop_pow_eq ps (fun pq => (EthLib.Cryptography.Bls.Embedded.ofG1 (Eth.G1.ofA pq.1),
      EthLib.Cryptography.Bls.Embedded.ofG2 (Eth.G2.ofA pq.2)))
    fun pq hpq => ⟨(hps pq hpq).1, (hps pq hpq).2.1, (hps pq hpq).2.2, Eth.embeds_ofG1 pq.1,
      Eth.untwists_ofG2 (hps pq hpq).1⟩

/-- `MillerLoopsCube` is LC4b's hypothesis, `FinalExpCube` for each list of pairs whose G2 points
are reduced points of `E'` with `[r]Q = O`, now that the runtime's final exponentiation is proved
(`finalExpCube_iff`, with the Miller loop's value reduced, `reduced_millerLoop`). -/
theorem millerLoopsCube_iff : MillerLoopsCube ↔
    ∀ ps : List (G1A × G2A), (∀ pq ∈ ps, pq.2.Reduced ∧ E2.Nonsingular pq.2.toJ ∧
      R • aff2 pq.2.toJ = 0) →
      FinalExpCube (millerLoop ps)
        (Eth.pairingAcc (ps.map fun pq => (Eth.G1.ofA pq.1, Eth.G2.ofA pq.2)).toArray) :=
  forall_congr' fun ps => imp_congr_right fun _ =>
    (finalExpCube_iff (reduced_millerLoop ps) _).symm

/-- **The runtime's pairing check is EthLib's** on the same points, as EthLib points `(x, y, 1)`,
for every list of pairs `(P, Q)`, `P` any runtime `G1A` and `Q` a reduced point of `E'` with
`[r]Q = O` (`millerLoopsCube`). -/
theorem pairingCheck_eq_eth (ps : List (G1A × G2A))
    (hps : ∀ pq ∈ ps, pq.2.Reduced ∧ E2.Nonsingular pq.2.toJ ∧ R • aff2 pq.2.toJ = 0) :
    pairingCheck ps = EthLib.Cryptography.Bls.pairingCheck
      (ps.map fun pq => (Eth.G1.ofA pq.1, Eth.G2.ofA pq.2)).toArray := by
  rw [Eth.pairingCheck_eq, Bool.eq_iff_iff,
    ← finalExp_isOne_iff ((millerLoopsCube_iff.mp millerLoopsCube) ps hps)]
  rfl

/-! ## EthLib's loop over the keys -/

/-- EthLib's loop over the keys, as a recursion: KeyValidate each, summing them with EthLib's
`G1.add`; the first that fails stops it with `some false`. -/
def Eth.keyLoop : List ByteArray → EthLib.Cryptography.Bls.G1 → Option Bool × EthLib.Cryptography.Bls.G1
  | [], acc => (none, acc)
  | pk :: l, acc => (keyValidate? pk).elim (some false, acc) fun k =>
      keyLoop l (EthLib.Cryptography.Bls.G1.add acc (Eth.G1.ofA k))

theorem Eth.forIn_keyLoop
    (body : ByteArray → Option Bool × EthLib.Cryptography.Bls.G1 →
      Id (ForInStep (Option Bool × EthLib.Cryptography.Bls.G1)))
    (hbody : ∀ pk acc, body pk (none, acc) = (keyValidate? pk).elim
      (pure (.done (some false, acc))) fun k =>
        pure (.yield (none, EthLib.Cryptography.Bls.G1.add acc (G1.ofA k)))) :
    ∀ (l : List ByteArray) (acc : EthLib.Cryptography.Bls.G1),
      forIn l (none, acc) body = keyLoop l acc
  | [], acc => rfl
  | pk :: l, acc => by
    rw [List.forIn_cons, hbody, keyLoop]
    cases keyValidate? pk with
    | none => rfl
    | some k => exact forIn_keyLoop body hbody l _

theorem Eth.keyLoop_none : ∀ (l : List ByteArray) (acc : EthLib.Cryptography.Bls.G1),
    (keyLoop l acc).1 = none ↔ (l.mapM keyValidate?).isSome
  | [], acc => by simp [keyLoop]
  | pk :: l, acc => by
    rw [keyLoop, List.mapM_cons]
    cases keyValidate? pk with
    | none => simp
    | some k =>
      rw [Option.elim_some, keyLoop_none l]
      cases l.mapM keyValidate? <;> simp

theorem Eth.keyLoop_sum : ∀ (l : List ByteArray) (acc : EthLib.Cryptography.Bls.G1) (ks : List G1A),
    l.mapM keyValidate? = some ks →
      (keyLoop l acc).2 = ks.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (G1.ofA k)) acc
  | [], acc, ks, h => by simp at h; subst h; rfl
  | pk :: l, acc, ks, h => by
    rw [List.mapM_cons] at h
    cases hk : keyValidate? pk with
    | none => simp [hk] at h
    | some k =>
      cases hl : l.mapM keyValidate? with
      | none => simp [hk, hl] at h
      | some ks' =>
        simp only [hk, hl, Option.bind_some, Option.pure_def, Option.some.injEq,
          Option.bind_eq_bind] at h
        subst h
        rw [keyLoop, hk, Option.elim_some, keyLoop_sum l _ ks' hl, List.foldl_cons]

theorem Eth.keyLoop_fst : ∀ (l : List ByteArray) (acc : EthLib.Cryptography.Bls.G1),
    (keyLoop l acc).1 = if (l.mapM keyValidate?).isSome then none else some false
  | [], acc => rfl
  | pk :: l, acc => by
    rw [keyLoop, List.mapM_cons]
    cases keyValidate? pk with
    | none => rfl
    | some k =>
      rw [Option.elim_some, keyLoop_fst l]
      cases l.mapM keyValidate? <;> rfl

/-! ## Points in EthLib's form -/

theorem Eth.G1.compress_inf {P : EthLib.Cryptography.Bls.G1} (hi : P.isInfinity = true) :
    EthLib.Cryptography.Bls.G1.compress P = EthLib.Cryptography.Bls.G1.infinityBytes := by
  rw [g1Compress_value]
  beta_reduce
  rw [hi, ite_eq_left rfl]
  rfl

theorem Eth.G1.infinityBytes_eq : EthLib.Cryptography.Bls.G1.infinityBytes = identityBytes 48 := by
  decide +kernel

theorem Eth.G2.infinityBytes_eq : EthLib.Cryptography.Bls.G2.infinityBytes = identityBytes 96 := by
  decide +kernel

theorem Eth.G1.generator_eq : EthLib.Cryptography.Bls.G1.generator = G1.ofA g1Gen := rfl

theorem Eth.G1.neg_ofA {a : G1A} (ha : a.Reduced) :
    EthLib.Cryptography.Bls.G1.neg (G1.ofA a) = G1.ofA a.neg := by
  have hy : (Fp.ofNat a.y).val = a.y := by
    simp [EthLib.Cryptography.Bls.Fp.ofNat, Fin.ofNat, Nat.mod_eq_of_lt (modulus_eq ▸ ha.2)]
  simp only [EthLib.Cryptography.Bls.G1.neg, G1.ofA, G1A.neg]
  congr 1
  conv_rhs => rw [← hy, fneg_val, fp_ofNat_val]

/-- An EthLib point `(x, y, 1)` built from another's affine coordinates has the same affine
coordinates and is not at infinity. -/
theorem Eth.G2.toAffine_ofA (q : EthLib.Cryptography.Bls.G2) :
    (G2.ofA ⟨ofEth q.toAffine.1, ofEth q.toAffine.2⟩).toAffine = q.toAffine := by
  unfold G2.ofA EthLib.Cryptography.Bls.G2.toAffine
  rw [ite_eq_right (by rw [show EthLib.Cryptography.Bls.Fp2.one.isZero = false from rfl]; exact
    Bool.false_ne_true)]
  simp only [Fp2.toEth_ofEth, (fp2_mul_one_inverse _).1, (fp2_mul_one_inverse _).2]

/-- EthLib's accumulator over two pairs depends on the second G2 point only through whether it is
the identity and its embedding (its affine coordinates). -/
theorem Eth.pairingAcc_congr2 (p1 : EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2)
    (z : EthLib.Cryptography.Bls.G1) {q q' : EthLib.Cryptography.Bls.G2}
    (hi : q.isInfinity = q'.isInfinity)
    (ho : EthLib.Cryptography.Bls.Embedded.ofG2 q = EthLib.Cryptography.Bls.Embedded.ofG2 q') :
    pairingAcc #[p1, (z, q)] = pairingAcc #[p1, (z, q')] := by
  unfold pairingAcc
  simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, hi, ho]

theorem Eth.pairingAcc_congr1 (z : EthLib.Cryptography.Bls.G1) {q q' : EthLib.Cryptography.Bls.G2}
    (hi : q.isInfinity = q'.isInfinity)
    (ho : EthLib.Cryptography.Bls.Embedded.ofG2 q = EthLib.Cryptography.Bls.Embedded.ofG2 q') :
    pairingAcc #[(z, q)] = pairingAcc #[(z, q')] := by
  unfold pairingAcc
  simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, hi, ho]

/-- EthLib's accumulator skips a pair whose G2 point is the identity. -/
theorem Eth.pairingAcc_skip (p : EthLib.Cryptography.Bls.G1) {P : EthLib.Cryptography.Bls.G2}
    (hP : P.isInfinity = true) (x : EthLib.Cryptography.Bls.G1 × EthLib.Cryptography.Bls.G2) :
    pairingAcc #[(p, P), x] = pairingAcc #[x] := by
  unfold pairingAcc
  simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, hP, Bool.or_true,
    ↓reduceIte]

theorem idBind {α β : Type} (x : α) (f : α → Id β) : (x >>= f : Id β) = f x := rfl

value_eq ethFav_value : EthLib.Cryptography.Bls.Signatures.fastAggregateVerify

/-- **FastAggregateVerify is EthLib's**, when EthLib's `hash_to_G2(msg)` under Ethereum's DST is
not the identity and the signature is not the identity's canonical encoding: the runtime's
`fastAggregateVerifyBytes`
(IRTF BLS's FastAggregateVerify over the keys' bytes) is EthLib's `fastAggregateVerify`, on every
key list, message and signature. (Both refuse an empty key list. For the identity's encoding see
`fastAggregateVerify_eth_identitySig`.) -/
theorem fastAggregateVerifyBytes_eq_eth (pks : Array ByteArray) (msg sig : ByteArray)
    (hH : ∀ q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
      EthLib.Cryptography.Bls.Signatures.DST = .ok q → q.isInfinity = false)
    (hsig : sig ≠ EthLib.Cryptography.Bls.G2.infinityBytes) :
    fastAggregateVerifyBytes pks msg sig =
      EthLib.Cryptography.Bls.Signatures.fastAggregateVerify pks msg sig := by
  have hrq : H2C.hashToG2? msg ethDst = (EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
      EthLib.Cryptography.Bls.Signatures.DST).toOption.bind Eth.g2Affine? := hashToG2?_eq_eth msg ethDst
  rw [ethFav_value]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false }) only []
  delta_private
  rw [← Array.forIn_toList, Eth.forIn_keyLoop _ (fun pk acc => ?hb)]
  case hb =>
    cases hk : keyValidate? pk with
    | none =>
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate pk).isOk = false := by
        rw [Eth.G1.keyValidate_isOk, hk]; rfl
      rw [ite_eq_left (by simp [hko]), Option.elim_none]
    | some k =>
      obtain ⟨hd, -⟩ := keyValidate?_some hk
      have hsz : pk.size = 48 := (g1Decompress?_parts hd).1
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate pk).isOk = true := by
        rw [Eth.G1.keyValidate_isOk, hk]; rfl
      rw [ite_eq_right (by simp [hsz, hko]), Eth.G1.uncompress_of_keyValidate? hk, Option.elim_some]
  generalize EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg EthLib.Cryptography.Bls.Signatures.DST = rq at hH hrq ⊢
  rw [idBind, Eth.keyLoop_fst]
  unfold fastAggregateVerifyBytes
  rw [Array.mapM_eq_mapM_toList]
  have hks := mapM_keyValidate?_mem pks.toList
  have hksub := mapM_keyValidate?_sub pks.toList
  cases hm : pks.toList.mapM keyValidate? with
  | none =>
    by_cases he : pks.isEmpty = true
    · rw [ite_eq_left he]; rfl
    · rw [ite_eq_right he]; rfl
  | some ks =>
    have hks' := hks ks hm
    have hksub' := hksub ks hm
    rw [show (List.toArray <$> some ks) = some ks.toArray from rfl, ite_eq_left (show (some ks).isSome = true from rfl),
      Eth.keyLoop_sum pks.toList _ ks hm]
    dsimp only
    by_cases he : pks.isEmpty = true
    · rw [ite_eq_left he]
      have hl : pks.toList = [] := by simpa using he
      rw [hl] at hm
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
      subst hm
      rfl
    rw [ite_eq_right he, Id.run_pure]
    obtain ⟨hEn, hEa⟩ := Eth.G1.foldl_add_spec ks EthLib.Cryptography.Bls.G1.zero Eth.G1.zero_spec.1 hks'
    rw [Eth.G1.zero_spec.2, zero_add] at hEa
    have hagg := aggregate?_spec ks.toArray (by simpa using hks')
    simp only at hagg
    unfold fastAggregateVerify verifyAggregate
    rw [fastAggregateVerify_match_3]
    revert hagg
    cases aggregate? ks.toArray with
    | none =>
      intro hagg
      have hinf := (Eth.G1.isInfinity_iff_zero hEn).mpr (by rw [hEa]; exact hagg)
      rw [Option.elim_none, Eth.G1.compress_inf hinf, Eth.G1.infinityBytes_eq]
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate (identityBytes 48)).isOk = false := by
        rw [Eth.G1.keyValidate_isOk, keyValidate?_identity]; rfl
      rw [ite_eq_left (by simp [hko])]
    | some a =>
      intro hagg
      obtain ⟨har, han, hae⟩ := hagg
      have hne : Point.toAffine E1 a.toJ ≠ 0 := by
        rw [G1A.toJ, Point.toAffine_some (by rw [← G1A.toJ]; exact han)]
        exact Affine.Point.some_ne_zero _
      have hinf : (List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).isInfinity = false := by
        cases h : (List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).isInfinity
        · rfl
        · exact absurd (by rw [hae, ← hEa]; exact (Eth.G1.isInfinity_iff_zero hEn).mp h) hne
      obtain ⟨hbn, hbe⟩ := Eth.G1.affine_spec hEn hinf
      have ha' : (⟨(List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).toAffine.1.val,
          (List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).toAffine.2.val⟩ : G1A) = a :=
        G1A.eq_of_aff ⟨val_lt _, val_lt _⟩ har hbn han (by
          show Point.toAffine E1 ![_, _, 1] = _
          rw [hbe, hEa, ← hae])
      rw [Eth.G1.compress_eq hinf, ha']
      have hsub : R • Point.toAffine E1 a.toJ = 0 := by
        rw [hae, List.smul_sum, List.map_map]
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hksub' p hp
      have hkv := keyValidate?_compress har han hsub
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate a.compress).isOk = true := by
        rw [Eth.G1.keyValidate_isOk, hkv]; rfl
      have hsz : a.compress.size = 48 := size_natBe _ _ _
      rw [ite_eq_right (by rw [hsz, hko]; decide),
        Eth.G1.uncompress_of_keyValidate? hkv, Option.elim_some]
      dsimp only
      rw [fastAggregateVerify_match_1, Eth.G1.neg_ofA har, Eth.G1.generator_eq]
      unfold sigValidate?
      rw [G2J.compress_match_1]
      by_cases h64 : (sig[0]?.getD 0) &&& 64 = 0
      · rw [Eth.G2.uncompress_eq sig h64]
        cases hd : g2Decompress? sig with
        | none =>
          rw [Option.elim_none, Option.elim_none, Option.elim_none]
          split <;> rfl
        | some q =>
          obtain ⟨hqr, hqn, -⟩ := g2Decompress?_some hd
          have hsz : sig.size = 96 := (g2Decompress?_parts hd).1
          rw [Option.elim_some, Option.elim_some,
            ite_eq_right (show ¬(sig.size ≠ 96) from by rw [hsz]; exact fun h => h rfl)]
          dsimp only
          rw [Eth.G2.inSubgroup_ofA hqr hqn, G2A.inSubgroupPsi_eq hqr hqn]
          cases hs : q.inSubgroup with
          | false => rfl
          | true =>
            rw [ite_eq_left (rfl : true = true), Option.elim_some, ite_eq_right (by decide),
              fastAggregateVerify_match_1, hrq]
            cases rq with
            | error e => rfl
            | ok qq =>
              have hqi := hH qq rfl
              rw [toOption_ok, Option.bind_some, Eth.g2Affine?, hqi,
                ite_eq_right Bool.false_ne_true, Option.elim_some]
              dsimp only
              have hh : H2C.hashToG2? msg ethDst = some ⟨ofEth qq.toAffine.1, ofEth qq.toAffine.2⟩ := by
                rw [hrq, toOption_ok, Option.bind_some, Eth.g2Affine?, hqi,
                  ite_eq_right Bool.false_ne_true]
              obtain ⟨hhr, hhn⟩ := hashOnCurve _ _ _ hh
              rw [pairingCheck_eq_eth _ (by
                intro pq hpq
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpq
                rcases hpq with rfl | rfl
                · exact ⟨hqr, hqn, (G2A.inSubgroup_iff hqr hqn).mp hs⟩
                · exact ⟨hhr, hhn, hashInG2 _ _ _ hh⟩)]
              simp only [List.map_cons, List.map_nil]
              rw [Eth.pairingCheck_eq, Eth.pairingCheck_eq,
                Eth.pairingAcc_congr2 _ _ (q' := qq) (by rw [Eth.G2.isInfinity_ofA, hqi])
                  (Eth.ofG2_congr (by rw [Eth.G2.isInfinity_ofA, hqi]) (Eth.G2.toAffine_ofA qq))]
      · have hd : g2Decompress? sig = none := by
          rw [g2Decompress?_eq]
          by_cases hs : sig.size ≠ 96
          · rw [ite_eq_left hs]
          rw [ite_eq_right hs]
          by_cases h1 : (sig[0]?.getD 0) &&& 128 = 0
          · rw [ite_eq_left h1]
          rw [ite_eq_right h1, ite_eq_left h64]
        rcases Eth.G2.uncompress_inf sig h64 with h | h
        · rw [hd, h, Option.elim_none, Option.elim_none]
          split <;> rfl
        · exact absurd h hsig
/-- The runtime refuses the identity's canonical encoding as a signature. -/
theorem fastAggregateVerifyBytes_identitySig (pks : Array ByteArray) (msg : ByteArray) :
    fastAggregateVerifyBytes pks msg EthLib.Cryptography.Bls.G2.infinityBytes = false := by
  unfold fastAggregateVerifyBytes
  cases pks.mapM keyValidate? with
  | none => rfl
  | some keys =>
    dsimp only
    unfold fastAggregateVerify verifyAggregate
    rw [fastAggregateVerify_match_3]
    cases aggregate? keys with
    | none => rfl
    | some agg =>
      rw [Option.elim_some, fastAggregateVerify_match_1, Eth.G2.infinityBytes_eq,
        sigValidate?_identity]
      rfl

/-- **The identity's encoding as the signature.** EthLib decodes it to the identity, whose
subgroup check passes and whose pair its pairing check skips: where `hash_to_G2(msg)` is not
the identity, EthLib's `fastAggregateVerify` is true exactly when every key passes KeyValidate,
their sum `A` is not the identity, and the runtime's check of the one pair `(−A, H(m))` passes,
`e(A, H(m)) = 1`. The runtime refuses this signature (`fastAggregateVerifyBytes_identitySig`), so
the two agree here exactly when that check fails: non-degeneracy, `H(m)` being in G2
(`hashInG2`), not proved here (`fastAggregateVerifyBytes_eq_eth_of_nonDegenerate` assumes it). -/
theorem fastAggregateVerify_eth_identitySig (pks : Array ByteArray) (msg : ByteArray)
    (hH : ∀ q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
      EthLib.Cryptography.Bls.Signatures.DST = .ok q → q.isInfinity = false) :
    EthLib.Cryptography.Bls.Signatures.fastAggregateVerify pks msg
        EthLib.Cryptography.Bls.G2.infinityBytes =
      (pks.mapM keyValidate?).elim false fun keys => (aggregate? keys).elim false fun agg =>
        (H2C.hashToG2? msg ethDst).elim false fun h => pairingCheck [(agg.neg, h)] := by
  have hrq : H2C.hashToG2? msg ethDst = (EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
      EthLib.Cryptography.Bls.Signatures.DST).toOption.bind Eth.g2Affine? :=
    hashToG2?_eq_eth msg ethDst
  have hP := G2.uncompress_infinityBytes
  obtain ⟨hsz96, -, -⟩ := G2.infinityBytes_bytes
  rw [ethFav_value]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  delta_private
  rw [← Array.forIn_toList, Eth.forIn_keyLoop _ (fun pk acc => ?hb)]
  case hb =>
    cases hk : keyValidate? pk with
    | none =>
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate pk).isOk = false := by
        rw [Eth.G1.keyValidate_isOk, hk]; rfl
      rw [ite_eq_left (by simp [hko]), Option.elim_none]
    | some k =>
      obtain ⟨hd, -⟩ := keyValidate?_some hk
      have hsz : pk.size = 48 := (g1Decompress?_parts hd).1
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate pk).isOk = true := by
        rw [Eth.G1.keyValidate_isOk, hk]; rfl
      rw [ite_eq_right (by simp [hsz, hko]), Eth.G1.uncompress_of_keyValidate? hk, Option.elim_some]
  generalize EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg
    EthLib.Cryptography.Bls.Signatures.DST = rq at hH hrq ⊢
  generalize EthLib.Cryptography.Bls.G2.uncompress EthLib.Cryptography.Bls.G2.infinityBytes = rP
    at hP ⊢
  rw [idBind, Eth.keyLoop_fst, Array.mapM_eq_mapM_toList]
  have hks := mapM_keyValidate?_mem pks.toList
  have hksub := mapM_keyValidate?_sub pks.toList
  cases hm : pks.toList.mapM keyValidate? with
  | none =>
    by_cases he : pks.isEmpty = true
    · rw [ite_eq_left he]; rfl
    · rw [ite_eq_right he]; rfl
  | some ks =>
    have hks' := hks ks hm
    have hksub' := hksub ks hm
    rw [show (List.toArray <$> some ks) = some ks.toArray from rfl,
      ite_eq_left (show (some ks).isSome = true from rfl), Eth.keyLoop_sum pks.toList _ ks hm,
      Option.elim_some]
    dsimp only
    by_cases he : pks.isEmpty = true
    · rw [ite_eq_left he]
      have hl : pks.toList = [] := by simpa using he
      rw [hl] at hm
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
      subst hm
      rfl
    rw [ite_eq_right he, Id.run_pure]
    obtain ⟨hEn, hEa⟩ := Eth.G1.foldl_add_spec ks EthLib.Cryptography.Bls.G1.zero
      Eth.G1.zero_spec.1 hks'
    rw [Eth.G1.zero_spec.2, zero_add] at hEa
    have hagg := aggregate?_spec ks.toArray (by simpa using hks')
    simp only at hagg
    revert hagg
    cases aggregate? ks.toArray with
    | none =>
      intro hagg
      have hinf := (Eth.G1.isInfinity_iff_zero hEn).mpr (by rw [hEa]; exact hagg)
      rw [Option.elim_none, Eth.G1.compress_inf hinf, Eth.G1.infinityBytes_eq]
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate (identityBytes 48)).isOk = false := by
        rw [Eth.G1.keyValidate_isOk, keyValidate?_identity]; rfl
      rw [ite_eq_left (by simp [hko])]
    | some a =>
      intro hagg
      obtain ⟨har, han, hae⟩ := hagg
      have hne : Point.toAffine E1 a.toJ ≠ 0 := by
        rw [G1A.toJ, Point.toAffine_some (by rw [← G1A.toJ]; exact han)]
        exact Affine.Point.some_ne_zero _
      have hinf : (List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).isInfinity = false := by
        cases h : (List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).isInfinity
        · rfl
        · exact absurd (by rw [hae, ← hEa]; exact (Eth.G1.isInfinity_iff_zero hEn).mp h) hne
      obtain ⟨hbn, hbe⟩ := Eth.G1.affine_spec hEn hinf
      have ha' : (⟨(List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).toAffine.1.val,
          (List.foldl (fun a k => EthLib.Cryptography.Bls.G1.add a (Eth.G1.ofA k))
          EthLib.Cryptography.Bls.G1.zero ks).toAffine.2.val⟩ : G1A) = a :=
        G1A.eq_of_aff ⟨val_lt _, val_lt _⟩ har hbn han (by
          show Point.toAffine E1 ![_, _, 1] = _
          rw [hbe, hEa, ← hae])
      rw [Eth.G1.compress_eq hinf, ha']
      have hsub : R • Point.toAffine E1 a.toJ = 0 := by
        rw [hae, List.smul_sum, List.map_map]
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hksub' p hp
      have hkv := keyValidate?_compress har han hsub
      have hko : (EthLib.Cryptography.Bls.G1.keyValidate a.compress).isOk = true := by
        rw [Eth.G1.keyValidate_isOk, hkv]; rfl
      have hsz : a.compress.size = 48 := size_natBe _ _ _
      rw [ite_eq_right (by rw [hsz, hko]; decide),
        Eth.G1.uncompress_of_keyValidate? hkv, Option.elim_some]
      dsimp only
      rw [Eth.G1.neg_ofA har, ite_eq_right (show ¬(EthLib.Cryptography.Bls.G2.infinityBytes.size ≠ 96)
        from by rw [hsz96]; exact fun h => h rfl)]
      cases rP with
      | error e => cases hP
      | ok P =>
        have hPi : P.isInfinity = true := by
          rw [toOption_ok, Option.map_some, Option.some.injEq] at hP; exact hP
        dsimp only
        rw [show EthLib.Cryptography.Bls.G2.inSubgroup P = true by
          unfold EthLib.Cryptography.Bls.G2.inSubgroup; rw [hPi, ite_eq_left rfl],
          ite_eq_right (by decide), hrq]
        cases rq with
        | error e => rfl
        | ok qq =>
          have hqi := hH qq rfl
          rw [toOption_ok, Option.bind_some, Eth.g2Affine?, hqi,
            ite_eq_right Bool.false_ne_true, Option.elim_some]
          dsimp only
          have hh : H2C.hashToG2? msg ethDst = some ⟨ofEth qq.toAffine.1, ofEth qq.toAffine.2⟩ := by
            rw [hrq, toOption_ok, Option.bind_some, Eth.g2Affine?, hqi,
              ite_eq_right Bool.false_ne_true]
          obtain ⟨hhr, hhn⟩ := hashOnCurve _ _ _ hh
          rw [pairingCheck_eq_eth _ (by
            intro pq hpq
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpq
            subst hpq
            exact ⟨hhr, hhn, hashInG2 _ _ _ hh⟩)]
          simp only [List.map_cons, List.map_nil]
          rw [Eth.pairingCheck_eq, Eth.pairingCheck_eq, Eth.pairingAcc_skip _ hPi,
            Eth.pairingAcc_congr1 _ (q' := qq) (by rw [Eth.G2.isInfinity_ofA, hqi])
              (Eth.ofG2_congr (by rw [Eth.G2.isInfinity_ofA, hqi]) (Eth.G2.toAffine_ofA qq))]

end LeanLight.Lc.Bls
