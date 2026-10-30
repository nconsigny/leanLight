import LeanLight.Base.Keccak
import LeanLight.Base.KeccakFast
import LeanLightProofs.Vendor.VCVio.Keccak

/-!
# The light client's Keccak-256 is VCVio's

`LeanLight.Base.Keccak` (`LeanLight.Spec.Keccak.keccak256`) computes
`VCVio.Algorithms.Keccak.keccak256` on every input: `keccak256_eq_vcvio`. The two write the same
FIPS 202 sponge, save that the runtime copy avoids panicking index operations (`a[i]!` becomes
`a[i]?.getD 0`, `set!` becomes `setIfInBounds`) and builds the squeezed digest with `push` rather
than `Array.ofFn`.

Because `0` is `Inhabited.default` on `Nat`, `UInt8` and `UInt64`, `a[i]!` is already `a[i]?.getD 0`
and `Array.set!` is `Array.setIfInBounds`, so `round`, `f1600` and `absorb` are equal on every
input, and `squeeze` builds the same `outLen` bytes. Together with `keccak256_eq_fast`
(`LeanLight.Base.KeccakFast`), the unboxed `keccak256Fast` also equals VCVio's
(`keccak256Fast_eq_vcvio`).
-/

namespace LeanLight.Spec.Keccak

private theorem getElem!_eq_getD_nat (a : Array Nat) (i : Nat) : a[i]! = a[i]?.getD 0 := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, getElem?_pos a i h]; rfl
  · rw [getElem!_neg a i h, getElem?_neg a i h]; rfl

private theorem getElem!_eq_getD_u64 (a : Array UInt64) (i : Nat) : a[i]! = a[i]?.getD 0 := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, getElem?_pos a i h]; rfl
  · rw [getElem!_neg a i h, getElem?_neg a i h]; rfl

private theorem getElem!_eq_getD_ba (m : ByteArray) (i : Nat) : m[i]! = m[i]?.getD 0 := by
  by_cases h : i < m.size
  · rw [getElem!_pos m i h, getElem?_pos m i h]; rfl
  · rw [getElem!_neg m i h, getElem?_neg m i h]; rfl

theorem rhoLUT_eq_vcvio : rhoLUT = VCVio.Algorithms.Keccak.rhoLUT := rfl

theorem piLUT_eq_vcvio : piLUT = VCVio.Algorithms.Keccak.piLUT := rfl

theorem roundConstants_eq_vcvio : roundConstants = VCVio.Algorithms.Keccak.roundConstants := rfl

theorem rotl64_eq_vcvio : rotl64 = VCVio.Algorithms.Keccak.rotl64 := rfl

/-- One runtime round is VCVio's round. -/
theorem round_eq_vcvio (state : Array UInt64) (rc : UInt64) :
    round state rc = VCVio.Algorithms.Keccak.round state rc := by
  simp only [round, VCVio.Algorithms.Keccak.round, rotl64_eq_vcvio, piLUT_eq_vcvio, rhoLUT_eq_vcvio,
    getElem!_eq_getD_u64, getElem!_eq_getD_nat, Array.set!_eq_setIfInBounds]

/-- The 24-round permutation is VCVio's `f1600`. -/
theorem f1600_eq_vcvio (state : Array UInt64) :
    f1600 state = VCVio.Algorithms.Keccak.f1600 state := by
  simp only [f1600, VCVio.Algorithms.Keccak.f1600, round_eq_vcvio, roundConstants_eq_vcvio,
    getElem!_eq_getD_u64]

/-- The sponge absorb is VCVio's `absorb` at every rate and domain-separation byte. -/
theorem absorb_eq_vcvio (input : ByteArray) (rate : Nat) (padByte : UInt8) :
    absorb input rate padByte = VCVio.Algorithms.Keccak.absorb input rate padByte := by
  simp only [absorb, VCVio.Algorithms.Keccak.absorb, f1600_eq_vcvio, getElem!_eq_getD_ba,
    getElem!_eq_getD_u64, Array.set!_eq_setIfInBounds]

private theorem foldl_push_range' (f : Nat → UInt8) (n : Nat) :
    ∀ (k : Nat) (acc : ByteArray),
      ((List.range' k n).foldl (fun out i => out.push (f i)) acc).data.toList =
        acc.data.toList ++ (List.range' k n).map f := by
  induction n with
  | zero =>
    intro k acc
    simp
  | succ n ih =>
    intro k acc
    rw [List.range'_succ, List.foldl_cons, ih (k + 1) (acc.push (f k))]
    simp [ByteArray.push, List.append_assoc]

/-- The single-block squeeze writes the same bytes as VCVio's `Array.ofFn` squeeze. -/
theorem squeeze_eq_vcvio (s : Array UInt64) (outLen : Nat) :
    squeeze s outLen = VCVio.Algorithms.Keccak.squeeze s outLen := by
  apply ByteArray.ext
  apply Array.ext'
  unfold squeeze VCVio.Algorithms.Keccak.squeeze
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    getElem!_eq_getD_u64]
  dsimp only [bind, pure, Id.instMonad]
  rw [foldl_push_range', ← List.range_eq_range', Array.toList_ofFn, List.ofFn_eq_map]
  have hemp : ByteArray.empty.data.toList = [] := rfl
  rw [hemp, List.nil_append, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- `LeanLight.Spec.Keccak.keccak256` equals `VCVio.Algorithms.Keccak.keccak256` on every input. -/
theorem keccak256_eq_vcvio (input : ByteArray) :
    keccak256 input = VCVio.Algorithms.Keccak.keccak256 input := by
  rw [keccak256, VCVio.Algorithms.Keccak.keccak256, absorb_eq_vcvio, squeeze_eq_vcvio]

/-- The unboxed `keccak256Fast` equals `VCVio.Algorithms.Keccak.keccak256` on every input. -/
theorem keccak256Fast_eq_vcvio (input : ByteArray) :
    keccak256Fast input = VCVio.Algorithms.Keccak.keccak256 input := by
  rw [← keccak256_eq_fast, keccak256_eq_vcvio]

end LeanLight.Spec.Keccak
