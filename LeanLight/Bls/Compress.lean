import LeanLight.Bls.G1
import LeanLight.Bls.G2

/-!
# BLS12-381: point encodings, KeyValidate and the signature's checks

Moved from the benchmark's `Bls/Curve.lean` (see `LeanLight.Bls.Fp`). The encodings are ZCash's
compressed ones (draft-irtf-cfrg-pairing-friendly-curves, Appendix C; EthLib's `Compress`): 48
bytes for G1, the big-endian `x`; 96 for G2, `x.c1 ‖ x.c0`; the first byte's top three bits
carry the flags: compressed (`0x80`, required), identity (`0x40`), and the sign of `y`
(`0x20`, set when `y` is the lexicographically larger root, `fLarge`, `Fp2.large`).

The light client takes no identity point, so decompression refuses every encoding with the
identity flag (`g1Decompress?`, `g2Decompress?`): a public key that is the identity fails
KeyValidate (IRTF BLS §2.5), and a signature that is the identity is refused before the
pairing, where under a key that is not the identity it never verifies. A coordinate must be
below `P`, and `y` is the root of the curve's equation the sign bit names, so the point is on
the curve; the subgroup checks are `[r]P = O` and `[r]Q = O` (`keyValidate?`, `sigValidate?`),
run as Scott's tests (`G1A.inSubgroupFast`, with `[r]P` as its fallback, and
`G2A.inSubgroupPsi`), each equal to the check it replaces on the curve.
`isIdentity48` and `isIdentity96` recognize the identity's one canonical encoding, which
the tests' Ethereum wrappers need.
-/

namespace LeanLight.Lc.Bls

/-- `0xc0` then `n − 1` zero bytes: the identity's canonical encoding. -/
def identityBytes (n : Nat) : ByteArray := natBe 0 n 0xc0

/-- `b` is the identity's canonical 48-byte encoding. -/
def isIdentity48 (b : ByteArray) : Bool := b == identityBytes 48

/-- `b` is the identity's canonical 96-byte encoding. -/
def isIdentity96 (b : ByteArray) : Bool := b == identityBytes 96

/-! ## G1 -/

/-- The compressed encoding of an affine point. -/
def G1A.compress (p : G1A) : ByteArray :=
  natBe p.x 48 (0x80 ||| (if fLarge p.y then 0x20 else 0))

/-- The compressed encoding of a point, the identity's included. -/
def G1J.compress (p : G1J) : ByteArray :=
  match p.toAffine? with
  | some a => a.compress
  | none => identityBytes 48

/-- 48 bytes to a point of `E(Fp)` that is not the identity: the compression flag set, the
identity flag clear, `x < P`, and `x³ + 4` a square, whose root the sign bit names is `y`.
`none` otherwise. No subgroup check. -/
def g1Decompress? (b : ByteArray) : Option G1A :=
  if b.size ≠ 48 then none else
  let b0 := b[0]?.getD 0
  if b0 &&& 0x80 = 0 then none else
  if b0 &&& 0x40 ≠ 0 then none else
  let sign := b0 &&& 0x20 ≠ 0
  let x := beNat b 1 47 (b0 &&& 0x1f).toNat
  if x ≥ P then none else
  match fsqrt? (fadd (fmul (fsqr x) x) 4) with
  | none => none
  | some y => some ⟨x, if fLarge y == sign then y else fneg y⟩

/-- KeyValidate (IRTF BLS §2.5) of a 48-byte public key: decompressed, not the identity, and
`[r]P = O`, checked as `G1A.inSubgroupFast` checks it (equal to `inSubgroup` on the curve). -/
def keyValidate? (b : ByteArray) : Option G1A :=
  match g1Decompress? b with
  | some p => if p.inSubgroupFast then some p else none
  | none => none

/-! ## G2 -/

/-- The compressed encoding of an affine point. -/
def G2A.compress (p : G2A) : ByteArray :=
  natBe p.x.c1 48 (0x80 ||| (if p.y.large then 0x20 else 0)) ++ natBe p.x.c0 48

/-- The compressed encoding of a point, the identity's included. -/
def G2J.compress (p : G2J) : ByteArray :=
  match p.toAffine? with
  | some a => a.compress
  | none => identityBytes 96

/-- 96 bytes to a point of `E'(Fp2)` that is not the identity: the compression flag set, the
identity flag clear, `x.c1 ‖ x.c0` each below `P`, and `x³ + 4(1 + u)` a square, whose root the
sign bit names is `y`. `none` otherwise. No subgroup check. -/
def g2Decompress? (b : ByteArray) : Option G2A :=
  if b.size ≠ 96 then none else
  let b0 := b[0]?.getD 0
  if b0 &&& 0x80 = 0 then none else
  if b0 &&& 0x40 ≠ 0 then none else
  let sign := b0 &&& 0x20 ≠ 0
  let x1 := beNat b 1 47 (b0 &&& 0x1f).toNat
  let x0 := beNat b 48 48
  if x0 ≥ P || x1 ≥ P then none else
  let x : Fp2 := ⟨x0, x1⟩
  match (x.sqr.mul x |>.add bTwist).sqrt? with
  | none => none
  | some y => some ⟨x, if y.large == sign then y else y.neg⟩

/-- The signature's checks of CoreVerify (IRTF BLS §2.7, `signature_subgroup_check`): 96 bytes
decompressed, not the identity, and `[r]Q = O`, checked by Scott's test `G2A.inSubgroupPsi`
(equal to `inSubgroup` on the curve). -/
def sigValidate? (b : ByteArray) : Option G2A :=
  match g2Decompress? b with
  | some q => if q.inSubgroupPsi then some q else none
  | none => none

end LeanLight.Lc.Bls
