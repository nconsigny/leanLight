/-!
# BLS12-381: the base field `Fp`, on `Nat`

The fast layer of the light client's BLS12-381 (`docs/spec-16-light-client.md`, "Cryptography in
Lean"), moved from the benchmark of 2026-10-24 (`Bls/Field.lean`, written for lkd), whose
measurements are in "Speed". Its readable specification is EthLib's, vendored in
`LeanLightProofs.Vendor.EthLib.Bls`, where `Fp` is `Fin p`; `LeanLightProofs.Bls.Fp` proves each
operation here equal to EthLib's (25c, LC4b), and `LeanLightTests.Bls` also runs both layers on the
same inputs.

An element is a `Nat` below `P`, and every operation keeps its result below `P` when its
arguments are. Big numbers are Lean core's `Nat`, which the runtime backs with GMP above 63
bits. Verification touches only public data, so nothing here is constant-time.

**`Nat.powMod`**, Lean core's `lean_nat_powmod` (GMP's `mpz_powm`), is called at one site,
`fpow`, with the modulus `P`, a nonzero literal (`P_ne_zero`): with modulus 0 it would compute
`b ^ e` and abort above an exponent of 2³²−1.

Also here, the big-endian byte readers and writers the encodings use (`beNat`, `natBe`).
-/

namespace LeanLight.Lc.Bls

/-- The base field's modulus `p`, 381 bits. -/
def P : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- `r`, the prime order of G1, G2 and the pairing's target group, 255 bits. -/
def R : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- `|x|`, the absolute value of the curve parameter `x = −0xd201000000010000`. -/
def X : Nat := 0xd201000000010000

/-- G2's effective cofactor `h_eff` (RFC 9380 §8.8.2), 636 bits: `clear_cofactor(P)` is
`[h_eff]P` (open decision 12). `hEff_def` derives it from `x`. -/
def hEff : Nat :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551

/-- `P²`: added before a subtraction of products below it, so that the difference stays a
`Nat`. -/
def PP : Nat := P * P

/-- The one modulus `Nat.powMod` is called with is not zero. -/
theorem P_ne_zero : P ≠ 0 := by decide

/-- `h_eff = 3(x² − 1)·h₂` with `x = −|x|` and `h₂ = (x⁸ − 4x⁷ + 5x⁶ − 4x⁴ + 6x³ − 4x² − 4x + 13)/9`,
G2's cofactor (RFC 9380 §8.8.2 and Appendix G.3, after Budroni and Pintore), by the kernel. -/
theorem hEff_def :
    let x : Int := -(X : Int)
    (hEff : Int) = 3 * (x ^ 2 - 1) *
      ((x ^ 8 - 4 * x ^ 7 + 5 * x ^ 6 - 4 * x ^ 4 + 6 * x ^ 3 - 4 * x ^ 2 - 4 * x + 13) / 9) := by
  decide +kernel

/-! ## Fp -/

@[inline] def fadd (a b : Nat) : Nat := let s := a + b; if s ≥ P then s - P else s
@[inline] def fsub (a b : Nat) : Nat := if a ≥ b then a - b else a + P - b
@[inline] def fneg (a : Nat) : Nat := if a = 0 then 0 else P - a
@[inline] def fmul (a b : Nat) : Nat := a * b % P
@[inline] def fsqr (a : Nat) : Nat := a * a % P
@[inline] def fdbl (a : Nat) : Nat := fadd a a

/-- `a^e mod P`: the one call of `Nat.powMod`, its modulus the literal `P` (`P_ne_zero`). -/
def fpow (a e : Nat) : Nat := Nat.powMod a e P

/-- The inverse by Fermat, `a^(P−2)`; `0` maps to `0`. -/
@[inline] def finv (a : Nat) : Nat := fpow a (P - 2)

/-- A square root for `P ≡ 3 mod 4`: `a^((P+1)/4)`, kept only when it squares to `a`. -/
def fsqrt? (a : Nat) : Option Nat :=
  let y := fpow a ((P + 1) / 4)
  if y * y % P = a % P then some y else none

/-- Euler's criterion: `a` is a square in `Fp` (zero included). -/
@[inline] def fIsSquare (a : Nat) : Bool := a % P = 0 || fpow a ((P - 1) / 2) = 1

/-- ZCash's "lexicographically largest" for `Fp`: `y > (P − 1)/2`, so `y > P − y`. -/
@[inline] def fLarge (y : Nat) : Bool := y > (P - 1) / 2

/-! ## Big-endian bytes -/

/-- `acc` followed by the bytes `b[off, off + n)` read as a big-endian number; a byte past the
end reads 0. -/
def beNat (b : ByteArray) (off n : Nat) (acc : Nat := 0) : Nat := Id.run do
  let mut v := acc
  for i in [0:n] do
    v := v * 256 + (b[off + i]?.getD 0).toNat
  return v

/-- `a` as `n` big-endian bytes (`a < 256^n`), with `flags` OR-ed into the first byte. -/
def natBe (a n : Nat) (flags : UInt8 := 0) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:n] do
    let byte := (a >>> (8 * (n - 1 - i))).toUInt8
    out := out.push (if i = 0 then byte ||| flags else byte)
  return out

end LeanLight.Lc.Bls
