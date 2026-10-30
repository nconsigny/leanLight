/-
Copyright (c) 2026 Vitalik Buterin, Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file
`proofs/LeanLightProofs/Vendor/VCVio/LICENSE`.
Authors: Vitalik Buterin, Nicolas Consigny
-/

/-!
# Keccak-256

Ethereum's hash: the Keccak-f[1600] permutation of FIPS 202 in a sponge of rate 136 bytes
(capacity 512 bits) with the original Keccak padding `0x01 … 0x80`, which FIPS 202 later
replaced with `0x06` for SHA3-256. Transaction hashes are this function, and `keyd` runs
`keccak256Fast` in its place (`LeanLight.Base.KeccakFast`, `keccak256_eq_fast`).

This is VCVio's pure-Lean Keccak-256 (`VCVio.Algorithms.Keccak`, Apache-2.0; first vendored
from `HashSig/SLHDSA/Concrete/Keccak.lean` at commit `cbd4144b51d92da00dd50f05e068b2348fa6e529`),
vendored because VCVio's module imports Mathlib, and nothing compiled into `keyd` may. Two
changes, both so that no expression can panic: every `a[i]!` is written `a[i]?.getD 0`, and
every `set!` is written `setIfInBounds`, the function `set!` abbreviates.
`LeanLightProofs.Spec.Keccak` proves this `keccak256` equal to `VCVio.Algorithms.Keccak.keccak256`
at commit `88efe971` (`proofs/LeanLightProofs/Vendor/VCVio/Keccak.lean`).

Reviewing it against FIPS 202 means checking: `roundConstants` (§3.2.5, ι), `rhoLUT`
(§3.2.2, ρ offsets with lanes ordered `x + 5y`), `piLUT` (§3.2.3, `(x, y) ↦ (y, 2x + 3y)`),
`round` (θ, ρ, π, χ, ι in that order), `f1600` (24 rounds), `absorb` (pad, then XOR each
136-byte block into the state little-endian per lane and permute) and `squeeze` (the first 32
bytes of the state, little-endian per lane).
-/

namespace LeanLight.Spec.Keccak

/-- ρ rotation offsets (lanes ordered `x + 5*y`). -/
def rhoLUT : Array Nat :=
  #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
    41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- π permutation: `(x,y) ↦ (y, 2x+3y mod 5)`, precomputed as `oldIdx ↦ newIdx`. -/
def piLUT : Array Nat :=
  (((List.range 5).map fun y => (List.range 5).map fun x =>
    let nx := y; let ny := (2 * x + 3 * y) % 5; nx + 5 * ny).flatten).toArray

/-- Keccak-f[1600] round constants. -/
def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Left-rotate a 64-bit word by `n` bits. -/
def rotl64 (x : UInt64) (n : Nat) : UInt64 := (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

/-- One Keccak-f[1600] round (θ, ρ, π, χ, ι). -/
def round (state : Array UInt64) (rc : UInt64) : Array UInt64 :=
  let C : Array UInt64 := (List.range 5).toArray.map fun x =>
    state[x]?.getD 0 ^^^ state[x + 5]?.getD 0 ^^^ state[x + 10]?.getD 0 ^^^
      state[x + 15]?.getD 0 ^^^ state[x + 20]?.getD 0
  let D : Array UInt64 := (List.range 5).toArray.map fun x =>
    C[(x + 4) % 5]?.getD 0 ^^^ rotl64 (C[(x + 1) % 5]?.getD 0) 1
  let s1 : Array UInt64 := (List.range 25).toArray.map fun i =>
    state[i]?.getD 0 ^^^ D[i % 5]?.getD 0
  let B : Array UInt64 := (List.range 25).foldl
    (fun B' i => B'.setIfInBounds (piLUT[i]?.getD 0) (rotl64 (s1[i]?.getD 0) (rhoLUT[i]?.getD 0)))
    (Array.replicate 25 0)
  let s2 : Array UInt64 := (List.range 25).toArray.map fun i =>
    let x := i % 5; let y := i / 5
    B[i]?.getD 0 ^^^ (~~~(B[(x + 1) % 5 + 5 * y]?.getD 0) &&& B[(x + 2) % 5 + 5 * y]?.getD 0)
  s2.setIfInBounds 0 (s2[0]?.getD 0 ^^^ rc)

/-- The full 24-round Keccak-f[1600] permutation. -/
def f1600 (state : Array UInt64) : Array UInt64 :=
  (List.range 24).foldl (fun s r => round s (roundConstants[r]?.getD 0)) state

/-- Sponge absorb with the given `rate` (bytes) and domain-separation pad byte. -/
def absorb (input : ByteArray) (rate : Nat) (padByte : UInt8) : Array UInt64 := Id.run do
  let padTotal := rate - input.size % rate
  let padBytes : List UInt8 :=
    if padTotal = 1 then [padByte ||| 0x80]
    else padByte :: (List.replicate (padTotal - 2) 0 ++ [0x80])
  let padded := input ++ ByteArray.mk padBytes.toArray
  let mut s : Array UInt64 := Array.replicate 25 0
  for b in [0:padded.size / rate] do
    for i in [0:rate] do
      let bv : UInt64 := (padded[b * rate + i]?.getD 0).toNat.toUInt64
      s := s.setIfInBounds (i / 8) (s[i / 8]?.getD 0 ^^^ (bv <<< ((i % 8) * 8).toUInt64))
    s := f1600 s
  return s

/-- Squeeze `outLen ≤ rate` bytes from the state (one block; sufficient for 32-byte digests). -/
def squeeze (s : Array UInt64) (outLen : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:outLen] do
    out := out.push (((s[i / 8]?.getD 0 >>> ((i % 8) * 8).toUInt64) &&& 0xFF).toUInt8)
  return out

/-- EVM `keccak256` (rate 136, pad `0x01`), 32-byte digest. -/
def keccak256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x01) 32

end LeanLight.Spec.Keccak
