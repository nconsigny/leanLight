import LeanLight.Base.Keccak

/-!
# Keccak-256, the code that runs

`LeanLight.Base.Keccak` is the readable Keccak-256 every theorem is about: its state is an
`Array UInt64` whose 25 lanes are boxed, rebuilt with `List.range` maps in each of the 24 rounds,
and its sponge XORs the input in one byte at a time. Compiled as it is, it costs about 15 µs per
136-byte block. This file is the same function written for the compiler, about 40 times faster
(leanKohakuDesktop's `spec/01-keyd.md`, "Cost"), and `keccak256_eq_fast` proves the two equal on every input.
Registered as a `csimp` equation, it makes every definition compiled after this file is
imported call `keccak256Fast` wherever its source says `keccak256`,
while every statement, and every proof about `keccak256`, keeps meaning the readable one.

The fast version:

- holds the state as `Lanes`, one structure of 25 `UInt64` fields, which the compiler keeps
  unboxed; a round reads the 25 fields and builds the next state, reusing the old one's memory
  when it is not shared, so no round allocates;
- writes θ, ρ, π, χ and ι out per lane (`Lanes.round`), and the 24 rounds out with their
  constants (`Lanes.permute`);
- XORs a block into the state a lane at a time, 8 bytes per lane, straight from the input
  (`Lanes.absorbBlock`, `Lanes.xorLaneAt`), and the final block with its padding made byte by
  byte as it is read (`Lanes.absorbLast`, `Lanes.padByte`), so the padded copy of the input the
  readable `absorb` builds is never made;
- writes the 32 bytes of the digest out (`Lanes.digest`).

Why the equation replaces `keccak256` and not the permutation `f1600`: a `csimp` equation
changes only the code compiled after it. `absorb`, which calls `f1600`, is compiled in
`LeanLight.Base.Keccak`, before this file, so an equation for `f1600` would leave it calling the
slow permutation; and nothing else calls `f1600`. Every caller in the runtime libraries (today
`LeanLight.Base.Common`, `LeanLight.El.Header` and `LeanLight.El.Trie`) calls `keccak256`, and must
have this file in its imports, directly or not, for the equation to apply to it; no script checks
that import (`scripts/check-runtime.sh` only lists the `@[csimp]` equations).

The proof: one round on 25 symbolic lanes, by evaluating the readable `round` at
`Lanes.toArray s` (`round_toArray`); the 24 rounds (`f1600_toArray`); the inner loop of `absorb`
on one block (`xorBytes_toArray`); its outer loop, block by block, the padded input's whole
blocks being the input's and its last block `padByte`'s (`absorb_toArray`); `squeeze`
(`squeeze_toArray`); and their composition (`keccak256_eq_fast`). No step evaluates the hash,
none uses `native_decide` or `bv_decide`, and the equation rests on `propext`,
`Classical.choice` and `Quot.sound` alone (`proofs/Audit.lean`). The per-lane formulas are long
but mechanical, and a reviewer need not check them by hand: the proof checks them against the
readable code.
-/

namespace LeanLight.Spec.Keccak

/-- The Keccak-f[1600] state as 25 lanes, lane `x + 5y` (FIPS 202's `A[x, y]`) in field
`a{x + 5y}`, the index the readable code gives it in its array. -/
structure Lanes where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

namespace Lanes

/-- The state as the readable code holds it: lane `i` at index `i`. -/
def toArray (s : Lanes) : Array UInt64 :=
  #[s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14,
    s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

/-- The all-zero state the sponge starts from. -/
def zero : Lanes :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `x` rotated left by `n` bits, for `0 < n < 64`: `rotl64 x n` with the shift amounts as
`UInt64` constants. -/
@[inline] def rotl (x : UInt64) (n : UInt64) : UInt64 := x <<< n ||| x >>> (64 - n)

/-- One round, `round` on the lanes: θ (the column parities `c` and their mix `d`), ρ and π (lane
`i` XORed with `d`, rotated and moved to `b{π i}`), then χ, and ι on lane 0. -/
def round (s : Lanes) (rc : UInt64) : Lanes :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  let b0 := s.a0 ^^^ d0
  let b1 := rotl (s.a6 ^^^ d1) 44
  let b2 := rotl (s.a12 ^^^ d2) 43
  let b3 := rotl (s.a18 ^^^ d3) 21
  let b4 := rotl (s.a24 ^^^ d4) 14
  let b5 := rotl (s.a3 ^^^ d3) 28
  let b6 := rotl (s.a9 ^^^ d4) 20
  let b7 := rotl (s.a10 ^^^ d0) 3
  let b8 := rotl (s.a16 ^^^ d1) 45
  let b9 := rotl (s.a22 ^^^ d2) 61
  let b10 := rotl (s.a1 ^^^ d1) 1
  let b11 := rotl (s.a7 ^^^ d2) 6
  let b12 := rotl (s.a13 ^^^ d3) 25
  let b13 := rotl (s.a19 ^^^ d4) 8
  let b14 := rotl (s.a20 ^^^ d0) 18
  let b15 := rotl (s.a4 ^^^ d4) 27
  let b16 := rotl (s.a5 ^^^ d0) 36
  let b17 := rotl (s.a11 ^^^ d1) 10
  let b18 := rotl (s.a17 ^^^ d2) 15
  let b19 := rotl (s.a23 ^^^ d3) 56
  let b20 := rotl (s.a2 ^^^ d2) 62
  let b21 := rotl (s.a8 ^^^ d3) 55
  let b22 := rotl (s.a14 ^^^ d4) 39
  let b23 := rotl (s.a15 ^^^ d0) 41
  let b24 := rotl (s.a21 ^^^ d1) 2
  ⟨b0 ^^^ (~~~b1 &&& b2) ^^^ rc,
   b1 ^^^ (~~~b2 &&& b3),
   b2 ^^^ (~~~b3 &&& b4),
   b3 ^^^ (~~~b4 &&& b0),
   b4 ^^^ (~~~b0 &&& b1),
   b5 ^^^ (~~~b6 &&& b7),
   b6 ^^^ (~~~b7 &&& b8),
   b7 ^^^ (~~~b8 &&& b9),
   b8 ^^^ (~~~b9 &&& b5),
   b9 ^^^ (~~~b5 &&& b6),
   b10 ^^^ (~~~b11 &&& b12),
   b11 ^^^ (~~~b12 &&& b13),
   b12 ^^^ (~~~b13 &&& b14),
   b13 ^^^ (~~~b14 &&& b10),
   b14 ^^^ (~~~b10 &&& b11),
   b15 ^^^ (~~~b16 &&& b17),
   b16 ^^^ (~~~b17 &&& b18),
   b17 ^^^ (~~~b18 &&& b19),
   b18 ^^^ (~~~b19 &&& b15),
   b19 ^^^ (~~~b15 &&& b16),
   b20 ^^^ (~~~b21 &&& b22),
   b21 ^^^ (~~~b22 &&& b23),
   b22 ^^^ (~~~b23 &&& b24),
   b23 ^^^ (~~~b24 &&& b20),
   b24 ^^^ (~~~b20 &&& b21)⟩

/-- The 24 rounds of Keccak-f[1600], `f1600` on the lanes, with the round constants of
`roundConstants`. -/
def permute (s : Lanes) : Lanes :=
  let s := s.round 0x0000000000000001
  let s := s.round 0x0000000000008082
  let s := s.round 0x800000000000808A
  let s := s.round 0x8000000080008000
  let s := s.round 0x000000000000808B
  let s := s.round 0x0000000080000001
  let s := s.round 0x8000000080008081
  let s := s.round 0x8000000000008009
  let s := s.round 0x000000000000008A
  let s := s.round 0x0000000000000088
  let s := s.round 0x0000000080008009
  let s := s.round 0x000000008000000A
  let s := s.round 0x000000008000808B
  let s := s.round 0x800000000000008B
  let s := s.round 0x8000000000008089
  let s := s.round 0x8000000000008003
  let s := s.round 0x8000000000008002
  let s := s.round 0x8000000000000080
  let s := s.round 0x000000000000800A
  let s := s.round 0x800000008000000A
  let s := s.round 0x8000000080008081
  let s := s.round 0x8000000000008080
  let s := s.round 0x0000000080000001
  s.round 0x8000000080008008

/-- Lane `x` XORed with the 8 bytes `g o, …, g (o + 7)`, little-endian: the first into its low
byte. -/
@[inline] def xorLane (x : UInt64) (g : Nat → UInt8) (o : Nat) : UInt64 :=
  x ^^^ (g o).toUInt64 ^^^ (g (o + 1)).toUInt64 <<< 8 ^^^ (g (o + 2)).toUInt64 <<< 16 ^^^
    (g (o + 3)).toUInt64 <<< 24 ^^^ (g (o + 4)).toUInt64 <<< 32 ^^^
    (g (o + 5)).toUInt64 <<< 40 ^^^ (g (o + 6)).toUInt64 <<< 48 ^^^ (g (o + 7)).toUInt64 <<< 56

/-- The 136 bytes `g 0, …, g 135` of a block XORed into the first 17 lanes, 8 to a lane, which
is what the readable `absorb` does a byte at a time. The code that runs does it with
`xorLaneAt` and `xorLanePad`, a lane per call (`absorbBlock_eq`, `absorbLast_eq`). -/
def xorBlock (s : Lanes) (g : Nat → UInt8) : Lanes :=
  ⟨xorLane s.a0 g 0, xorLane s.a1 g 8, xorLane s.a2 g 16, xorLane s.a3 g 24, xorLane s.a4 g 32,
   xorLane s.a5 g 40, xorLane s.a6 g 48, xorLane s.a7 g 56, xorLane s.a8 g 64, xorLane s.a9 g 72,
   xorLane s.a10 g 80, xorLane s.a11 g 88, xorLane s.a12 g 96, xorLane s.a13 g 104,
   xorLane s.a14 g 112, xorLane s.a15 g 120, xorLane s.a16 g 128, s.a17, s.a18, s.a19, s.a20,
   s.a21, s.a22, s.a23, s.a24⟩

/-- Byte `i` of `b`, `0` past its end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt8 := b[i]?.getD 0

/-- Lane `x` XORed with the 8 bytes of `b` from byte `o` on. -/
def xorLaneAt (x : UInt64) (b : ByteArray) (o : Nat) : UInt64 := xorLane x (byteAt b) o

/-- The block of `b` at byte `off`, absorbed: XORed in a lane at a time, then permuted. -/
def absorbBlock (s : Lanes) (b : ByteArray) (off : Nat) : Lanes :=
  permute ⟨xorLaneAt s.a0 b off, xorLaneAt s.a1 b (off + 8), xorLaneAt s.a2 b (off + 16),
    xorLaneAt s.a3 b (off + 24), xorLaneAt s.a4 b (off + 32), xorLaneAt s.a5 b (off + 40),
    xorLaneAt s.a6 b (off + 48), xorLaneAt s.a7 b (off + 56), xorLaneAt s.a8 b (off + 64),
    xorLaneAt s.a9 b (off + 72), xorLaneAt s.a10 b (off + 80), xorLaneAt s.a11 b (off + 88),
    xorLaneAt s.a12 b (off + 96), xorLaneAt s.a13 b (off + 104), xorLaneAt s.a14 b (off + 112),
    xorLaneAt s.a15 b (off + 120), xorLaneAt s.a16 b (off + 128), s.a17, s.a18, s.a19, s.a20,
    s.a21, s.a22, s.a23, s.a24⟩

/-- `count` blocks of `b`, the first at byte `off`, absorbed in order. -/
def absorbBlocks (b : ByteArray) (off : Nat) : (count : Nat) → Lanes → Lanes
  | 0, s => s
  | count + 1, s => absorbBlocks b (off + 136) count (absorbBlock s b off)

/-- Byte `j` of the final, padded block, which starts at byte `base` of `b`: `b`'s byte while
there is one, `0x01` right after the last, zeros, and `0x80` ORed into the block's last byte (the
original Keccak padding, `0x01 ‥ 0x80`, which is `0x81` when it is a single byte). -/
def padByte (b : ByteArray) (base j : Nat) : UInt8 :=
  let i := base + j
  let v : UInt8 := if i < b.size then b[i]?.getD 0 else if i = b.size then 0x01 else 0
  if j = 135 then v ||| 0x80 else v

/-- Lane `x` XORed with bytes `o, …, o + 7` of the final block, which starts at byte `base` of
`b`, padded (`padByte`). -/
def xorLanePad (x : UInt64) (b : ByteArray) (base o : Nat) : UInt64 := xorLane x (padByte b base) o

/-- The final block, from byte `base` of `b` on, padded and absorbed. -/
def absorbLast (s : Lanes) (b : ByteArray) (base : Nat) : Lanes :=
  permute ⟨xorLanePad s.a0 b base 0, xorLanePad s.a1 b base 8, xorLanePad s.a2 b base 16,
    xorLanePad s.a3 b base 24, xorLanePad s.a4 b base 32, xorLanePad s.a5 b base 40,
    xorLanePad s.a6 b base 48, xorLanePad s.a7 b base 56, xorLanePad s.a8 b base 64,
    xorLanePad s.a9 b base 72, xorLanePad s.a10 b base 80, xorLanePad s.a11 b base 88,
    xorLanePad s.a12 b base 96, xorLanePad s.a13 b base 104, xorLanePad s.a14 b base 112,
    xorLanePad s.a15 b base 120, xorLanePad s.a16 b base 128, s.a17, s.a18, s.a19, s.a20, s.a21,
    s.a22, s.a23, s.a24⟩

/-- The 8 bytes of a lane appended to `b`, least significant first. -/
@[inline] def putLane (b : ByteArray) (x : UInt64) : ByteArray :=
  let b := b.push (x &&& 0xFF).toUInt8
  let b := b.push (x >>> 8 &&& 0xFF).toUInt8
  let b := b.push (x >>> 16 &&& 0xFF).toUInt8
  let b := b.push (x >>> 24 &&& 0xFF).toUInt8
  let b := b.push (x >>> 32 &&& 0xFF).toUInt8
  let b := b.push (x >>> 40 &&& 0xFF).toUInt8
  let b := b.push (x >>> 48 &&& 0xFF).toUInt8
  b.push (x >>> 56 &&& 0xFF).toUInt8

/-- The 32-byte digest: the first four lanes, little-endian, which is `squeeze s 32`. -/
def digest (s : Lanes) : ByteArray :=
  putLane (putLane (putLane (putLane (ByteArray.emptyWithCapacity 32) s.a0) s.a1) s.a2) s.a3

end Lanes

/-- EVM `keccak256` as it runs: the whole blocks of `input` absorbed in place, then the final
block padded as it is read, then the digest. `keccak256_eq_fast` proves it is `keccak256`. -/
def keccak256Fast (input : ByteArray) : ByteArray :=
  let n := input.size / 136
  (Lanes.absorbLast (Lanes.absorbBlocks input 0 n Lanes.zero) input (n * 136)).digest

/-! ## One round -/

theorem rotl64_zero (x : UInt64) : rotl64 x 0 = x := by
  have h : x >>> 64 = x := UInt64.toBitVec_inj.mp (by simp)
  simp [rotl64, h]

theorem piLUT_lit : piLUT =
    #[0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4] :=
  rfl

private theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl

private theorem range25 : List.range 25 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] :=
  rfl

theorem zero_toArray : Lanes.zero.toArray = Array.replicate 25 0 := rfl

private theorem replicate25 : Array.replicate 25 (0 : UInt64) =
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
  rfl

/-- One readable round on the lanes of `s` is `Lanes.round`. -/
theorem round_toArray (s : Lanes) (rc : UInt64) : round s.toArray rc = (s.round rc).toArray := by
  -- Evaluate the readable round's arrays, lookup tables and fold at 25 symbolic lanes.
  simp only [round, Lanes.toArray, range5, range25, replicate25, piLUT_lit, rhoLUT,
    List.map_toArray, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero, List.getElem?_toArray,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, Nat.reduceMod,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, rotl64_zero]
  -- Both sides now rotate by literal amounts: make them the same shifts.
  simp only [Lanes.round, rotl64, Lanes.rotl, Nat.toUInt64_eq, UInt64.reduceOfNat, Nat.reduceSub,
    UInt64.reduceSub]

/-! ## The permutation -/

private theorem range24 : List.range 24 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] :=
  rfl

/-- The readable permutation on the lanes of `s` is `Lanes.permute`. -/
theorem f1600_toArray (s : Lanes) : f1600 s.toArray = s.permute.toArray := by
  simp only [f1600, range24, List.foldl_cons, List.foldl_nil, roundConstants,
    List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    round_toArray]
  rfl

/-! ## The sponge -/

private theorem foldl_congr {α β : Type} (f g : α → β → α) (a : α) (l : List β)
    (h : ∀ x ∈ l, ∀ y, f y x = g y x) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (List.mem_cons_self) a]
    exact ih _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The readable `absorb`'s inner loop, which XORs the block's byte `i`, here `g i`, into lane
`i / 8`, is `Lanes.xorBlock` with any `h` equal to `g` on the block. -/
theorem xorBytes_toArray (s : Lanes) (g h : Nat → UInt8) (hg : ∀ i < 136, g i = h i) :
    (List.range' 0 136).foldl (fun b a => b.setIfInBounds (a / 8)
      (b[a / 8]?.getD 0 ^^^ (g a).toNat.toUInt64 <<< (a % 8 * 8).toUInt64)) s.toArray =
    (s.xorBlock h).toArray := by
  rw [foldl_congr _ (fun b a => b.setIfInBounds (a / 8)
      (b[a / 8]?.getD 0 ^^^ (h a).toNat.toUInt64 <<< (a % 8 * 8).toUInt64)) _ _
    (fun x hx y => by rw [hg x (by simp only [List.mem_range'_1] at hx; omega)])]
  simp only [List.range'_succ, List.range'_zero, Nat.reduceAdd, List.foldl_cons, List.foldl_nil,
    Lanes.toArray, List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero,
    List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.toUInt64_eq, UInt64.reduceOfNat,
    UInt64.ofNat_uInt8ToNat, UInt64.shiftLeft_zero, Lanes.xorBlock, Lanes.xorLane]

/-- `Lanes.absorbBlock`, a lane per call, is `Lanes.xorBlock` of the block's bytes, permuted. -/
theorem absorbBlock_eq (s : Lanes) (b : ByteArray) (off : Nat) :
    s.absorbBlock b off = (s.xorBlock fun i => b[off + i]?.getD 0).permute := by
  simp only [Lanes.absorbBlock, Lanes.xorBlock, Lanes.xorLaneAt, Lanes.xorLane, Lanes.byteAt,
    Nat.add_assoc, Nat.add_zero, Nat.zero_add, Nat.reduceAdd]

/-- `Lanes.absorbLast`, a lane per call, is `Lanes.xorBlock` of the padded block, permuted. -/
theorem absorbLast_eq (s : Lanes) (b : ByteArray) (base : Nat) :
    s.absorbLast b base = (s.xorBlock (Lanes.padByte b base)).permute :=
  rfl

/-- One block of the readable `absorb`, read from `P` at block `k`, is `Lanes.absorbBlock` of
`input` where the two agree on it. -/
theorem absorbBlock_toArray (s : Lanes) (input P : ByteArray) (k : Nat)
    (h : ∀ i < 136, P[k * 136 + i]?.getD 0 = input[k * 136 + i]?.getD 0) :
    f1600 ((List.range' 0 136).foldl (fun b a => b.setIfInBounds (a / 8)
      (b[a / 8]?.getD 0 ^^^ (P[k * 136 + a]?.getD 0).toNat.toUInt64 <<< (a % 8 * 8).toUInt64))
      s.toArray) = (s.absorbBlock input (k * 136)).toArray := by
  rw [xorBytes_toArray s _ (fun i => input[k * 136 + i]?.getD 0) h, f1600_toArray,
    absorbBlock_eq]

/-- The readable `absorb`'s loop over the whole blocks `k, …, k + m - 1` of `P`, which agrees
with `input` on them, is `Lanes.absorbBlocks`. -/
theorem absorbBlocks_toArray (input P : ByteArray)
    (hfull : ∀ i < input.size / 136 * 136, P[i]?.getD 0 = input[i]?.getD 0) (m : Nat) :
    ∀ (k : Nat) (s : Lanes), k + m ≤ input.size / 136 →
    (List.range' k m).foldl (fun b a => f1600 ((List.range' 0 136).foldl (fun b a_1 =>
      b.setIfInBounds (a_1 / 8) (b[a_1 / 8]?.getD 0 ^^^
        (P[a * 136 + a_1]?.getD 0).toNat.toUInt64 <<< (a_1 % 8 * 8).toUInt64)) b))
      s.toArray = (Lanes.absorbBlocks input (k * 136) m s).toArray := by
  induction m with
  | zero => intro k s _; rfl
  | succ m ih =>
    intro k s hk
    rw [List.range'_succ (s := k), List.foldl_cons,
      absorbBlock_toArray s input P k (fun i hi => hfull _ (by omega)), ih (k + 1) _ (by omega)]
    simp only [Lanes.absorbBlocks, Nat.succ_mul]

/-- The readable `absorb`'s loop over a padded input `P`, which is `input`'s whole blocks, then
one final block of `Lanes.padByte`s, is `Lanes.absorbBlocks` then `Lanes.absorbLast`. -/
theorem absorbPadded_toArray (input P : ByteArray)
    (hsize : P.size / 136 = input.size / 136 + 1)
    (hfull : ∀ i < input.size / 136 * 136, P[i]?.getD 0 = input[i]?.getD 0)
    (hlast : ∀ j < 136, P[input.size / 136 * 136 + j]?.getD 0 =
      Lanes.padByte input (input.size / 136 * 136) j) :
    (List.range' 0 (P.size / 136)).foldl (fun b a => f1600 ((List.range' 0 136).foldl
      (fun b a_1 => b.setIfInBounds (a_1 / 8) (b[a_1 / 8]?.getD 0 ^^^
        (P[a * 136 + a_1]?.getD 0).toNat.toUInt64 <<< (a_1 % 8 * 8).toUInt64)) b))
      (Array.replicate 25 0) =
    (Lanes.absorbLast (Lanes.absorbBlocks input 0 (input.size / 136) Lanes.zero) input
      (input.size / 136 * 136)).toArray := by
  rw [hsize, List.range'_concat (s := 0) (n := input.size / 136), List.foldl_append,
    ← zero_toArray, absorbBlocks_toArray input P hfull _ 0 _ (by omega)]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul, Nat.zero_mul]
  rw [xorBytes_toArray _ _ (Lanes.padByte input (input.size / 136 * 136)) hlast, f1600_toArray,
    absorbLast_eq]

/-- Byte `i` of a byte array `a` with the bytes `L` appended. -/
private theorem getElem?_append_mk (a : ByteArray) (L : Array UInt8) (i : Nat) :
    (a ++ ⟨L⟩)[i]? = if i < a.size then a[i]? else L[i - a.size]? := by
  show (a ++ ⟨L⟩).data[i]? = _
  rw [ByteArray.data_append, Array.getElem?_append]
  rfl

/-- The readable `absorb` with Keccak-256's rate and padding is `Lanes.absorbBlocks` then
`Lanes.absorbLast`. -/
theorem absorb_toArray (input : ByteArray) :
    absorb input 136 0x01 = (Lanes.absorbLast (Lanes.absorbBlocks input 0 (input.size / 136)
      Lanes.zero) input (input.size / 136 * 136)).toArray := by
  unfold absorb
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, pure_bind,
    List.forIn_pure_yield_eq_foldl, bind_pure, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have hr := Nat.mod_lt input.size (show 136 > 0 by decide)
  refine absorbPadded_toArray input _ ?_ ?_ ?_
  · -- The padding is `136 - input.size % 136` bytes: one block more than the whole blocks.
    rw [ByteArray.size_append]
    show (input.size + List.length (if _ then _ else _)) / 136 = _
    split <;> simp only [List.length_cons, List.length_nil, List.length_append,
      List.length_replicate] <;> omega
  · -- Before the final block, the padded input is the input.
    intro i hi
    rw [getElem?_append_mk, ite_eq_left (show i < input.size by omega)]
  · -- The final block: the input's last bytes, then the padding, as `padByte` reads it.
    intro j hj
    rw [getElem?_append_mk, List.getElem?_toArray]
    simp only [Lanes.padByte]
    by_cases hi : input.size / 136 * 136 + j < input.size
    · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_right (show ¬j = 135 by omega)]
    · rw [ite_eq_right hi, ite_eq_right hi,
        show input.size / 136 * 136 + j - input.size = j - input.size % 136 by omega]
      by_cases hp : 136 - input.size % 136 = 1
      · -- One byte of padding, `0x01 ||| 0x80`, the block's last.
        rw [ite_eq_left hp, show j - input.size % 136 = 0 by omega,
          ite_eq_left (show j = 135 by omega),
          ite_eq_left (show input.size / 136 * 136 + j = input.size by omega)]
        rfl
      · rw [ite_eq_right hp]
        by_cases he : input.size / 136 * 136 + j = input.size
        · -- The first byte of padding, `0x01`.
          rw [show j - input.size % 136 = 0 by omega, ite_eq_right (show ¬j = 135 by omega),
            ite_eq_left he]
          rfl
        · rw [ite_eq_right he,
            show j - input.size % 136 = (j - input.size % 136 - 1) + 1 by omega,
            List.getElem?_cons_succ]
          by_cases h135 : j = 135
          · -- The last byte of padding, `0x80`.
            rw [ite_eq_left h135, List.getElem?_append_right (by
              simp only [List.length_replicate]; omega), List.length_replicate,
              show j - input.size % 136 - 1 - (136 - input.size % 136 - 2) = 0 by omega]
            decide
          · -- Zeros in between.
            rw [ite_eq_right h135, List.getElem?_append_left (by
              simp only [List.length_replicate]; omega), List.getElem?_replicate_of_lt (by omega)]
            rfl

private theorem emptyWithCapacity_32 : ByteArray.emptyWithCapacity 32 = ByteArray.empty := rfl

/-- The readable `squeeze` of 32 bytes from the lanes of `s` is `Lanes.digest`. -/
theorem squeeze_toArray (s : Lanes) : squeeze s.toArray 32 = s.digest := by
  unfold squeeze
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.div_one, List.range'_succ,
    List.range'_zero, Nat.reduceAdd, List.foldl_cons, List.foldl_nil, Lanes.toArray,
    List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.toUInt64_eq, UInt64.reduceOfNat,
    UInt64.shiftRight_zero, Lanes.digest, Lanes.putLane, emptyWithCapacity_32]
  rfl

/-- `keccak256Fast` is `keccak256` on every input. As a `csimp` equation, it makes code
compiled where this file is imported call `keccak256Fast` wherever its source calls
`keccak256`. -/
@[csimp] theorem keccak256_eq_fast : @keccak256 = @keccak256Fast := by
  funext input
  rw [keccak256, absorb_toArray, squeeze_toArray]
  rfl

end LeanLight.Spec.Keccak
