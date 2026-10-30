import LeanLight.Bls.Fp2

/-!
# BLS12-381: G2 on the twist `E': y² = x³ + 4(1 + u)` over `Fp2`

Moved from the benchmark's `Bls/Curve.lean` (see `LeanLight.Bls.Fp`), with a mixed addition added
(`addA`, madd-2007-bl), which the scalar multiplications by `r` and `h_eff` use. Points are
affine (`G2A`, never the identity) or Jacobian (`G2J`, `z = 0` the identity), with the formulas
of `LeanLight.Bls.G1` over `Fp2`.

**Subgroup membership** is `[r]Q = O` (`G2A.inSubgroup`), as the signature's checks state it.
What runs is Scott's test (eprint 2021/1130) by the endomorphism
`ψ = twist⁻¹ ∘ Frobenius ∘ twist`, `ψ(Q) = [x]Q` with `x = −X` the curve's parameter
(`G2A.inSubgroupPsi`): a double-and-add over `X`'s 64 bits instead of `r`'s 255, about six times
faster. `LeanLightProofs.Bls.ScottComplete` proves it sound and complete, so that on every reduced
point of `E'` it accepts exactly what `inSubgroup` accepts (`G2A.inSubgroupPsi_eq`), with no
fallback. `ψ`'s two constants are pinned (`psiX_eq`, `psiY_eq`), and that `ψ` acts on G2's
generator as `[x]` is checked (`psi_acts`), by the kernel.
-/

namespace LeanLight.Lc.Bls

/-- An affine point of `E'(Fp2)`, never the identity. -/
structure G2A where
  x : Fp2
  y : Fp2
deriving DecidableEq

/-- A point in Jacobian coordinates; `z = 0` is the identity. -/
structure G2J where
  x : Fp2
  y : Fp2
  z : Fp2

/-- `4(1 + u)`, the twist's `b`. -/
def bTwist : Fp2 := ⟨4, 4⟩

namespace G2J

@[inline] def inf : G2J := ⟨Fp2.one, Fp2.one, Fp2.zero⟩
@[inline] def ofAffine (p : G2A) : G2J := ⟨p.x, p.y, Fp2.one⟩
@[inline] def isInf (p : G2J) : Bool := p.z.isZero
@[inline] def neg (p : G2J) : G2J := ⟨p.x, p.y.neg, p.z⟩

/-- Doubling, dbl-2009-l. -/
def dbl (p : G2J) : G2J :=
  if p.z.isZero then p else
  let a := p.x.sqr
  let b := p.y.sqr
  let c := b.sqr
  let d := ((p.x.add b).sqr.sub a |>.sub c).dbl
  let e := a.dbl.add a
  let f := e.sqr
  let x3 := f.sub d.dbl
  let y3 := (e.mul (d.sub x3)).sub c.dbl.dbl.dbl
  let z3 := (p.y.mul p.z).dbl
  ⟨x3, y3, z3⟩

/-- Addition, add-2007-bl, with its special cases. -/
def add (p q : G2J) : G2J :=
  if p.z.isZero then q else if q.z.isZero then p else
  let z1z1 := p.z.sqr
  let z2z2 := q.z.sqr
  let u1 := p.x.mul z2z2
  let u2 := q.x.mul z1z1
  let s1 := (p.y.mul q.z).mul z2z2
  let s2 := (q.y.mul p.z).mul z1z1
  if u1.eq u2 then (if s1.eq s2 then dbl p else inf) else
  let h := u2.sub u1
  let i := h.dbl.sqr
  let j := h.mul i
  let r := (s2.sub s1).dbl
  let v := u1.mul i
  let x3 := (r.sqr.sub j).sub v.dbl
  let y3 := (r.mul (v.sub x3)).sub (s1.mul j).dbl
  let z3 := ((p.z.add q.z).sqr.sub z1z1 |>.sub z2z2).mul h
  ⟨x3, y3, z3⟩

/-- Mixed addition with an affine point, madd-2007-bl, with the same special cases. -/
def addA (p : G2J) (q : G2A) : G2J :=
  if p.z.isZero then ofAffine q else
  let z1z1 := p.z.sqr
  let u2 := q.x.mul z1z1
  let s2 := (q.y.mul p.z).mul z1z1
  if p.x.eq u2 then (if p.y.eq s2 then dbl p else inf) else
  let h := u2.sub p.x
  let hh := h.sqr
  let i := hh.dbl.dbl
  let j := h.mul i
  let r := (s2.sub p.y).dbl
  let v := p.x.mul i
  let x3 := (r.sqr.sub j).sub v.dbl
  let y3 := (r.mul (v.sub x3)).sub (p.y.mul j).dbl
  let z3 := ((p.z.add h).sqr.sub z1z1).sub hh
  ⟨x3, y3, z3⟩

/-- `[k]p` for an affine `p`: double-and-add from the most significant bit of `k`, with mixed
additions. -/
def mulA (p : G2A) (k : Nat) : G2J := Id.run do
  let mut acc := inf
  let n := Nat.log2 k + 1
  for i in [0:n] do
    acc := dbl acc
    if (k >>> (n - 1 - i)) % 2 = 1 then acc := addA acc p
  return acc

/-- Equality of the points two Jacobian triples stand for. -/
def eq (p q : G2J) : Bool :=
  if p.z.isZero then q.z.isZero else if q.z.isZero then false else
  let z1z1 := p.z.sqr
  let z2z2 := q.z.sqr
  (p.x.mul z2z2).eq (q.x.mul z1z1) &&
    ((p.y.mul q.z).mul z2z2).eq ((q.y.mul p.z).mul z1z1)

/-- The affine point, by one inversion; `none` for the identity. -/
def toAffine? (p : G2J) : Option G2A :=
  if p.z.isZero then none else
  let zi := p.z.inv
  let zi2 := zi.sqr
  some ⟨p.x.mul zi2, p.y.mul (zi2.mul zi)⟩

end G2J

namespace G2A

@[inline] def neg (p : G2A) : G2A := ⟨p.x, p.y.neg⟩

/-- On `E'`: `y² = x³ + 4(1 + u)`. -/
def onCurve (p : G2A) : Bool := p.y.sqr.eq ((p.x.sqr.mul p.x).add bTwist)

/-- Membership in G2 by `[r]q = O`: the check v1 runs. -/
def inSubgroup (p : G2A) : Bool := (G2J.mulA p R).isInf

end G2A

/-- G2's generator (draft-irtf-cfrg-pairing-friendly-curves, as EthLib's `G2.generator`). -/
def g2Gen : G2A :=
  ⟨⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
    0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩,
   ⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
    0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩⟩

/-! ## ψ: the subgroup test -/

/-- `ξ^(−(P−1)/3)` (`psiX_eq`). -/
def psiX : Fp2 :=
  ⟨0, 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad⟩

/-- `ξ^(−(P−1)/2)` (`psiY_eq`). -/
def psiY : Fp2 :=
  ⟨0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2,
   0x06af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09⟩

theorem psiX_eq : psiX = (Fp2.pow xi ((P - 1) / 3)).inv := by decide +kernel
theorem psiY_eq : psiY = (Fp2.pow xi ((P - 1) / 2)).inv := by decide +kernel

/-- `ψ(x, y) = (x̄·ξ^(−(P−1)/3), ȳ·ξ^(−(P−1)/2))`, on Jacobian coordinates. -/
@[inline] def G2J.psi (p : G2J) : G2J := ⟨p.x.conj.mul psiX, p.y.conj.mul psiY, p.z.conj⟩

theorem psi_acts : (G2J.ofAffine g2Gen).psi.eq (G2J.mulA g2Gen X).neg = true := by decide +kernel

/-- Membership in G2 by Scott's test `ψ(q) = [x]q`, `x = −X` negative: `ψ(q) = −[X]q`, as the
signature's checks run it. Equal to `inSubgroup` on the curve (`LeanLightProofs.Bls.ScottComplete`,
`G2A.inSubgroupPsi_eq`). -/
def G2A.inSubgroupPsi (p : G2A) : Bool := (G2J.ofAffine p).psi.eq (G2J.mulA p X).neg

end LeanLight.Lc.Bls
