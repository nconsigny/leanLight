import LeanLight.Bls.Fav
import LeanLightTests.Bls.Layer

/-!
# The light client's BLS layer (`LeanLight.Bls`) under test

`runtime` is the `Layer` over `LeanLight.Bls`, the code `lkd-lc` runs; Ethereum's wrappers are
built here from its pieces, as the light client does not call them. `selfTests` are the
benchmark's checks, kept: the tower's identities, the curves' generators, points outside the
subgroups, the pairing's bilinearity and order, the final exponentiation's cube, and the
endomorphism tests against `[r]P`. `timings` measures an update and a committee.
-/

namespace LeanLight.Tests.Bls

open LeanLight.Lc.Bls

def g2Pt (q : G2A) : Pt2 := (q.x.c0, q.x.c1, q.y.c0, q.y.c1)

/-- The light client's layer. -/
def runtime : Layer where
  name := "runtime"
  fav pks msg sig := fastAggregateVerifyBytes pks.toArray msg sig
  ethFav pks msg sig :=
    if pks.isEmpty then isIdentity96 sig else fastAggregateVerifyBytes pks.toArray msg sig
  ethAgg pks :=
    if pks.isEmpty then none else
    (pks.toArray.mapM keyValidate?).map fun keys =>
      (keys.foldl (fun acc p => acc.addA p) G1J.inf).compress
  deserG1 b := isIdentity48 b || (keyValidate? b).isSome
  deserG2 b := isIdentity96 b || (sigValidate? b).isSome
  sign sk msg :=
    if sk = 0 || sk ≥ R then none
    else (H2C.hashToG2? msg ethDst).map fun h => (G2J.mulA h sk).compress
  h2g msg dst := (H2C.hashToG2? msg dst).map g2Pt
  h2f msg dst := let (u0, u1) := H2C.hashToField msg dst; some ((u0.c0, u0.c1), (u1.c0, u1.c1))
  map u := ((H2C.sswu? ⟨u.1, u.2⟩).bind fun q => (H2C.isoMap q).toAffine?).map g2Pt
  sha256 := Ssz.Sha256.hash

/-- `a^e` in `Fp12`, square-and-multiply (tests only). -/
def fp12Pow (a : Fp12) (e : Nat) : Fp12 := Id.run do
  let mut acc := Fp12.one
  let n := Nat.log2 e + 1
  for k in [0:n] do
    acc := acc.sqr
    if (e >>> (n - 1 - k)) % 2 = 1 then acc := acc.mul a
  return acc

def g1Aff (p : G1J) : G1A := p.toAffine?.getD ⟨0, 0⟩
def g2Aff (p : G2J) : G2A := p.toAffine?.getD ⟨Fp2.zero, Fp2.zero⟩

/-- A point of `E(Fp)` outside G1: the first `x ≥ 1` with `x³ + 4` a square and not in G1. -/
def nonG1 : G1A := Id.run do
  let mut out : G1A := ⟨0, 2⟩
  for x in [1:100] do
    match fsqrt? (fadd (fmul (fsqr x) x) 4) with
    | some y => if !(G1A.inSubgroup ⟨x, y⟩) then return ⟨x, y⟩ else out := ⟨x, y⟩
    | none => pure ()
  return out

/-- A point of `E'(Fp2)` outside G2. -/
def nonG2 : G2A := Id.run do
  let mut out : G2A := ⟨Fp2.zero, Fp2.zero⟩
  for k in [1:100] do
    let x : Fp2 := ⟨k, 1⟩
    match (x.sqr.mul x |>.add bTwist).sqrt? with
    | some y => if !(G2A.inSubgroup ⟨x, y⟩) then return ⟨x, y⟩ else out := ⟨x, y⟩
    | none => pure ()
  return out

/-- The benchmark's checks, and the endomorphism tests against `[r]P` on every key and
signature of the vectors that decompresses. `z` is 0 at run time, unknown to the compiler. -/
def selfTests (z : Nat) : IO Tally := do
  let mut t : Tally := {}
  let a : Nat := 0x123456789abcdef0123456789abcdef0123456789abcdef + z
  t := t.add "fp inverse" (fmul a (finv a) = 1)
  t := t.add "fp sqrt" (match fsqrt? (fsqr a) with | some y => fsqr y = fsqr a | none => false)
  let a2 : Fp2 := ⟨a, a + 7⟩
  t := t.add "fp2 inverse" ((a2.mul a2.inv).eq Fp2.one)
  t := t.add "fp2 sqrt" (match a2.sqr.sqrt? with | some y => y.sqr.eq a2.sqr | none => false)
  t := t.add "fp2 isSquare" (a2.sqr.isSquare && !(a2.sqr.mul H2C.sswuZ).isSquare)
  let a6 : Fp6 := ⟨a2, a2.sqr, a2.mulXi⟩
  t := t.add "fp6 sqr = mul" (a6.sqr.eq (a6.mul a6))
  t := t.add "fp6 inverse" ((a6.mul a6.inv).eq Fp6.one)
  let a12 : Fp12 := ⟨a6, a6.sqr⟩
  t := t.add "fp12 sqr = mul" (a12.sqr.eq (a12.mul a12))
  t := t.add "fp12 inverse" (a12.mul a12.inv).isOne
  t := t.add "fp12 frob = pow P" (a12.frob.eq (fp12Pow a12 P))
  let g1 := G1J.ofAffine g1Gen
  let g2 := G2J.ofAffine g2Gen
  t := t.add "g1 on E, [r]g1 = O" (g1Gen.onCurve && g1Gen.inSubgroup)
  t := t.add "g2 on E', [r]g2 = O" (g2Gen.onCurve && g2Gen.inSubgroup)
  t := t.add "Scott's test accepts g1, psi's g2" (g1Gen.inSubgroupScott && g2Gen.inSubgroupPsi)
  let bad1 := nonG1
  t := t.add "a point of E outside G1 refused by both tests"
    (bad1.onCurve && !bad1.inSubgroup && !bad1.inSubgroupScott && (keyValidate? bad1.compress).isNone)
  let bad2 := nonG2
  t := t.add "a point of E' outside G2 refused by both tests"
    (bad2.onCurve && !bad2.inSubgroup && !bad2.inSubgroupPsi && (sigValidate? bad2.compress).isNone)
  let p7 := g1Aff (G1J.mulA g1Gen (7 + z))
  t := t.add "[7]g1 = g1 + ... + g1" ((G1J.mulA g1Gen 7).eq
    (g1.add g1 |>.add g1 |>.add g1 |>.add g1 |>.add g1 |>.add g1))
  t := t.add "addA = add" ((g1.addA p7).eq (g1.add (G1J.ofAffine p7)))
  let q5 := g2Aff (G2J.mulA g2Gen (5 + z))
  t := t.add "g2 addA = add" ((g2.addA q5).eq (g2.add (G2J.ofAffine q5)))
  t := t.add "g1 compress, decompress" (g1Decompress? p7.compress == some p7)
  t := t.add "g2 compress, decompress" (g2Decompress? q5.compress == some q5)
  t := t.add "[r - 1]g1 = -g1, [r - 1]g2 = -g2"
    ((G1J.mulA g1Gen (R - 1)).eq g1.neg && (G2J.mulA g2Gen (R - 1)).eq g2.neg)
  -- The pairing.
  let e := finalExp (millerLoop [(g1Gen, g2Gen)])
  t := t.add "e(g1, g2) != 1" (!e.isOne)
  t := t.add "e(g1, g2)^r = 1" (fp12Pow e R).isOne
  let sa := 0x1234567 + z
  let sb := 0x89abcdef + z
  let eab := finalExp (millerLoop [(g1Aff (G1J.mulA g1Gen sa), g2Aff (G2J.mulA g2Gen sb))])
  t := t.add "bilinear: e(aP, bQ) = e(P, Q)^(ab)" (eab.eq (fp12Pow e (sa * sb % R)))
  let e2 := finalExp (millerLoop [(g1Aff (G1J.mulA g1Gen 2), g2Gen)])
  t := t.add "e(2P, Q) = e(P, Q)^2" (e2.eq (e.mul e))
  let ml := millerLoop [(g1Gen, g2Gen)]
  let naive := fp12Pow ml ((P ^ 12 - 1) / R)
  t := t.add "finalExp is the cube of f^((p^12 - 1)/r)" (e.eq (naive.mul naive |>.mul naive))
  t := t.add "and not f^((p^12 - 1)/r) itself" (!e.eq naive)
  let pab := g1Aff (G1J.mulA g1Gen (sa * sb % R))
  let qab := g2Aff (G2J.mulA g2Gen (sa * sb % R))
  t := t.add "pairingCheck e(g1, abQ) e(-abP, Q) = 1"
    (pairingCheck [(g1Gen, qab), (pab.neg, g2Gen)])
  t := t.add "pairingCheck refuses a wrong product"
    (!pairingCheck [(g1Gen, g2Aff (G2J.mulA g2Gen (sa * sb % R + 1))), (pab.neg, g2Gen)])
  -- hash_to_G2's pieces.
  let (u0, u1) := H2C.hashToField "abc".toUTF8 ethDst
  let r0 := (H2C.sswu? u0).map H2C.isoMap
  let r1 := (H2C.sswu? u1).map H2C.isoMap
  match r0, r1 with
  | some r0, some r1 =>
    let rsum := r0.add r1
    t := t.add "SSWU then the isogeny lands on E'" ((g2Aff r0).onCurve && (g2Aff r1).onCurve)
    t := t.add "SSWU lands on E''" (match H2C.sswu? u0 with
      | some q => q.y.sqr.eq (H2C.gIso q.x) | none => false)
    let h := H2C.clearCofactor rsum
    t := t.add "clear_cofactor's result is in G2" ((g2Aff h).inSubgroup)
  | _, _ => t := t.add "SSWU refused hash_to_field(\"abc\")" false
  -- The endomorphism tests agree with [r]P on the vectors' keys and signatures.
  let mut keys : Array ByteArray := #[]
  let mut sigs : Array ByteArray := #[]
  for v in Vectors.ethFav ++ Vectors.blsFav ++ Vectors.blsVerify do
    keys := keys ++ (v.pubkeys.map unhex).toArray
    sigs := sigs.push (unhex v.signature)
  for v in Vectors.blsG1 do keys := keys.push (unhex v.bytes)
  for v in Vectors.blsG2 do sigs := sigs.push (unhex v.bytes)
  let mut agreeG1 := true
  let mut agreeG2 := true
  let mut n1 := 0
  let mut n2 := 0
  for k in keys do
    if let some p := g1Decompress? k then
      n1 := n1 + 1
      agreeG1 := agreeG1 && p.inSubgroup == p.inSubgroupScott
  for s in sigs do
    if let some q := g2Decompress? s then
      n2 := n2 + 1
      agreeG2 := agreeG2 && q.inSubgroup == q.inSubgroupPsi
  t := t.add s!"Scott's test = [r]P on {n1} keys" agreeG1
  t := t.add s!"psi's test = [r]Q on {n2} signatures" agreeG2
  return t

/-- The keys `[i + 1]g1` for `i < 512`, compressed, and their secret sum `512·513/2`. -/
def committee (z : Nat) : Array ByteArray := Id.run do
  let g := G1J.ofAffine ⟨g1Gen.x + z, g1Gen.y⟩
  let mut acc := g
  let mut out : Array ByteArray := #[]
  for _ in [0:512] do
    out := out.push acc.compress
    acc := acc.add g
  return out

/-- An update's verification and a committee's KeyValidates, timed: best of `reps` runs. -/
def timings (z reps : Nat) : IO (Tally × Nat × Nat) := do
  let mut t : Tally := {}
  let pkBytes := committee z
  let keys := (pkBytes.mapM keyValidate?).getD #[]
  t := t.add "512 committee keys pass KeyValidate" (keys.size = 512)
  let root := ByteArray.mk ((Array.range 32).map fun i => (i + z).toUInt8)
  let sig := match H2C.hashToG2? root ethDst with
    | some h => (G2J.mulA h (512 * 513 / 2)).compress
    | none => ByteArray.empty
  t := t.add "a 512-key aggregate signature verifies" (fastAggregateVerify keys root sig)
  t := t.add "and not over 511 of the keys" (!fastAggregateVerify (keys.extract 0 511) root sig)
  let update ← timeBest 1 reps fun i =>
    if fastAggregateVerify keys (if i = 1000 then sig else root) sig then 1 else 0
  let committeeNs ← timeBest 1 (max 1 (reps / 4)) fun i =>
    (pkBytes.extract 0 (512 - i / 1000)).foldl (fun acc pk =>
      match keyValidate? pk with | some q => acc + q.x % 2 | none => acc) 0
  let agg ← timeBest 1 reps fun i => match aggregate? (keys.extract 0 (512 - i / 1000)) with
    | some a => a.x % 2 | none => 0
  let h2g ← timeBest 1 reps fun i => match H2C.hashToG2? (root.push i.toUInt8) ethDst with
    | some h => h.x.c0 % 2 | none => 0
  let sigCheck ← timeBest 1 reps fun i =>
    match sigValidate? (if i = 1000 then root else sig) with | some q => q.x.c0 % 2 | none => 0
  let hq := (H2C.hashToG2? root ethDst).getD g2Gen
  let sq := (sigValidate? sig).getD g2Gen
  let psiNs ← timeBest 1 reps fun i =>
    if (if i = 1000 then g2Gen else sq).inSubgroupPsi then 1 else 0
  let rqNs ← timeBest 1 reps fun i =>
    if (if i = 1000 then g2Gen else sq).inSubgroup then 1 else 0
  let aggA := (aggregate? keys).getD g1Gen
  let pairing ← timeBest 1 reps fun i =>
    if pairingCheck [(g1Gen, sq), ((if i = 1000 then g1Gen else aggA).neg, hq)] then 1 else 0
  let cof ← timeBest 1 reps fun i => (H2C.clearCofactor ⟨hq.x, hq.y, ⟨i + 1, 0⟩⟩).x.c0 % 2
  IO.println s!"TIME update (512 keys aggregated, hash_to_G2, signature decompressed and its subgroup check, 2-pair pairing check): {ms update}"
  IO.println s!"TIME   of which: aggregate 512 keys {ms agg}, hash_to_G2 {ms h2g} (clear_cofactor [h_eff]P {ms cof}), signature checks {ms sigCheck}, pairing check {ms pairing}"
  IO.println s!"TIME the signature's subgroup check: psi(Q) = [x]Q {ms psiNs} (what runs), [r]Q = O {ms rqNs}"
  IO.println s!"TIME committee: 512 x (decompress + KeyValidate with [r]P): {ms committeeNs}"
  return (t, update, committeeNs)

end LeanLight.Tests.Bls
