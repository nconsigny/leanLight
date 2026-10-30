import LeanLightProofs.Spec.Mpt
import LeanLightProofs.Spec.Common

/-!
# The Yellow Paper's trie, and what `lookup` reads from it

`Spec.Mpt.binding` says that two proofs `lookup` accepts with different results hold a
Keccak-256 collision; it does not say that `lookup` reads the trie Ethereum commits to, as any
reader that follows hashes from the root deterministically binds as well. This module defines
that trie, from the Yellow Paper (`ethereum/yellowpaper`, `Paper.tex` at commit `efc5f9a1`,
Appendix D, with Appendix C's hex-prefix encoding and Appendix B's RLP, `Spec.Rlp`), and proves
`lookup` correct against it.

**The model**, written from Appendix D's equations, not from the code. A map `I` is a list of
pairs of byte sequences (𝔍); `y` reads its keys as nibbles; `compose` is the structural
composition function c(𝔍, i) (a leaf, an extension, or a branch of sixteen children and a
value) and `cap` the node cap function n(𝔍, i) (`()` for no pair, the node itself when its RLP
is shorter than 32 bytes, else the Keccak-256 of its RLP); `root I` is TRIE(𝔍) =
KEC(RLP(c(𝔍, 0))), and `emptyRoot` for the empty map (`root_nil`). `proofOf I k` is the proof
of `k` that geth's `Trie.Prove` builds (what its `eth_getProof` returns), in the stream form
`lookup` reads: the root node's RLP, then that of every node on `k`'s path that its parent names by
hash (an inline node is inside its parent). Not every node sends that proof: anvil (seen on 1.5.1)
also lists each inline node on the path as an item of its own (`proofOfFull`), which `lookup`
accepts as well (`lookup_complete_full`, and the `#guard`s at the end of the file). That happens in
storage tries, where a node below the root can be shorter than 32 bytes (a state trie's leaves hold
accounts, 70 bytes at least). For an empty trie geth sends nothing where `proofOf` is `0x80`;
`lookup_empty` accepts both. `get I k` is what `I` holds at `k`. The roots of `ethereum/tests`'
trie vectors are checked at the end of the file.

**Theorems**, for a `WellFormed` map: keys of at most 32 bytes (`maxKey`, the longest `lookup`
takes), values nonempty and shorter than 2^32 bytes. Keys need not share one length, nor be
prefix-free (a key's value then sits in a branch), nor be unique (Appendix D assumes they are;
`get` takes the first pair with a key).

- `lookup_complete` and `lookup_complete_full` (**completeness**): for every key `k` of at most
  32 bytes, `lookup (root I) k` returns `some (get I k)` on both `proofOf I k` (hashed nodes only)
  and `proofOfFull I k` (with standalone `< 32`-byte inline nodes included).
- `lookup_sound` (**soundness**): a proof `lookup` accepts for `k` under `root I` gives
  `get I k`, or the two byte strings `collision (root I) k proof (proofOf I k)` are different
  and have the same Keccak-256. With `binding`, this is what makes a proved read the map's
  value: forging one is exhibiting a Keccak-256 collision on those exact bytes. No axiom.

**Accounts and storage.** The state and storage tries are secure tries (section 4.1), keyed by
the Keccak-256 of the address or slot (`secure`). A `State` holds accounts at addresses, stored
as `accountRlp` (which `accountOf_iff` reads back), an absent one being `emptyAccount`; a
`Storage` holds nonzero values at slots, stored as `slotRlp` (`slotOf_iff`), an absent one
being zero (`StorageOk`). Accounts are `AccountValid` (the Yellow Paper's validity function);
one is read back only when it is `AccountOk` (a nonce below 2^64 and a balance below 2^128, the
code's bounds), which completeness asks of the account read alone, and soundness of none.
`account_complete`, `account_complete_full`, `storage_complete`, `storage_complete_full`,
`account_sound` and `storage_sound` are the completeness and soundness theorems for
`Spec.Mpt.account` and `Spec.Mpt.storage`, with one more pair named, as a hash of the key cannot
be assumed injective: `clash S a`, the first key of `S` with `a`'s Keccak-256, and `a`, which is a
collision exactly when the two differ.

The proof follows the walk down the honest proof (`walk_compose`, `walk_compose_full`): at the
node c(𝔍', i) for the pairs `𝔍'` whose keys start with `k`'s first `i` nibbles (`Under`), `step`
reads what Appendix D put there (`step_leaf`, `step_ext`, `step_branch`), the next node being
inline or the proof's next item (`child_cap`, `node_hashed`, `node_inline_composeProof`,
`node_inline_present`). Every node has an RLP encoding (`encodes`).
-/

namespace LeanLight.Spec.Mpt.Trie

open LeanLight.Spec.Rlp LeanLight.Spec.RlpDecode
open LeanLight.Spec.Header (keccak window_all window_drop)

/-! ## The trie (Yellow Paper, Appendices C and D) -/

/-- 𝔍 (Appendix D): the pairs of byte sequences a trie commits to, key then value, as a list.
`get` reads the first pair with a key. -/
abbrev Map := List (Bytes × Bytes)

/-- A pair of y(𝔍): its key as a sequence of nibbles (𝕐), and its value. -/
abbrev Entry := List Nat × Bytes

/-- A key's nibbles, y's k' (Appendix D), big-endian: of each byte `b`, `⌊b ÷ 16⌋` then
`b mod 16`. -/
def nibbles (k : Bytes) : List Nat := k.flatMap fun b => [b.toNat / 16, b.toNat % 16]

/-- y(𝔍) (Appendix D): every key as its nibbles. -/
def y (I : Map) : List Entry := I.map fun p => (nibbles p.1, p.2)

/-- f(t) of hex-prefix encoding (Appendix C): 2 for a leaf (`t`), 0 for an extension. -/
def hpFlag (t : Bool) : Nat := if t then 2 else 0

/-- `16x[0] + x[1], 16x[2] + x[3], ...`: an even number of nibbles, two to a byte (`hp` packs
only an even number, so a last odd nibble never arises). -/
def pack : List Nat → Bytes
  | a :: b :: x => (16 * a + b).toUInt8 :: pack x
  | _ => []

/-- HP(x, t), hex-prefix encoding (Appendix C): the first byte's high nibble is `f(t)`, plus 1
when `x` has an odd number of nibbles, in which case its low nibble is `x[0]` (else 0); the
remaining nibbles follow two to a byte. -/
def hp (x : List Nat) (t : Bool) : Bytes :=
  if x.length % 2 = 0 then (16 * hpFlag t).toUInt8 :: pack x
  else (16 * (hpFlag t + 1) + x.headD 0).toUInt8 :: pack x.tail

/-- The longest common prefix of two sequences. -/
def lcp : List Nat → List Nat → List Nat
  | a :: x, b :: z => if a = b then a :: lcp x z else []
  | _, _ => []

/-- The longest prefix all the keys of a nonempty 𝔍 share: its length is the `j` of c's
extension case, `max {x : ∃l : ‖l‖ = x ∧ ∀I ∈ 𝔍 : I₀[0 .. (x − 1)] = l}` (Appendix D). -/
def common : List Entry → List Nat
  | [] => []
  | [e] => e.1
  | e :: J => lcp e.1 (common J)

/-- The nibbles the keys of 𝔍 have past the first `i`, plus one for each pair: what `compose`
and `cap` recurse down. -/
def size (J : List Entry) (i : Nat) : Nat := (J.map fun e => e.1.length - i + 1).sum

/-- The value in the 17th item of c's branch case (Appendix D): `I₁` if some `I ∈ 𝔍` has a
key of `i` nibbles, else `()`. -/
def terminal (J : List Entry) (i : Nat) : Bytes :=
  match J.find? (fun e => e.1.length = i) with
  | some e => e.2
  | none => []

/-- `{I : I ∈ 𝔍 ∧ I₀[i] = x}` (Appendix D, the branch case's `u(x)`): the pairs whose key's
nibble `i` is `x`. -/
def sub (J : List Entry) (i x : Nat) : List Entry := J.filter fun e => e.1[i]? = some x

/-- RLP (Appendix B): `Spec.Rlp.encodeTree` as a byte sequence. RLP fails only on a byte
array or a sequence of 2^64 bytes or more, which no node of a `WellFormed` map reaches
(`encodes`), so the empty default is never taken there. -/
def rlp (t : Tree) : Bytes := (encodeTree t).getD []

private theorem lcp_prefix_left : ∀ a b : List Nat, lcp a b <+: a
  | a :: x, b :: z => by
    unfold lcp; split
    · exact (List.prefix_cons_inj a).mpr (lcp_prefix_left x z)
    · exact List.nil_prefix
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

private theorem lcp_prefix_right : ∀ a b : List Nat, lcp a b <+: b
  | a :: x, b :: z => by
    unfold lcp; split
    · rename_i h; subst h; exact (List.prefix_cons_inj a).mpr (lcp_prefix_right x z)
    · exact List.nil_prefix
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

/-- `common` is a prefix of every key. -/
theorem common_prefix : ∀ (J : List Entry), ∀ e ∈ J, common J <+: e.1
  | [], _, h => by simp at h
  | [e], f, h => by simp at h; subst h; simp [common]
  | e :: e' :: J, f, h => by
    simp only [common]
    rcases List.mem_cons.mp h with rfl | h
    · exact lcp_prefix_left _ _
    · exact (lcp_prefix_right _ _).trans (common_prefix (e' :: J) f h)

private theorem size_lt {J : List Entry} {i j : Nat} (hJ : J ≠ []) (hij : i < j)
    (h : ∀ e ∈ J, j ≤ e.1.length) : size J j < size J i := by
  induction J with
  | nil => exact absurd rfl hJ
  | cons e J ih =>
    simp only [size, List.map_cons, List.sum_cons] at ih ⊢
    have he := h e (by simp)
    by_cases hJ' : J = []
    · subst hJ'; simp; omega
    · have := ih hJ' (fun f hf => h f (by simp [hf])); omega

private theorem size_sub (J : List Entry) (i x : Nat) :
    size (sub J i x) (i + 1) + J.length ≤ size J i := by
  induction J with
  | nil => simp [size, sub]
  | cons e J ih =>
    simp only [sub, size] at ih ⊢
    rw [List.filter_cons]
    split
    · rename_i hx
      have : i < e.1.length := (List.getElem?_eq_some_iff.mp (of_decide_eq_true hx)).1
      simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
    · simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

mutual
/-- n(𝔍, i), the node cap function (Appendix D): `()` for the empty set; c(𝔍, i) itself when
its RLP is shorter than 32 bytes (the node is inline in its parent); else the Keccak-256 of
its RLP. -/
def cap : List Entry → Nat → Tree
  | [], _ => .leaf []
  | e :: J, i =>
    if (rlp (compose (e :: J) i)).length < 32 then compose (e :: J) i
    else .leaf (keccak (rlp (compose (e :: J) i)))
termination_by J i => (size J i, 1)
decreasing_by all_goals exact Prod.Lex.right _ (by decide)

/-- c(𝔍, i), the structural composition function (Appendix D), for the pairs `𝔍` whose keys
share their first `i` nibbles:

- a **leaf**, `(HP(I₀[i ..], 1), I₁)`, when 𝔍 is the one pair `I`;
- an **extension**, `(HP(I₀[i .. (j − 1)], 0), n(𝔍, j))`, when the keys share `j > i` nibbles
  (`common`, whose nibbles past the `i`-th are `I₀[i .. (j − 1)]` of every pair);
- a **branch** otherwise, `(u(0), ..., u(15), v)`: `u(x) = n({I ∈ 𝔍 : I₀[i] = x}, i + 1)`
  (`sub`), and `v` the value of the key of `i` nibbles, or `()` (`terminal`).

Appendix D's extension test is `i ≠ j`; as the keys share `i` nibbles, `j ≥ i` and it is
`i < j`, which makes `compose` terminate on every input. Appendix D leaves c(∅, i)
undefined, as the empty trie has no node: it is `()` here, so that `root []` is
`KEC(RLP(()))`, the empty trie's root `emptyRoot` (`root_nil`). -/
def compose : List Entry → Nat → Tree
  | [], _ => .leaf []
  | [e], i => .branch [.leaf (hp (e.1.drop i) true), .leaf e.2]
  | e :: e' :: J, i =>
    if i < (common (e :: e' :: J)).length then
      .branch [.leaf (hp ((common (e :: e' :: J)).drop i) false),
        cap (e :: e' :: J) (common (e :: e' :: J)).length]
    else
      .branch ((List.range 16).map (fun x => cap (sub (e :: e' :: J) i x) (i + 1)) ++
        [.leaf (terminal (e :: e' :: J) i)])
termination_by J i => (size J i, 0)
decreasing_by
  · rename_i h
    exact Prod.Lex.left _ _ (size_lt (by simp) h fun f hf => (common_prefix _ f hf).length_le)
  · exact Prod.Lex.left _ _ (by have := size_sub (e :: e' :: J) i x; simp at this; omega)
end

/-- TRIE(𝔍) (Appendix D): `KEC(RLP(c(𝔍, 0)))`, the root hash. -/
def root (I : Map) : Bytes := keccak (rlp (compose (y I) 0))

mutual
/-- The proof from n(𝔍, i) on, along the key `k`: c(𝔍, i)'s RLP when n(𝔍, i) is its hash (an
inline node is inside its parent), then the nodes below it on `k`'s path (`composeProof`). -/
def capProof (k : List Nat) : List Entry → Nat → Bytes
  | [], _ => []
  | e :: J, i =>
    (if (rlp (compose (e :: J) i)).length < 32 then [] else rlp (compose (e :: J) i)) ++
      composeProof k (e :: J) i
termination_by J i => (size J i, 1)
decreasing_by all_goals exact Prod.Lex.right _ (by decide)

/-- The proof below c(𝔍, i) along the key `k`: nothing below a leaf; below an extension, from
n(𝔍, j) on if `k` starts with the extension's nibbles, else nothing; below a branch, from
`u(x)` on for `k`'s nibble `x`, or nothing when `k` ends at the branch. -/
def composeProof (k : List Nat) : List Entry → Nat → Bytes
  | [], _ => []
  | [_], _ => []
  | e :: e' :: J, i =>
    if i < (common (e :: e' :: J)).length then
      if k.take (common (e :: e' :: J)).length = common (e :: e' :: J) then
        capProof k (e :: e' :: J) (common (e :: e' :: J)).length
      else []
    else
      match k[i]? with
      | some x => capProof k (sub (e :: e' :: J) i x) (i + 1)
      | none => []
termination_by J i => (size J i, 0)
decreasing_by
  · rename_i h _
    exact Prod.Lex.left _ _ (size_lt (by simp) h fun f hf => (common_prefix _ f hf).length_le)
  · exact Prod.Lex.left _ _ (by have := size_sub (e :: e' :: J) i x; simp at this; omega)
end

/-- The proof of `k` in the trie of `I`, as geth's `Trie.Prove` builds it for `eth_getProof`
(EIP-1186) and `lookup` reads it: the root node's RLP, then the RLP of every node on `k`'s path
that its parent names by hash, one after the other; an inline node is inside its parent (anvil
lists inline nodes as items as well, `proofOfFull`, which `lookup` also accepts). For the empty map
it is `0x80`, the RLP of `()`, as anvil proves a slot of an account without storage; geth sends
nothing, which `lookup_empty` accepts too. -/
def proofOf (I : Map) (k : Bytes) : Bytes :=
  rlp (compose (y I) 0) ++ composeProof (nibbles k) (y I) 0

mutual
/-- `capProof` when inline nodes are also emitted in the proof stream (as anvil's `eth_getProof`
does): every nonempty node on `k`'s path emits `rlp (compose (e :: J) i)`. -/
def capProofFull (k : List Nat) : List Entry → Nat → Bytes
  | [], _ => []
  | e :: J, i => rlp (compose (e :: J) i) ++ composeProofFull k (e :: J) i
termination_by J i => (size J i, 1)
decreasing_by all_goals exact Prod.Lex.right _ (by decide)

/-- `composeProof` when inline nodes are also emitted in the proof stream. -/
def composeProofFull (k : List Nat) : List Entry → Nat → Bytes
  | [], _ => []
  | [_], _ => []
  | e :: e' :: J, i =>
    if i < (common (e :: e' :: J)).length then
      if k.take (common (e :: e' :: J)).length = common (e :: e' :: J) then
        capProofFull k (e :: e' :: J) (common (e :: e' :: J)).length
      else []
    else
      match k[i]? with
      | some x => capProofFull k (sub (e :: e' :: J) i x) (i + 1)
      | none => []
termination_by J i => (size J i, 0)
decreasing_by
  · rename_i h _
    exact Prod.Lex.left _ _ (size_lt (by simp) h fun f hf => (common_prefix _ f hf).length_le)
  · exact Prod.Lex.left _ _ (by have := size_sub (e :: e' :: J) i x; simp at this; omega)
end

/-- The proof of `k` in the trie of `I` when inline nodes on `k`'s path are also listed as items in
the proof stream (as anvil's `eth_getProof` returns). -/
def proofOfFull (I : Map) (k : Bytes) : Bytes :=
  rlp (compose (y I) 0) ++ composeProofFull (nibbles k) (y I) 0

/-- What `I` holds at `k`: the value of the first pair with key `k`, or absence. -/
def get (I : Map) (k : Bytes) : Found :=
  match I.find? (fun p => p.1 = k) with
  | some p => .value p.2
  | none => .absent

/-- A map whose trie `lookup` reads: every key of at most `maxKey` (32) bytes, the longest key
`lookup` takes, and every value nonempty (`lookup` refuses an empty value in a leaf, and reads
one in a branch as absence) and shorter than 2^32 bytes (RLP encodes nothing of 2^64 bytes or
more; under this bound every node has an encoding). Keys need not be unique, nor of one
length. -/
structure WellFormed (I : Map) : Prop where
  keys : ∀ p ∈ I, p.1.length ≤ maxKey
  values : ∀ p ∈ I, p.2 ≠ [] ∧ p.2.length < 2 ^ 32

/-! ## Nibbles and hex-prefix paths -/

theorem nibbles_nil : nibbles [] = [] := rfl

theorem nibbles_cons (b : UInt8) (k : Bytes) :
    nibbles (b :: k) = b.toNat / 16 :: b.toNat % 16 :: nibbles k := by
  simp [nibbles, List.flatMap_cons]

theorem nibbles_append (a b : Bytes) : nibbles (a ++ b) = nibbles a ++ nibbles b := by
  simp [nibbles, List.flatMap_append]

theorem nibbles_length (k : Bytes) : (nibbles k).length = 2 * k.length := by
  induction k with
  | nil => rfl
  | cons b k ih => rw [nibbles_cons]; simp [ih]; omega

theorem nibbles_lt (k : Bytes) : ∀ a ∈ nibbles k, a < 16 := by
  induction k with
  | nil => simp [nibbles]
  | cons b k ih =>
    rw [nibbles_cons]
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · have := b.toNat_lt; omega
    · omega
    · exact ih a ha

/-- `Spec.Mpt.nibble`, which the walk reads keys and paths with, is y's k'. -/
theorem nibble_eq (k : Bytes) (j : Nat) : nibble k j = (nibbles k)[j]?.getD 0 := by
  induction k generalizing j with
  | nil => simp [nibble, nibbles]
  | cons b k ih =>
    rw [nibbles_cons]
    match j with
    | 0 => simp [nibble]
    | 1 => simp [nibble]
    | j + 2 =>
      have : nibble (b :: k) (j + 2) = nibble k j := by
        simp only [nibble, show (j + 2) / 2 = j / 2 + 1 by omega,
          show (j + 2) % 2 = j % 2 by omega, List.getElem?_cons_succ]
      rw [this, ih]
      simp

theorem nibbles_inj : ∀ {a b : Bytes}, nibbles a = nibbles b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [nibbles_cons, nibbles_nil] at h
  | _ :: _, [], h => by simp [nibbles_cons, nibbles_nil] at h
  | x :: a, z :: b, h => by
    rw [nibbles_cons, nibbles_cons] at h
    simp only [List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have : x = z := UInt8.toNat_inj.mp (by omega)
    rw [this, nibbles_inj h3]

private theorem toUInt8_toNat' {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

theorem nibbles_pack : ∀ (x : List Nat), x.length % 2 = 0 → (∀ a ∈ x, a < 16) →
    nibbles (pack x) = x
  | [], _, _ => rfl
  | [_], h, _ => by simp at h
  | a :: b :: x, h, hlt => by
    rw [pack, nibbles_cons]
    have ha := hlt a (by simp)
    have hb := hlt b (by simp)
    rw [toUInt8_toNat' (by omega), nibbles_pack x (by simp at h; omega)
      (fun c hc => hlt c (by simp [hc]))]
    congr 1
    · omega
    · congr 1; omega

/-- The nibbles of HP(x, t): the flag nibble (`f(t)`, plus 1 when `x` is odd), a zero nibble
when `x` is even, then `x`. -/
theorem nibbles_hp {x : List Nat} (t : Bool) (hlt : ∀ a ∈ x, a < 16) :
    nibbles (hp x t) = (if x.length % 2 = 0 then [hpFlag t, 0] else [hpFlag t + 1]) ++ x := by
  have hf : hpFlag t ≤ 2 := by cases t <;> simp [hpFlag]
  unfold hp
  split
  · rename_i he
    rw [nibbles_cons, toUInt8_toNat' (by omega), nibbles_pack x he hlt]
    simp
  · rename_i ho
    cases x with
    | nil => simp at ho
    | cons a x =>
      have ha := hlt a (by simp)
      simp only [List.headD_cons, List.tail_cons]
      rw [nibbles_cons, toUInt8_toNat' (by omega),
        nibbles_pack x (by simp at ho; omega) (fun c hc => hlt c (by simp [hc]))]
      simp; omega

theorem hp_length {x : List Nat} (t : Bool) (hlt : ∀ a ∈ x, a < 16) :
    (hp x t).length = x.length / 2 + 1 := by
  have := congrArg List.length (nibbles_hp t hlt)
  rw [nibbles_length] at this
  split at this <;> simp at this <;> omega

theorem hp_ne_nil (x : List Nat) (t : Bool) : hp x t ≠ [] := by
  unfold hp; split <;> simp

/-- The first byte of HP(x, t): its high nibble is the flag, and its low nibble zero when `x`
is even. -/
theorem hp_head {x : List Nat} (t : Bool) (hlt : ∀ a ∈ x, a < 16) :
    ((hp x t)[0]?.getD 0).toNat / 16 = hpFlag t + x.length % 2 ∧
      (x.length % 2 = 0 → ((hp x t)[0]?.getD 0).toNat % 16 = 0) := by
  have h := nibbles_hp t hlt
  cases hh : hp x t with
  | nil => exact absurd hh (hp_ne_nil x t)
  | cons b r =>
    rw [hh, nibbles_cons] at h
    simp only [List.getElem?_cons_zero, Option.getD_some]
    split at h
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact ⟨by omega, fun _ => h.2.1⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact ⟨by omega, fun h' => by omega⟩

/-! ## Reading encoded trees back -/

/-- `it`, an item read in `bs`, is the encoding of the tree `t`: its bytes are `t`'s RLP, and
its payload is `t`'s bytes (a byte array) or its subtrees' encodings (a sequence). -/
def Encodes (bs : Bytes) (t : Tree) (it : Span) : Prop :=
  it.pos ≤ it.start ∧ it.start ≤ it.stop ∧ it.stop ≤ bs.length ∧
    encodeTree t = some (window bs it.pos it.stop) ∧
    match t with
    | .leaf x => it.list = false ∧ window bs it.start it.stop = x
    | .branch ts => it.list = true ∧ encodeTrees ts = some (window bs it.start it.stop)

private theorem encodeTree_item {t : Tree} {e : Bytes} (h : encodeTree t = some e) :
    ∃ l q, encodeItem l q = some e ∧ match t with
      | .leaf x => l = false ∧ q = x
      | .branch ts => l = true ∧ encodeTrees ts = some q := by
  cases t with
  | leaf x => exact ⟨false, x, h, rfl, rfl⟩
  | branch ts =>
    simp only [encodeTree] at h
    cases hs : encodeTrees ts with
    | none => simp [hs] at h
    | some q => rw [hs, Option.bind_some] at h; exact ⟨true, q, h, rfl, hs⟩

private theorem window_take {bs : Bytes} {p stop : Nat} (n : Nat) (h : p + n ≤ stop) :
    window bs p (p + n) = (window bs p stop).take n := by
  simp only [window, List.take_drop, List.take_take, Nat.min_eq_left h]

/-- An encoding at a position of a buffer is read back as an item that encodes its tree. -/
theorem encodes_at {bs r e : Bytes} {t : Tree} {p stop : Nat} (he : encodeTree t = some e)
    (hs : stop ≤ bs.length) (hw : window bs p stop = e ++ r) :
    ∃ it, itemAt bs p stop = some it ∧ it.pos = p ∧ it.stop = p + e.length ∧
      Encodes bs t it := by
  obtain ⟨l, q, hlq, ht⟩ := encodeTree_item he
  have hi := itemAt_encodeItem hlq hs hw
  have hsuf := encodeItem_suffix hlq
  have hlen : p + e.length ≤ stop := by
    have h1 := congrArg List.length hw
    have h2 := List.length_pos_iff.mpr (encodeTree_ne_nil he)
    rw [window_length hs, List.length_append] at h1
    omega
  have hwe : window bs p (p + e.length) = e := by
    rw [window_take _ hlen, hw, List.take_left' rfl]
  have hwq : window bs (p + (e.length - q.length)) (p + e.length) = q := by
    rw [window_drop, hwe, hsuf.2]
  refine ⟨_, hi, rfl, rfl, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; rw [hwe]; exact he, ?_⟩
  cases t with
  | leaf x => obtain ⟨rfl, rfl⟩ := ht; exact ⟨rfl, hwq⟩
  | branch ts => obtain ⟨rfl, hq⟩ := ht; exact ⟨rfl, by simp only; rw [hwq]; exact hq⟩

private theorem itemsF_trees (bs : Bytes) {stop : Nat} (hs : stop ≤ bs.length) :
    ∀ (ts : List Tree) (p : Nat) {s : Bytes}, encodeTrees ts = some s → window bs p stop = s →
    ∃ its, itemsF (stop - p + 1) bs p stop = some its ∧ its.length = ts.length ∧
      ∀ k < ts.length, Encodes bs (ts[k]?.getD (.leaf [])) (its[k]?.getD default)
  | [], p, s, h, hw => by
    simp only [encodeTrees, Option.some.injEq] at h
    subst h
    have := congrArg List.length hw
    rw [window_length hs] at this
    simp only [List.length_nil] at this
    refine ⟨[], ?_, rfl, by simp⟩
    rw [show stop - p + 1 = 0 + 1 by omega]
    simp only [itemsF]
    rw [ite_eq_right (by omega)]
  | t :: ts, p, s, h, hw => by
    simp only [encodeTrees] at h
    cases he : encodeTree t with
    | none => simp [he] at h
    | some e =>
      cases hr : encodeTrees ts with
      | none => simp [he, hr] at h
      | some s' =>
        simp only [he, hr, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have hne : e ≠ [] := encodeTree_ne_nil he
        have hlen := List.length_pos_iff.mpr hne
        have hwl := congrArg List.length hw
        rw [window_length hs, List.length_append] at hwl
        obtain ⟨it, hi, hpos, hstop, henc⟩ := encodes_at he hs hw
        obtain ⟨its, h1, h2, h3⟩ := itemsF_trees bs hs ts (p + e.length) hr
          (by rw [window_drop, hw, List.drop_left' rfl])
        refine ⟨it :: its, ?_, by simp [h2], ?_⟩
        · rw [itemsF_succ (by omega) hi, hstop, h1]; rfl
        · intro k hk
          cases k with
          | zero => simpa using henc
          | succ k => simpa using h3 k (by simp at hk; omega)

/-- The items of an encoded sequence are its subtrees' encodings, one for each. -/
theorem itemsAt_trees {ts : List Tree} {s : Bytes} (h : encodeTrees ts = some s) :
    ∃ its, itemsAt s 0 s.length = some its ∧ its.length = ts.length ∧
      ∀ k < ts.length, Encodes s (ts[k]?.getD (.leaf [])) (its[k]?.getD default) := by
  obtain ⟨its, h1, h2, h3⟩ := itemsF_trees s (Nat.le_refl _) ts 0 h (window_all s)
  refine ⟨its, ?_, h2, h3⟩
  unfold itemsAt
  rw [ite_eq_left ⟨Nat.zero_le _, Nat.le_refl _⟩]
  exact h1

/-- A node named by its hash is read from the front of the stream: its payload, then what
follows it. -/
theorem node_hashed {ts : List Tree} {q e r : Bytes} (he : encodeTree (.branch ts) = some e)
    (hq : encodeTrees ts = some q) : Mpt.node (.hashed (keccak e)) (e ++ r) = some (q, r) := by
  obtain ⟨it, hi, hpos, hstop, h1, h2, h3, h4, hl, h5⟩ :=
    encodes_at (bs := e ++ r) (p := 0) he (Nat.le_refl _) (by rw [window_all])
  have hw : window (e ++ r) 0 it.stop = e := by
    rw [hstop, Nat.zero_add, window, List.take_left' rfl, List.drop_zero]
  have hq' : window (e ++ r) it.start it.stop = q := Option.some.inj (h5.symm.trans hq)
  simp only [Mpt.node, hi, hl, hw, true_and, ite_true, hq']
  rw [hstop, Nat.zero_add, List.drop_left' rfl]

/-- A node named inline whose encoding is also at the front of the stream is consumed from it,
leaving what follows. -/
theorem node_inline_present {ts : List Tree} {q e r : Bytes} (he : encodeTree (.branch ts) = some e)
    (hq : encodeTrees ts = some q) : Mpt.node (.inline q) (e ++ r) = some (q, r) := by
  obtain ⟨it, hi, hpos, hstop, h1, h2, h3, h4, hl, h5⟩ :=
    encodes_at (bs := e ++ r) (p := 0) he (Nat.le_refl _) (by rw [window_all])
  have hq' : window (e ++ r) it.start it.stop = q := Option.some.inj (h5.symm.trans hq)
  simp only [Mpt.node, Mpt.afterInline, hi, hl, hq', and_self, ite_true]
  rw [hstop, Nat.zero_add, List.drop_left' rfl]

/-! ## Every node has an encoding -/

/-- A pair of y(𝔍) as those of a `WellFormed` map are: a key of at most 64 nibbles, each below
16, and a nonempty value shorter than 2^32 bytes. -/
def EntryOk (e : Entry) : Prop :=
  e.1.length ≤ 2 * maxKey ∧ (∀ a ∈ e.1, a < 16) ∧ e.2 ≠ [] ∧ e.2.length < 2 ^ 32

/-- Keccak-256 gives 32 bytes (here without VCVio, from the vendored `Spec.Keccak.squeeze`). -/
private theorem keccak_length (bs : Bytes) : (keccak bs).length = 32 := by
  have push : ∀ (g : Nat → UInt8) (l : List Nat) (acc : ByteArray),
      (l.foldl (fun b a => b.push (g a)) acc).size = acc.size + l.length := by
    intro g l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih, ByteArray.size_push, List.length_cons]
      omega
  simp only [LeanLight.Spec.Header.keccak, Common.keccak, Spec.Keccak.keccak256, Spec.Keccak.squeeze]
  simp
  rw [push]
  rfl

private theorem encodeBytes_some {x : Bytes} (h : x.length < 2 ^ 64) :
    ∃ e, encodeBytes x = some e := by
  unfold encodeBytes
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · simp

private theorem encodeList_some {s : Bytes} (h : s.length < 2 ^ 64) :
    ∃ e, encodeList s = some e := by
  unfold encodeList
  split
  · exact ⟨_, rfl⟩
  · simp

/-- A hash is encoded with one byte before it. -/
theorem encodeBytes_hash (bs : Bytes) :
    encodeBytes (keccak bs) = some ((128 + 32).toUInt8 :: keccak bs) := by
  rw [encodeBytes_short (by rw [keccak_length]; omega) (by rw [keccak_length]; omega),
    keccak_length]

private theorem encodeTrees_bound (B : Nat) : ∀ (ts : List Tree),
    (∀ t ∈ ts, ∃ e, encodeTree t = some e ∧ e.length ≤ B) →
    ∃ s, encodeTrees ts = some s ∧ s.length ≤ B * ts.length
  | [], _ => ⟨[], rfl, by simp⟩
  | t :: ts, h => by
    obtain ⟨e, he, hl⟩ := h t (by simp)
    obtain ⟨s, hs, hsl⟩ := encodeTrees_bound B ts (fun u hu => h u (by simp [hu]))
    exact ⟨e ++ s, encodeTrees_cons he hs, by simp [Nat.mul_succ]; omega⟩

/-- What `encodes` proves of c(𝔍, i) and n(𝔍, i): for 𝔍 nonempty, c(𝔍, i) is a sequence whose
items have an encoding, and so has it, `rlp (compose J i)`; n(𝔍, i)'s encoding takes at most
33 bytes. -/
def NodeEnc (J : List Entry) (i : Nat) : Prop :=
  (J ≠ [] → ∃ ts q, compose J i = .branch ts ∧ encodeTrees ts = some q ∧
    encodeTree (compose J i) = some (rlp (compose J i))) ∧
  ∃ e, encodeTree (cap J i) = some e ∧ e.length ≤ 33

private theorem hp_short {x : List Nat} (t : Bool) (hx : x.length ≤ 2 * maxKey)
    (hlt : ∀ a ∈ x, a < 16) :
    ∃ e, encodeBytes (hp x t) = some e ∧ e.length ≤ 42 := by
  have hl := hp_length t hlt
  simp only [maxKey] at hx
  obtain ⟨e, he⟩ := encodeBytes_some (x := hp x t) (by omega)
  exact ⟨e, he, by have := encodeBytes_length_le he; omega⟩

/-- Every node of a map whose pairs are `EntryOk` has an encoding. -/
theorem encodes : ∀ (n : Nat) (J : List Entry) (i : Nat), size J i < n →
    (∀ e ∈ J, EntryOk e) → NodeEnc J i
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, J, i, hn, hJ => by
    have hc : J ≠ [] → ∃ ts q, compose J i = .branch ts ∧ encodeTrees ts = some q ∧
        encodeTree (compose J i) = some (rlp (compose J i)) := by
      intro hne
      suffices h : ∃ ts q, compose J i = .branch ts ∧ encodeTrees ts = some q ∧
          q.length < 2 ^ 64 by
        obtain ⟨ts, q, h1, h2, h3⟩ := h
        obtain ⟨e, he⟩ := encodeList_some h3
        refine ⟨ts, q, h1, h2, ?_⟩
        have : encodeTree (compose J i) = some e := by rw [h1]; simp [encodeTree, h2, he]
        rw [rlp, this]
        rfl
      match J, hne with
      | [e], _ =>
        obtain ⟨hk, hlt, -, hv⟩ := hJ e (by simp)
        obtain ⟨e1, he1, l1⟩ := hp_short true (x := e.1.drop i) (by simp; omega)
          (fun a ha => hlt a (List.mem_of_mem_drop ha))
        obtain ⟨e2, he2⟩ := encodeBytes_some (x := e.2) (by omega)
        have l2 := encodeBytes_length_le he2
        refine ⟨_, e1 ++ (e2 ++ []), by rw [compose],
          encodeTrees_cons (t := .leaf _) he1 (encodeTrees_cons (t := .leaf _) he2 rfl),
          by simp; omega⟩
      | e :: e' :: J', _ =>
        have hpre := common_prefix (e :: e' :: J')
        rw [compose]
        split
        · rename_i hij
          have hsz : size (e :: e' :: J') (common (e :: e' :: J')).length < n := by
            have := size_lt (J := e :: e' :: J') (by simp) hij
              (fun f hf => (hpre f hf).length_le)
            omega
          obtain ⟨-, c, hc, hcl⟩ := encodes n _ _ hsz hJ
          obtain ⟨hk, hlt, -, -⟩ := hJ e (by simp)
          have hcl' := (hpre e (by simp)).length_le
          obtain ⟨e1, he1, l1⟩ := hp_short false (x := (common (e :: e' :: J')).drop i)
            (by simp; omega)
            (fun a ha => hlt a ((hpre e (by simp)).subset (List.mem_of_mem_drop ha)))
          exact ⟨_, e1 ++ (c ++ []), rfl,
            encodeTrees_cons (t := .leaf _) he1 (encodeTrees_cons hc rfl),
            by simp; omega⟩
        · have hu : ∀ t ∈ (List.range 16).map (fun x => cap (sub (e :: e' :: J') i x) (i + 1)),
              ∃ c, encodeTree t = some c ∧ c.length ≤ 33 := by
            intro t ht
            simp only [List.mem_map, List.mem_range] at ht
            obtain ⟨x, -, rfl⟩ := ht
            have := size_sub (e :: e' :: J') i x
            simp only [List.length_cons, sub] at this
            exact (encodes n _ _ (by omega)
              (fun f hf => hJ f (List.mem_filter.mp hf).1)).2
          obtain ⟨s1, hs1, hl1⟩ := encodeTrees_bound 33 _ hu
          have ht : (terminal (e :: e' :: J') i).length < 2 ^ 32 := by
            unfold terminal
            split
            · rename_i f hf
              exact (hJ f (List.mem_of_find?_eq_some hf)).2.2.2
            · simp
          obtain ⟨e3, he3⟩ := encodeBytes_some (x := terminal (e :: e' :: J') i) (by omega)
          have l3 := encodeBytes_length_le he3
          refine ⟨_, s1 ++ (e3 ++ []), rfl,
            encodeTrees_append hs1 (encodeTrees_cons (t := .leaf _) he3 rfl), ?_⟩
          simp only [List.length_map, List.length_range] at hl1
          simp; omega
    refine ⟨hc, ?_⟩
    match J, hc with
    | [], _ => exact ⟨[0x80], by rw [cap]; rfl, by simp⟩
    | e :: J', hc =>
      obtain ⟨ts, q, h1, h2, h3⟩ := hc (by simp)
      rw [cap]
      split
      · rename_i hlt
        exact ⟨_, h3, by omega⟩
      · exact ⟨_, encodeBytes_hash _, by simp [keccak_length]⟩

/-! ## Reading one node -/

/-- An item that encodes HP(x, t): a byte array of `‖x‖ / 2 + 1` bytes, whose nibbles from its
payload on are the flag nibbles, then `x`, then the nibbles of what follows. -/
theorem hp_item {q : Bytes} {x : List Nat} {t : Bool} {s0 : Span}
    (h0 : Encodes q (.leaf (hp x t)) s0) (hlt : ∀ a ∈ x, a < 16) :
    s0.list = false ∧ s0.stop - s0.start = x.length / 2 + 1 ∧
      q[s0.start]?.getD 0 = (hp x t)[0]?.getD 0 ∧
      nibbles (q.drop s0.start) =
        ((if x.length % 2 = 0 then [hpFlag t, 0] else [hpFlag t + 1]) ++ x) ++
          nibbles (q.drop s0.stop) := by
  obtain ⟨-, h1, h2, -, hl, hw⟩ := h0
  have hlen : s0.stop - s0.start = x.length / 2 + 1 := by
    rw [← hp_length t hlt, ← hw, window_length h2]
  have hd : q.drop s0.start = hp x t ++ q.drop s0.stop := by
    rw [← hw, window]
    conv => lhs; rw [← List.take_append_drop s0.stop q]
    rw [List.drop_append_of_le_length (by simp; omega)]
  refine ⟨hl, hlen, ?_, ?_⟩
  · have : q[s0.start]? = (q.drop s0.start)[0]? := by simp
    rw [this, hd, List.getElem?_append_left (by rw [hp_length t hlt]; omega)]
  · rw [hd, nibbles_append, nibbles_hp t hlt]

/-- `pathMatches`, on a path that encodes HP(x, t) and no longer than what is left of the key,
is whether `x` comes next in the key's nibbles. -/
theorem hp_matches {q : Bytes} {x : List Nat} {t : Bool} {s0 : Span} {key : Bytes} {nib : Nat}
    (h0 : Encodes q (.leaf (hp x t)) s0) (hlt : ∀ a ∈ x, a < 16)
    (hx : x.length ≤ 2 * key.length - nib) :
    pathMatches q s0.start (decide (x.length % 2 = 1)) key nib x.length = true ↔
      x <+: (nibbles key).drop nib := by
  obtain ⟨-, -, -, hn⟩ := hp_item h0 hlt
  have hkl := nibbles_length key
  have mid : ∀ (P r : List Nat) k, k < x.length → (P ++ x ++ r)[k + P.length]? = x[k]? := by
    intro P r k hk
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
    simp
  have hoff : (if x.length % 2 = 1 then 1 else 2) =
      (if x.length % 2 = 0 then [hpFlag t, 0] else [hpFlag t + 1]).length := by
    split <;> split <;> simp <;> omega
  unfold pathMatches
  rw [List.all_eq_true, List.prefix_iff_getElem?]
  simp only [List.mem_range, decide_eq_true_eq]
  rw [hoff]
  constructor
  · intro h k hk
    have := h k hk
    rw [nibble_eq, nibble_eq, hn, mid _ _ k hk, List.getElem?_eq_getElem hk, Option.getD_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega), this]
  · intro h k hk
    have := h k hk
    rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega), Option.some.injEq] at this
    rw [nibble_eq, nibble_eq, hn, mid _ _ k hk, List.getElem?_eq_getElem hk, Option.getD_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some, this]

/-- What a leaf (`t`) or an extension says, when its path encodes HP(x, t) with `x` of at most
64 nibbles: `short` with the path's flag, length and nibbles read back. -/
theorem short_hp {q : Bytes} {x : List Nat} {t : Bool} {s0 c : Span} {key : Bytes} {nib : Nat}
    (h0 : Encodes q (.leaf (hp x t)) s0) (hx : x.length ≤ 2 * maxKey) (hlt : ∀ a ∈ x, a < 16) :
    short q s0 c key nib =
      if t = true then
        if !(!c.list && decide (c.start < c.stop)) then none
        else if x.length = 2 * key.length - nib ∧ x <+: (nibbles key).drop nib then
          some (.found (.value (window q c.start c.stop)))
        else some (.found .absent)
      else if x.length = 0 then none
      else if x.length ≤ 2 * key.length - nib ∧ x <+: (nibbles key).drop nib then
        child q c (nib + x.length) false
      else some (.found .absent) := by
  obtain ⟨hl, hn, hb, -⟩ := hp_item h0 hlt
  obtain ⟨hf, hz⟩ := hp_head t hlt
  rw [← hb] at hf hz
  have h2 := h0.2.2.1
  simp only [maxKey] at hx
  have hok : pathOk q s0 = true := by
    simp only [pathOk, hl, hf, Bool.not_false, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, Bool.or_eq_true]
    refine ⟨⟨⟨⟨by omega, h2⟩, by omega⟩, by cases t <;> simp [hpFlag] <;> omega⟩, ?_⟩
    by_cases he : x.length % 2 = 0
    · right; exact hz he
    · left; cases t <;> simp [hpFlag] <;> omega
  have hodd : decide ((q[s0.start]?.getD 0).toNat / 16 % 2 = 1) = decide (x.length % 2 = 1) := by
    rw [hf]; cases t <;> simp [hpFlag]
  have hlen : (if decide (x.length % 2 = 1) = true then 2 * (s0.stop - s0.start) - 1
      else 2 * (s0.stop - s0.start) - 2) = x.length := by
    rw [hn]; split <;> simp_all <;> omega
  have c1 : (x.length = 2 * key.length - nib ∧
      pathMatches q s0.start (decide (x.length % 2 = 1)) key nib x.length = true) ↔
      (x.length = 2 * key.length - nib ∧ x <+: (nibbles key).drop nib) :=
    and_congr_right fun h => hp_matches h0 hlt (by omega)
  have c2 : (x.length ≤ 2 * key.length - nib ∧
      pathMatches q s0.start (decide (x.length % 2 = 1)) key nib x.length = true) ↔
      (x.length ≤ 2 * key.length - nib ∧ x <+: (nibbles key).drop nib) :=
    and_congr_right fun h => hp_matches h0 hlt h
  unfold short
  rw [ite_eq_left hok]
  simp only []
  rw [hodd, hlen, hf]
  cases t
  · simp only [hpFlag, Bool.false_eq_true, ite_false, c2]
    rw [ite_eq_right (by omega)]
  · simp only [hpFlag, ite_true, c1]
    rw [ite_eq_left (by omega)]

/-- `nx` names the node c(𝔍, i), and `pre` is what the proof holds of it before the nodes
below it: c(𝔍, i)'s RLP when `nx` is its hash, nothing when `nx` is the node inline (whose RLP is
shorter than 32 bytes). -/
def Points (J : List Entry) (i : Nat) (nx : Next) (pre : Bytes) : Prop :=
  (nx = .hashed (keccak (rlp (compose J i))) ∧ pre = rlp (compose J i)) ∨
    (∃ ts q, compose J i = .branch ts ∧ encodeTrees ts = some q ∧
      (rlp (compose J i)).length < 32 ∧ nx = .inline q ∧ pre = [])

/-- `nx` names the node c(𝔍, i) when every node on the path (hashed or inline) emits
`rlp (compose J i)` in the proof stream (`capProofFull`). -/
def PointsFull (J : List Entry) (i : Nat) (nx : Next) : Prop :=
  nx = .hashed (keccak (rlp (compose J i))) ∨
    (∃ ts q, compose J i = .branch ts ∧ encodeTrees ts = some q ∧ nx = .inline q)

/-- The item that encodes n(∅, i) = `()` proves absence from a branch. -/
theorem child_empty {q : Bytes} {c : Span} {i nib : Nat} (hc : Encodes q (cap [] i) c) :
    child q c nib true = some (.found .absent) := by
  rw [cap] at hc
  obtain ⟨-, h1, h2, -, hl, hw⟩ := hc
  have := congrArg List.length hw
  rw [window_length h2, List.length_nil] at this
  unfold child
  rw [hl]
  simp only [Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by omega), ite_eq_left ⟨trivial, by omega⟩]

/-- The item that encodes n(𝔍, i), 𝔍 nonempty, names c(𝔍, i): inline when its RLP is shorter
than 32 bytes, else by its hash, which the proof then holds next. -/
theorem child_cap {q : Bytes} {c : Span} {e : Entry} {J : List Entry} {i nib : Nat} {b : Bool}
    (k : List Nat) (hc : Encodes q (cap (e :: J) i) c) (hn : NodeEnc (e :: J) i) :
    ∃ nx pre, child q c nib b = some (.next nx nib) ∧ Points (e :: J) i nx pre ∧
      capProof k (e :: J) i = pre ++ composeProof k (e :: J) i := by
  obtain ⟨ts, q', h1, h2, h3⟩ := hn.1 (by simp)
  rw [cap] at hc
  rw [capProof]
  by_cases hlt : (rlp (compose (e :: J) i)).length < 32
  · rw [ite_eq_left hlt] at hc
    rw [ite_eq_left hlt]
    have hc' := hc
    rw [h1] at hc'
    obtain ⟨hps, hss, hsl, henc, hl, hts⟩ := hc'
    have h3' : encodeTree (compose (e :: J) i) = some (window q c.pos c.stop) := by
      rw [h1]; exact henc
    have hw := Option.some.inj (h3'.symm.trans h3)
    have : c.stop - c.pos < 32 := by
      have := congrArg List.length hw
      rw [window_length hsl] at this
      omega
    refine ⟨_, [], ?_, Or.inr ⟨ts, _, h1, hts, hlt, rfl, rfl⟩, rfl⟩
    unfold child
    rw [hl, ite_eq_left rfl, ite_eq_left ⟨by omega, this⟩]
  · rw [ite_eq_right hlt] at hc
    rw [ite_eq_right hlt]
    obtain ⟨-, hss, hsl, -, hl, hw⟩ := hc
    have : c.stop - c.start = 32 := by
      have := congrArg List.length hw
      rw [window_length hsl, keccak_length] at this
      exact this
    refine ⟨_, _, ?_, Or.inl ⟨rfl, rfl⟩, rfl⟩
    unfold child
    rw [hl]
    simp only [Bool.false_eq_true, ite_false]
    rw [ite_eq_left ⟨hss, this⟩, hw]

/-- What the pairs `J` hold at the key `K`: the value of the first pair with key `K`, or
absence. -/
def holds (J : List Entry) (K : List Nat) : Found :=
  match J.find? (fun e => e.1 = K) with
  | some e => .value e.2
  | none => .absent

/-- The pairs under the node at nibble `i` on the path of the key `K`: their keys start with
`K`'s first `i` nibbles, and they are `EntryOk`. -/
structure Under (K : List Nat) (J : List Entry) (i : Nat) : Prop where
  agree : ∀ e ∈ J, e.1.take i = K.take i
  ok : ∀ e ∈ J, EntryOk e

private theorem drop_eq_iff {a K : List Nat} {i : Nat} (h : a.take i = K.take i) :
    a.drop i = K.drop i ↔ a = K := by
  constructor
  · intro hd
    rw [← List.take_append_drop i a, h, hd, List.take_append_drop]
  · rintro rfl; rfl

/-- A leaf holds its value at its own key, and proves every other key absent. -/
theorem step_leaf {key : Bytes} {e : Entry} {i : Nat} {q : Bytes}
    (hu : Under (nibbles key) [e] i) (hi : i ≤ 2 * key.length)
    (hq : encodeTrees [.leaf (hp (e.1.drop i) true), .leaf e.2] = some q) :
    step key i q = some (.found (holds [e] (nibbles key))) := by
  obtain ⟨its, hits, hlen, henc⟩ := itemsAt_trees hq
  have h0 := henc 0 (by simp)
  have h1 := henc 1 (by simp)
  simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ] at h0 h1
  obtain ⟨hk, hlt, hv0, hv⟩ := hu.ok e (by simp)
  have hpre := hu.agree e (by simp)
  have hkl := nibbles_length key
  unfold step
  rw [hits]
  dsimp only
  rw [ite_eq_right (by simp [hlen]), ite_eq_left (by simp [hlen])]
  rw [short_hp h0 (by simp; omega) (fun a ha => hlt a (List.mem_of_mem_drop ha))]
  obtain ⟨-, hss, hsl, -, hl1, hw1⟩ := h1
  have hst : (its[1]?.getD default).start < (its[1]?.getD default).stop := by
    have := congrArg List.length hw1
    rw [window_length hsl] at this
    have := List.length_pos_iff.mpr hv0
    omega
  simp only [ite_true, hl1, hst, Bool.not_false, decide_true, Bool.and_true, Bool.not_true,
    Bool.false_eq_true, ite_false, hw1]
  have hel : i ≤ e.1.length := by
    have := congrArg List.length hpre
    simp at this; omega
  unfold holds
  simp only [List.find?_cons, List.find?_nil]
  by_cases he : e.1 = nibbles key
  · rw [ite_eq_left ⟨by rw [he, List.length_drop, hkl], by rw [he]; exact List.prefix_refl _⟩]
    simp [he]
  · rw [ite_eq_right]
    · simp [he]
    · rintro ⟨h1, h2⟩
      apply he
      apply (drop_eq_iff hpre).mp
      exact h2.eq_of_length (by simp [hkl] at h1 ⊢; omega)

private theorem find?_congr {α : Type} {p r : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = r a) → l.find? p = l.find? r
  | [], _ => rfl
  | a :: l, h => by
    have ih : l.find? p = l.find? r := find?_congr (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.find?_cons, h a List.mem_cons_self, ih]

private theorem find?_filter_of {α : Type} {p r : α → Bool} (l : List α)
    (h : ∀ a, r a = true → p a = true) :
    (l.filter p).find? r = l.find? r := by
  rw [List.find?_filter]
  apply find?_congr
  intro a _
  by_cases hr : r a = true
  · simp [hr, h a hr]
  · simp [hr]

/-- Under a branch, the pairs whose key goes on with the key's next nibble hold what all of them
hold at it. -/
theorem holds_sub {J : List Entry} {K : List Nat} {i x : Nat} (hx : K[i]? = some x) :
    holds (sub J i x) K = holds J K := by
  unfold holds sub
  rw [find?_filter_of]
  intro a ha
  simp only [decide_eq_true_eq] at ha ⊢
  rw [ha, hx]

theorem under_sub {J : List Entry} {K : List Nat} {i x : Nat} (hu : Under K J i)
    (hx : K[i]? = some x) : Under K (sub J i x) (i + 1) := by
  refine ⟨fun e he => ?_, fun e he => hu.ok e (List.mem_filter.mp he).1⟩
  obtain ⟨he, hex⟩ := List.mem_filter.mp he
  simp only [decide_eq_true_eq] at hex
  rw [List.take_add_one, List.take_add_one, hu.agree e he, hex, hx]

/-- At a branch where the key ends, the key is held exactly when the branch has a value. -/
theorem holds_terminal {J : List Entry} {K : List Nat} (hu : Under K J K.length) :
    holds J K = if terminal J K.length = [] then .absent else .value (terminal J K.length) := by
  have hc : J.find? (fun e => e.1.length = K.length) = J.find? (fun e => e.1 = K) := by
    apply find?_congr
    intro e he
    have h := hu.agree e he
    rw [List.take_length] at h
    simp only [decide_eq_decide]
    constructor
    · intro hl; rw [← h, List.take_of_length_le (by omega)]
    · rintro rfl; rfl
  unfold holds terminal
  rw [hc]
  split
  · rename_i e he
    rw [ite_eq_right (hu.ok e (List.mem_of_find?_eq_some he)).2.2.1]
  · simp

/-- Below an extension the key does not go on with, it is absent. -/
theorem holds_off {J : List Entry} {K C : List Nat} (hC : ∀ f ∈ J, C <+: f.1)
    (hf : K.take C.length ≠ C) : holds J K = .absent := by
  unfold holds
  split
  · rename_i e he
    have := List.find?_some he
    simp only [decide_eq_true_eq] at this
    obtain ⟨t, ht⟩ := hC e (List.mem_of_find?_eq_some he)
    rw [this] at ht
    exact absurd (by rw [← ht, List.take_left' rfl]) hf
  · rfl

theorem under_ext {J : List Entry} {K C : List Nat} {i : Nat} (hu : Under K J i)
    (hC : ∀ f ∈ J, C <+: f.1) (hf : K.take C.length = C) : Under K J C.length := by
  refine ⟨fun e he => ?_, hu.ok⟩
  obtain ⟨t, ht⟩ := hC e he
  rw [hf, ← ht, List.take_left' rfl]

/-- The key goes on with an extension's nibbles past the `i` it shares with them exactly when
it starts with all of them. -/
theorem follows_iff {C K : List Nat} {i : Nat} (h : C.take i = K.take i) :
    C.drop i <+: K.drop i ↔ K.take C.length = C := by
  constructor
  · rintro ⟨u, hu⟩
    have : K = C ++ u := by
      rw [← List.take_append_drop i K, ← hu, ← h, ← List.append_assoc, List.take_append_drop]
    rw [this, List.take_left' rfl]
  · intro hf
    rw [← hf, List.drop_take]
    exact List.take_prefix _ _

theorem nibble_lt (key : Bytes) (j : Nat) : nibble key j < 16 := by
  rw [nibble_eq]
  cases h : (nibbles key)[j]? with
  | none => simp
  | some a => exact nibbles_lt key a (List.mem_of_getElem? h)

theorem nibbles_getElem? {key : Bytes} {j : Nat} (h : j < 2 * key.length) :
    (nibbles key)[j]? = some (nibble key j) := by
  rw [nibble_eq, List.getElem?_eq_getElem (by rw [nibbles_length]; exact h)]
  rfl

/-- An extension names the node after it when the key goes on with its nibbles, and proves the
key absent otherwise. -/
theorem step_ext {key : Bytes} {e : Entry} {J : List Entry} {C : List Nat} {i : Nat} {q : Bytes}
    (hu : Under (nibbles key) (e :: J) i) (hij : i < C.length) (hC : ∀ f ∈ e :: J, C <+: f.1)
    (hn : NodeEnc (e :: J) C.length)
    (hq : encodeTrees [.leaf (hp (C.drop i) false), cap (e :: J) C.length] = some q) :
    ((nibbles key).take C.length = C ∧ ∃ nx pre, step key i q = some (.next nx C.length) ∧
        Points (e :: J) C.length nx pre ∧
        capProof (nibbles key) (e :: J) C.length =
          pre ++ composeProof (nibbles key) (e :: J) C.length) ∨
      ((nibbles key).take C.length ≠ C ∧ step key i q = some (.found .absent)) := by
  obtain ⟨its, hits, hlen, henc⟩ := itemsAt_trees hq
  have h0 := henc 0 (by simp)
  have h1 := henc 1 (by simp)
  simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ] at h0 h1
  obtain ⟨hk, hlt, -, -⟩ := hu.ok e (by simp)
  obtain ⟨t, ht⟩ := hC e (by simp)
  have hkl := nibbles_length key
  have hCl : C.length ≤ e.1.length := by rw [← ht]; simp
  have hCt : C.take i = (nibbles key).take i := by
    rw [← hu.agree e (by simp), ← ht, List.take_append_of_le_length (by omega)]
  have hCx : ∀ a ∈ C.drop i, a < 16 := fun a ha =>
    hlt a (by rw [← ht]; exact List.mem_append_left _ (List.mem_of_mem_drop ha))
  unfold step
  rw [hits]
  dsimp only
  rw [ite_eq_right (by simp [hlen]), ite_eq_left (by simp [hlen])]
  rw [short_hp h0 (by simp; omega) hCx]
  simp only [Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by simp; omega), List.length_drop, show i + (C.length - i) = C.length by omega]
  by_cases hf : (nibbles key).take C.length = C
  · left
    refine ⟨hf, ?_⟩
    obtain ⟨nx, pre, hch, hpts, hcp⟩ :=
      child_cap (nib := C.length) (b := false) (nibbles key) h1 hn
    refine ⟨nx, pre, ?_, hpts, hcp⟩
    have hle : C.length ≤ 2 * key.length := by
      have := congrArg List.length hf; simp at this; omega
    rw [ite_eq_left ⟨by omega, (follows_iff hCt).mpr hf⟩, hch]
  · right
    refine ⟨hf, ?_⟩
    rw [ite_eq_right]
    rintro ⟨-, h2⟩
    exact hf ((follows_iff hCt).mp h2)

/-- A branch holds the value of the key that ends at it; for a longer key it proves it absent
when the child at the key's next nibble is `()`, and names that child otherwise. -/
theorem step_branch {key : Bytes} {J : List Entry} {i : Nat} {q : Bytes}
    (hu : Under (nibbles key) J i) (hi : i ≤ 2 * key.length)
    (hn : ∀ x, NodeEnc (sub J i x) (i + 1))
    (hq : encodeTrees ((List.range 16).map (fun x => cap (sub J i x) (i + 1)) ++
      [.leaf (terminal J i)]) = some q) :
    (i = 2 * key.length ∧ step key i q = some (.found (holds J (nibbles key)))) ∨
    (i < 2 * key.length ∧ sub J i (nibble key i) = [] ∧ step key i q = some (.found .absent)) ∨
    (i < 2 * key.length ∧ ∃ f J', sub J i (nibble key i) = f :: J' ∧ ∃ nx pre,
      step key i q = some (.next nx (i + 1)) ∧ Points (f :: J') (i + 1) nx pre ∧
      capProof (nibbles key) (f :: J') (i + 1) =
        pre ++ composeProof (nibbles key) (f :: J') (i + 1)) := by
  obtain ⟨its, hits, hlen, henc⟩ := itemsAt_trees hq
  have hkl := nibbles_length key
  unfold step
  rw [hits]
  dsimp only
  rw [ite_eq_left (by simp [hlen])]
  by_cases hik : i = 2 * key.length
  · left
    refine ⟨hik, ?_⟩
    rw [ite_eq_left hik]
    have h16 := henc 16 (by simp)
    rw [List.getElem?_append_right (by simp)] at h16
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some] at h16
    obtain ⟨-, hss, hsl, -, hl, hw⟩ := h16
    have hl0 := congrArg List.length hw
    rw [window_length hsl] at hl0
    rw [hl]
    simp only [Bool.false_eq_true, ite_false]
    rw [holds_terminal (by rw [hkl, ← hik]; exact hu)]
    rw [← hkl, ← hik] at *
    by_cases ht : terminal J i = []
    · rw [ite_eq_left (by rw [ht] at hl0; simp at hl0; omega), ite_eq_left ht]
    · rw [ite_eq_right (fun h => ht (List.length_eq_zero_iff.mp (by omega))), ite_eq_right ht,
        hw]
  · right
    have hlt : i < 2 * key.length := by omega
    rw [ite_eq_right hik]
    have hx := nibble_lt key i
    have hc := henc (nibble key i) (by simp; omega)
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_range hx] at hc
    simp only [Option.map_some, Option.getD_some] at hc
    cases hs : sub J i (nibble key i) with
    | nil =>
      rw [hs] at hc
      exact Or.inl ⟨hlt, rfl, child_empty hc⟩
    | cons f J' =>
      rw [hs] at hc
      have hnx := hn (nibble key i)
      rw [hs] at hnx
      obtain ⟨nx, pre, hch, hpts, hcp⟩ := child_cap (nib := i + 1) (b := true) (nibbles key) hc hnx
      exact Or.inr ⟨hlt, f, J', rfl, nx, pre, hch, hpts, hcp⟩

/-! ## Completeness -/

theorem nodeEnc (J : List Entry) (i : Nat) (h : ∀ e ∈ J, EntryOk e) : NodeEnc J i :=
  encodes (size J i + 1) J i (Nat.lt_succ_self _) h

/-- Every stream emitted by `composeProof` is either empty or begins with a hashed node whose RLP
is at least 32 bytes. -/
theorem composeProof_head_ge32 (k : List Nat) : ∀ (n : Nat) (J : List Entry) (i : Nat),
    size J i < n → (∀ e ∈ J, EntryOk e) →
    composeProof k J i = [] ∨
      ∃ t u, encodeTree t = some u ∧ 32 ≤ u.length ∧ u <+: composeProof k J i
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, [], i, _, _ => by rw [composeProof]; exact Or.inl rfl
  | n + 1, [e], i, _, _ => by rw [composeProof]; exact Or.inl rfl
  | n + 1, e :: e' :: J, i, hn, hJ => by
    have hpre := common_prefix (e :: e' :: J)
    rw [composeProof]
    have stepCap : ∀ (J' : List Entry) (j : Nat), size J' j < n → (∀ f ∈ J', EntryOk f) →
        capProof k J' j = [] ∨
          ∃ t u, encodeTree t = some u ∧ 32 ≤ u.length ∧ u <+: capProof k J' j := by
      intro J' j hsz hJ'
      cases J' with
      | nil => rw [capProof]; exact Or.inl rfl
      | cons f J'' =>
        rw [capProof]
        split
        · rw [List.nil_append]
          exact composeProof_head_ge32 k n (f :: J'') j hsz hJ'
        · rename_i hge
          obtain ⟨ts, q, h1, h2, h3⟩ := (nodeEnc (f :: J'') j hJ').1 (by simp)
          exact Or.inr ⟨compose (f :: J'') j, rlp (compose (f :: J'') j), h3, by omega, ⟨_, rfl⟩⟩
    split
    · rename_i hij
      split
      · have hsz : size (e :: e' :: J) (common (e :: e' :: J)).length < n := by
          have := size_lt (J := e :: e' :: J) (by simp) hij
            (fun f hf => (hpre f hf).length_le)
          omega
        exact stepCap _ _ hsz hJ
      · exact Or.inl rfl
    · cases k[i]? with
      | none => exact Or.inl rfl
      | some x =>
        have hsz : size (sub (e :: e' :: J) i x) (i + 1) < n := by
          have := size_sub (e :: e' :: J) i x
          simp only [List.length_cons] at this
          omega
        exact stepCap _ _ hsz (fun f hf => hJ f (List.mem_filter.mp hf).1)

/-- An inline node `< 32` bytes cannot match the front of `composeProof` (with nothing trailing),
since `composeProof` is either empty or begins with a hashed node of at least 32 bytes. -/
theorem node_inline_composeProof {ts : List Tree} {q e : Bytes} (k : List Nat) (J : List Entry)
    (i : Nat) (hJ : ∀ f ∈ J, EntryOk f) (he : encodeTree (.branch ts) = some e)
    (hq : encodeTrees ts = some q) (hlt : e.length < 32) :
    Mpt.node (.inline q) (composeProof k J i) = some (q, composeProof k J i) := by
  simp only [Mpt.node, Mpt.afterInline]
  cases hi : itemAt (composeProof k J i) 0 (composeProof k J i).length with
  | none => rfl
  | some it =>
    dsimp only
    rw [ite_eq_right]
    rintro ⟨hl, hwin⟩
    obtain ⟨hpos, -, -, -, hstop, -, -, henc⟩ := itemAt_span hi
    rw [hl, hwin] at henc
    simp only [encodeItem, ↓reduceIte] at henc
    have he' : encodeList q = some e := by
      simp only [encodeTree, hq, Option.bind_some] at he
      exact he
    have hwe : window (composeProof k J i) 0 it.stop = e := Option.some.inj (henc.symm.trans he')
    rcases composeProof_head_ge32 k (size J i + 1) J i (Nat.lt_succ_self _) hJ with hnil |
        ⟨t, u, hu, hge, r, hcp⟩
    · simp [hnil, itemAt] at hi
    · have htake : (composeProof k J i).take it.stop = e := by
        simpa [window] using hwe
      have heq_len : e.length = u.length := by
        have h1 := encodeTree_itemLength (t := .branch ts) he ((composeProof k J i).drop it.stop)
        have h2 := encodeTree_itemLength hu r
        have happ : e ++ (composeProof k J i).drop it.stop = composeProof k J i := by
          rw [← htake, List.take_append_drop]
        rw [happ] at h1
        rw [← hcp] at h1
        rw [← h1, h2]
      omega

/-- The walk from a node on the key's path, given the proof from that node on, ends with what
the pairs under it hold at the key, and consumes the whole stream. -/
theorem walk_compose (key : Bytes) : ∀ (n : Nat) (J : List Entry) (i : Nat) (nx : Next)
    (pre : Bytes), Under (nibbles key) J i → J ≠ [] → i ≤ 2 * key.length →
    2 * key.length - i < n → Points J i nx pre →
    walk n key i nx (pre ++ composeProof (nibbles key) J i) =
      some (holds J (nibbles key), [])
  | 0, _, _, _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, J, i, nx, pre, hu, hJ, hi, hn, hp => by
    have hkl := nibbles_length key
    obtain ⟨ts, q, h1, h2, h3⟩ := (nodeEnc J i hu.ok).1 hJ
    have hnode : Mpt.node nx (pre ++ composeProof (nibbles key) J i) =
        some (q, composeProof (nibbles key) J i) := by
      rcases hp with ⟨rfl, rfl⟩ | ⟨ts', q', h1', h2', hlt, rfl, rfl⟩
      · rw [h1] at h3 ⊢
        exact node_hashed h3 h2
      · rw [h1] at h1'
        cases h1'
        rw [h2] at h2'
        cases h2'
        rw [List.nil_append]
        have h3' : encodeTree (.branch ts) = some (rlp (compose J i)) := by rw [← h1]; exact h3
        exact node_inline_composeProof (nibbles key) J i hu.ok h3' h2 hlt
    simp only [walk, hnode]
    match J, hJ, hu, h1, h2 with
    | [e], _, hu, h1, h2 =>
      rw [compose] at h1
      cases h1
      rw [step_leaf hu hi h2]
      simp [composeProof]
    | e :: e' :: J', _, hu, h1, h2 =>
      have hC := common_prefix (e :: e' :: J')
      rw [compose] at h1
      split at h1
      · rename_i hij
        cases h1
        rcases step_ext hu hij hC (nodeEnc _ _ hu.ok) h2 with
          ⟨hf, nx', pre', hs, hp', hcp⟩ | ⟨hf, hs⟩
        · rw [hs]
          dsimp only
          rw [composeProof, ite_eq_left hij, ite_eq_left hf, hcp]
          have hle : (common (e :: e' :: J')).length ≤ 2 * key.length := by
            have := congrArg List.length hf; simp at this; omega
          exact walk_compose key n _ _ nx' pre' (under_ext hu hC hf) (by simp) hle
            (by omega) hp'
        · rw [hs]
          dsimp only
          rw [composeProof, ite_eq_left hij, ite_eq_right hf, holds_off hC hf]
      · rename_i hij
        cases h1
        have hn' : ∀ x, NodeEnc (sub (e :: e' :: J') i x) (i + 1) := fun x =>
          nodeEnc _ _ (fun f hf => hu.ok f (List.mem_filter.mp hf).1)
        rcases step_branch hu hi hn' h2 with ⟨hik, hs⟩ | ⟨hlt, hsub, hs⟩ |
            ⟨hlt, f, J'', hsub, nx', pre', hs, hp', hcp⟩
        · rw [hs]
          dsimp only
          rw [composeProof, ite_eq_right hij,
            List.getElem?_eq_none (by rw [hkl]; omega)]
        · rw [hs]
          dsimp only
          have hx := nibbles_getElem? hlt
          rw [composeProof, ite_eq_right hij, hx]
          dsimp only
          rw [← holds_sub hx, hsub]
          simp [capProof, holds]
        · rw [hs]
          dsimp only
          have hx := nibbles_getElem? hlt
          rw [composeProof, ite_eq_right hij, hx]
          dsimp only
          rw [← holds_sub hx, hsub, hcp]
          rw [← hsub]
          exact walk_compose key n _ _ nx' pre' (under_sub hu hx) (by rw [hsub]; simp)
            (by omega) (by omega) (by rw [hsub]; exact hp')

/-- The walk from a node on the key's path when inline nodes are also emitted in the stream
(`composeProofFull`), ending with what the pairs under it hold at the key and leaving `rest`. -/
theorem walk_compose_full (key : Bytes) : ∀ (n : Nat) (J : List Entry) (i : Nat) (nx : Next)
    (rest : Bytes), Under (nibbles key) J i → J ≠ [] → i ≤ 2 * key.length →
    2 * key.length - i < n → PointsFull J i nx →
    walk n key i nx (rlp (compose J i) ++ composeProofFull (nibbles key) J i ++ rest) =
      some (holds J (nibbles key), rest)
  | 0, _, _, _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, J, i, nx, rest, hu, hJ, hi, hn, hp => by
    have hkl := nibbles_length key
    obtain ⟨ts, q, h1, h2, h3⟩ := (nodeEnc J i hu.ok).1 hJ
    have hnode : Mpt.node nx (rlp (compose J i) ++ composeProofFull (nibbles key) J i ++ rest) =
        some (q, composeProofFull (nibbles key) J i ++ rest) := by
      rw [List.append_assoc]
      have h3' : encodeTree (.branch ts) = some (rlp (compose J i)) := by rw [← h1]; exact h3
      rcases hp with rfl | ⟨ts', q', h1', h2', rfl⟩
      · exact node_hashed h3' h2
      · rw [h1] at h1'
        cases h1'
        rw [h2] at h2'
        cases h2'
        exact node_inline_present h3' h2
    simp only [walk, hnode]
    match J, hJ, hu, h1, h2 with
    | [e], _, hu, h1, h2 =>
      rw [compose] at h1
      cases h1
      rw [step_leaf hu hi h2]
      simp [composeProofFull]
    | e :: e' :: J', _, hu, h1, h2 =>
      have hC := common_prefix (e :: e' :: J')
      rw [compose] at h1
      split at h1
      · rename_i hij
        cases h1
        rcases step_ext hu hij hC (nodeEnc _ _ hu.ok) h2 with
          ⟨hf, nx', pre', hs, hp', -⟩ | ⟨hf, hs⟩
        · rw [hs]
          dsimp only
          rw [composeProofFull, ite_eq_left hij, ite_eq_left hf, capProofFull]
          have hle : (common (e :: e' :: J')).length ≤ 2 * key.length := by
            have := congrArg List.length hf; simp at this; omega
          have hpfull : PointsFull (e :: e' :: J') (common (e :: e' :: J')).length nx' := by
            rcases hp' with ⟨rfl, -⟩ | ⟨ts', q', h1', h2', -, rfl, -⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨ts', q', h1', h2', rfl⟩
          exact walk_compose_full key n _ _ nx' rest (under_ext hu hC hf) (by simp) hle
            (by omega) hpfull
        · rw [hs]
          dsimp only
          rw [composeProofFull, ite_eq_left hij, ite_eq_right hf, holds_off hC hf]
          rfl
      · rename_i hij
        cases h1
        have hn' : ∀ x, NodeEnc (sub (e :: e' :: J') i x) (i + 1) := fun x =>
          nodeEnc _ _ (fun f hf => hu.ok f (List.mem_filter.mp hf).1)
        rcases step_branch hu hi hn' h2 with ⟨hik, hs⟩ | ⟨hlt, hsub, hs⟩ |
            ⟨hlt, f, J'', hsub, nx', pre', hs, hp', -⟩
        · rw [hs]
          dsimp only
          rw [composeProofFull, ite_eq_right hij,
            List.getElem?_eq_none (by rw [hkl]; omega)]
          rfl
        · rw [hs]
          dsimp only
          have hx := nibbles_getElem? hlt
          rw [composeProofFull, ite_eq_right hij, hx]
          dsimp only
          rw [← holds_sub hx, hsub]
          simp [capProofFull, holds]
        · rw [hs]
          dsimp only
          have hx := nibbles_getElem? hlt
          rw [composeProofFull, ite_eq_right hij, hx]
          dsimp only
          rw [← holds_sub hx, hsub, capProofFull]
          rw [← hsub]
          have hpfull : PointsFull (sub (e :: e' :: J') i (nibble key i)) (i + 1) nx' := by
            rw [hsub]
            rcases hp' with ⟨rfl, -⟩ | ⟨ts', q', h1', h2', -, rfl, -⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨ts', q', h1', h2', rfl⟩
          exact walk_compose_full key n _ _ nx' rest (under_sub hu hx) (by rw [hsub]; simp)
            (by omega) (by omega) hpfull

/-- What the trie of `I` holds at `k` is what `I` holds there. -/
theorem holds_y (I : Map) (k : Bytes) : holds (y I) (nibbles k) = get I k := by
  unfold holds get y
  rw [List.find?_map]
  have : ((fun e : Entry => decide (e.1 = nibbles k)) ∘ fun p : Bytes × Bytes => (nibbles p.1, p.2))
      = fun p => decide (p.1 = k) := by
    funext p
    simp only [Function.comp, decide_eq_decide]
    exact ⟨nibbles_inj, fun h => h ▸ rfl⟩
  rw [this]
  cases I.find? _ <;> rfl

theorem under_y {I : Map} (hI : WellFormed I) (k : Bytes) : Under (nibbles k) (y I) 0 := by
  refine ⟨fun e _ => by simp, fun e he => ?_⟩
  simp only [y, List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  have hk := hI.keys p hp
  obtain ⟨h0, hl⟩ := hI.values p hp
  exact ⟨by simp only [nibbles_length]; omega, nibbles_lt _, h0, hl⟩

theorem encodeBytes_nil : encodeBytes [] = some [0x80] := by decide

/-- The empty map's root is the empty trie's, `emptyRoot`. -/
theorem root_nil : root [] = emptyRoot := by
  simp [root, y, compose, rlp, encodeTree, encodeBytes_nil, emptyRoot]

/-- The empty map's proof of any key is `0x80`, the RLP of `()`. -/
theorem proofOf_nil (k : Bytes) : proofOf [] k = [0x80] := by
  simp [proofOf, y, compose, rlp, encodeTree, encodeBytes_nil, composeProof]

/-- **Completeness.** In a `WellFormed` map `I`, for every key `k` of at most `maxKey` (32)
bytes, `lookup` accepts `proofOf I k`, the proof of `k` in the trie of `I` (Appendix D),
under its root `root I`, and finds what `I` holds at `k`: the value of the first pair with
key `k`, or absence. -/
theorem lookup_complete {I : Map} (hI : WellFormed I) {k : Bytes} (hk : k.length ≤ maxKey) :
    lookup (root I) k (proofOf I k) = some (get I k) := by
  cases hI' : I with
  | nil =>
    subst hI'
    rw [root_nil, proofOf_nil, lookup_empty hk (Or.inr rfl)]
    rfl
  | cons p I' =>
    rw [← hI']
    have hu := under_y hI k
    have hne : y I ≠ [] := by simp [y, hI']
    obtain ⟨ts, q, h1, h2, h3⟩ := (nodeEnc (y I) 0 hu.ok).1 hne
    have hhead : ∃ b r, rlp (compose (y I) 0) = b :: r ∧ 192 ≤ b.toNat := by
      have h3' : encodeTree (.branch ts) = some (rlp (compose (y I) 0)) := by rw [← h1]; exact h3
      simp only [encodeTree, h2, Option.bind_some] at h3'
      exact encodeList_head h3'
    obtain ⟨b, r, hb, h192⟩ := hhead
    have hnp : ¬(proofOf I k = [] ∨ proofOf I k = [0x80]) := by
      rw [proofOf, hb]
      rintro (h | h)
      · simp at h
      · simp only [List.cons_append, List.cons.injEq] at h
        have := congrArg UInt8.toNat h.1
        simp at this
        omega
    have hw := walk_compose k (2 * k.length + 1) (y I) 0 (.hashed (root I))
      (rlp (compose (y I) 0)) hu hne (Nat.zero_le _) (by omega) (Or.inl ⟨rfl, rfl⟩)
    unfold lookup
    rw [ite_eq_right (by omega), ite_eq_right (fun h => hnp h.1)]
    rw [proofOf, hw]
    simp only [ite_true, holds_y]

theorem proofOfFull_nil (k : Bytes) : proofOfFull [] k = [0x80] := by
  simp [proofOfFull, y, compose, rlp, encodeTree, encodeBytes_nil, composeProofFull]

/-- **Completeness for full proofs.** `lookup` also accepts `proofOfFull I k`, the proof stream
that includes `< 32`-byte inline nodes on `k`'s path (as anvil's `eth_getProof` returns). -/
theorem lookup_complete_full {I : Map} (hI : WellFormed I) {k : Bytes} (hk : k.length ≤ maxKey) :
    lookup (root I) k (proofOfFull I k) = some (get I k) := by
  cases hI' : I with
  | nil =>
    subst hI'
    rw [root_nil, proofOfFull_nil, lookup_empty hk (Or.inr rfl)]
    rfl
  | cons p I' =>
    rw [← hI']
    have hu := under_y hI k
    have hne : y I ≠ [] := by simp [y, hI']
    obtain ⟨ts, q, h1, h2, h3⟩ := (nodeEnc (y I) 0 hu.ok).1 hne
    have hhead : ∃ b r, rlp (compose (y I) 0) = b :: r ∧ 192 ≤ b.toNat := by
      have h3' : encodeTree (.branch ts) = some (rlp (compose (y I) 0)) := by rw [← h1]; exact h3
      simp only [encodeTree, h2, Option.bind_some] at h3'
      exact encodeList_head h3'
    obtain ⟨b, r, hb, h192⟩ := hhead
    have hnp : ¬(proofOfFull I k = [] ∨ proofOfFull I k = [0x80]) := by
      rw [proofOfFull, hb]
      rintro (h | h)
      · simp at h
      · simp only [List.cons_append, List.cons.injEq] at h
        have := congrArg UInt8.toNat h.1
        simp at this
        omega
    have hw := walk_compose_full k (2 * k.length + 1) (y I) 0 (.hashed (root I))
      [] hu hne (Nat.zero_le _) (by omega) (Or.inl rfl)
    rw [List.append_nil] at hw
    unfold lookup
    rw [ite_eq_right (by omega), ite_eq_right (fun h => hnp h.1)]
    rw [proofOfFull, hw]
    simp only [ite_true, holds_y]

/-- **Soundness.** A proof that `lookup` accepts for a key under the root of a `WellFormed`
map `I` gives what `I` holds at the key, or exhibits a Keccak-256 collision: the two byte
strings `collision` computes from the root, the key, that proof and `proofOf I k`, the honest
proof, which are different and have the same Keccak-256. -/
theorem lookup_sound {I : Map} (hI : WellFormed I) {k proof : Bytes} {f : Found}
    (h : lookup (root I) k proof = some f) :
    f = get I k ∨ IsCollision (collision (root I) k proof (proofOf I k)) := by
  have hk : k.length ≤ maxKey := by
    unfold lookup at h
    split at h
    · contradiction
    · omega
  by_cases hf : f = get I k
  · exact Or.inl hf
  · exact Or.inr (binding h (lookup_complete hI hk) hf)

/-! ## Secure tries: accounts and storage

Ethereum's state and storage tries are secure tries (Yellow Paper, section 4.1): the key of a
pair is the Keccak-256 of the address or slot. Two different addresses with one Keccak-256
would make the trie hold one of them only; the theorems name that pair (`clash`) rather than
assume it away. -/

/-- A secure trie's pairs: at the Keccak-256 of each key, its value's encoding `enc`. -/
def secure {α : Type} (enc : α → Bytes) (S : List (Bytes × α)) : Map :=
  S.map fun p => (keccak p.1, enc p.2)

/-- The two keys a secure trie could confuse with `a`: the first key in `S` with `a`'s
Keccak-256, and `a`; `(a, a)` when there is none. They are a Keccak-256 collision exactly when
that first key is not `a`. -/
def clash {α : Type} (S : List (Bytes × α)) (a : Bytes) : Bytes × Bytes :=
  match S.find? (fun p => keccak p.1 = keccak a) with
  | some p => (p.1, a)
  | none => (a, a)

private theorem find?_first {β : Type} {P Q : β → Bool} (h : ∀ y, Q y = true → P y = true) :
    ∀ {l : List β} {x : β}, l.find? P = some x → Q x = true → l.find? Q = some x
  | [], _, hx, _ => by simp at hx
  | y :: l, x, hx, hq => by
    rw [List.find?_cons] at hx ⊢
    by_cases hp : P y = true
    · rw [hp] at hx
      cases hx
      rw [hq]
    · rw [Bool.not_eq_true] at hp
      rw [hp] at hx
      have : Q y = false := by
        cases hqy : Q y
        · rfl
        · exact absurd (h y hqy) (by rw [hp]; decide)
      rw [this]
      exact find?_first h hx hq

/-- A secure trie holds at `keccak a` what the map holds at `a`, unless `clash S a` is a
Keccak-256 collision. -/
theorem get_secure {α : Type} (enc : α → Bytes) (S : List (Bytes × α)) (a : Bytes) :
    get (secure enc S) (keccak a) = get (S.map fun p => (p.1, enc p.2)) a ∨
      IsCollision (clash S a) := by
  have hQP : ∀ p : Bytes × α, decide (p.1 = a) = true → decide (keccak p.1 = keccak a) = true :=
    fun p h => by simp only [decide_eq_true_eq] at h ⊢; rw [h]
  unfold get secure clash
  rw [List.find?_map, List.find?_map]
  simp only [Function.comp_def]
  cases hf : S.find? (fun p => decide (keccak p.1 = keccak a)) with
  | none =>
    left
    rw [(List.find?_eq_none.mpr fun p hp hq => (List.find?_eq_none.mp hf) p hp (hQP p hq))]
    rfl
  | some p =>
    by_cases hpa : p.1 = a
    · left
      rw [find?_first hQP hf (by simp [hpa])]
      rfl
    · right
      have := List.find?_some hf
      simp only [decide_eq_true_eq] at this
      exact ⟨hpa, this⟩

theorem wellFormed_secure {α : Type} {enc : α → Bytes} {S : List (Bytes × α)}
    (h : ∀ p ∈ S, enc p.2 ≠ [] ∧ (enc p.2).length < 2 ^ 32) : WellFormed (secure enc S) := by
  constructor
  · intro p hp
    simp only [secure, List.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    simp [keccak_length, maxKey]
  · intro p hp
    simp only [secure, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact h q hq

/-! ### Accounts -/

/-- An account the Yellow Paper's world state holds: its account validity function `v`
(section 4.1), a nonce and a balance in ℕ_256 (below 2^256), a storage root and a code hash in
𝔹_32 (32 bytes). -/
def AccountValid (a : Account) : Prop :=
  a.nonce < 2 ^ 256 ∧ a.balance < 2 ^ 256 ∧ a.storageRoot.length = 32 ∧ a.codeHash.length = 32

/-- An account `Spec.Mpt.account` reads back (`accountOf_iff`): a nonce below 2^64, EIP-2681's
bound, a balance below 2^128 wei, as the code reads it into a `u128` (the Yellow Paper allows
balances below 2^256; `accountOf` refuses a larger one rather than truncate it), and two
32-byte hashes. -/
def AccountOk (a : Account) : Prop :=
  a.nonce < 2 ^ 64 ∧ a.balance < 2 ^ 128 ∧ a.storageRoot.length = 32 ∧ a.codeHash.length = 32

theorem accountValid_of_ok {a : Account} (h : AccountOk a) : AccountValid a :=
  ⟨by have := h.1; omega, by have := h.2.1; omega, h.2.2⟩

/-- The RLP of an account, the value the state trie holds (Yellow Paper, section 4.1, `p(a)`):
`[nonce, balance, storageRoot, codeHash]`, the scalars as their minimal big-endian bytes. -/
def accountRlp (a : Account) : Bytes :=
  rlp (.branch [.leaf (be a.nonce), .leaf (be a.balance), .leaf a.storageRoot, .leaf a.codeHash])

/-- A world state: accounts at addresses. An address absent from it holds the empty account. -/
abbrev State := List (Bytes × Account)

/-- The account at `a` in `S`: the first with that address, or `emptyAccount`. -/
def accountAt (S : State) (a : Bytes) : Account :=
  match S.find? (fun p => p.1 = a) with
  | some p => p.2
  | none => emptyAccount

/-- The state root of `S`: the root of the secure trie of its accounts' RLP. -/
def stateRoot (S : State) : Bytes := root (secure accountRlp S)

/-- The proof of the address `a`, as geth's `eth_getProof` returns it (its `accountProof`),
`proofOf` of `a`'s Keccak-256. -/
def accountProof (S : State) (a : Bytes) : Bytes := proofOf (secure accountRlp S) (keccak a)

/-- The proof of the address `a` when inline nodes on the path are also listed as items (as
anvil's `eth_getProof` returns). -/
def accountProofFull (S : State) (a : Bytes) : Bytes :=
  proofOfFull (secure accountRlp S) (keccak a)

/-- A valid account has an RLP encoding, nonempty and shorter than 2^32 bytes. -/
theorem accountRlp_valid {a : Account} (ha : AccountValid a) :
    encodeTree (.branch [.leaf (be a.nonce), .leaf (be a.balance), .leaf a.storageRoot,
      .leaf a.codeHash]) = some (accountRlp a) ∧ accountRlp a ≠ [] ∧
      (accountRlp a).length < 2 ^ 32 := by
  obtain ⟨hn, hb, hs, hc⟩ := ha
  have l1 := be_length_le (k := 32) (by simpa using hn)
  have l2 := be_length_le (k := 32) (by simpa using hb)
  have hleaf : ∀ t ∈ [Tree.leaf (be a.nonce), .leaf (be a.balance), .leaf a.storageRoot,
      .leaf a.codeHash], ∃ e, encodeTree t = some e ∧ e.length ≤ 41 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    have leaf : ∀ x : Bytes, x.length ≤ 32 → ∃ e, encodeTree (.leaf x) = some e ∧ e.length ≤ 41 :=
      fun x hx => by
        obtain ⟨e, he⟩ := encodeBytes_some (x := x) (by omega)
        exact ⟨e, he, by have := encodeBytes_length_le he; omega⟩
    rcases ht with rfl | rfl | rfl | rfl
    · exact leaf _ (by omega)
    · exact leaf _ (by omega)
    · exact leaf _ (by omega)
    · exact leaf _ (by omega)
  obtain ⟨s, hs', hsl⟩ := encodeTrees_bound 41 _ hleaf
  obtain ⟨v, hv⟩ := encodeList_some (s := s) (by simp at hsl; omega)
  have henc : encodeTree (.branch [.leaf (be a.nonce), .leaf (be a.balance), .leaf a.storageRoot,
      .leaf a.codeHash]) = some v := by simp only [encodeTree, hs', Option.bind_some, hv]
  have hr : accountRlp a = v := by rw [accountRlp, rlp, henc]; rfl
  rw [hr]
  refine ⟨henc, encodeTree_ne_nil henc, ?_⟩
  have := encodeList_length_le hv
  simp at hsl
  omega

/-- `accountOf` reads an `AccountOk` account back from its RLP. -/
theorem accountRlp_ok {a : Account} (ha : AccountOk a) : accountOf (accountRlp a) = some a := by
  obtain ⟨hn, hb, hs, hc⟩ := ha
  exact (accountOf_iff _ a).mpr
    ⟨hn, hb, hs, hc, (accountRlp_valid (accountValid_of_ok ⟨hn, hb, hs, hc⟩)).1⟩

/-- What `accountOf` reads from a valid account's RLP is that account: RLP is injective. -/
theorem accountOf_accountRlp {a b : Account} (ha : AccountValid a)
    (h : accountOf (accountRlp a) = some b) : b = a := by
  obtain ⟨-, -, -, -, hb⟩ := (accountOf_iff _ b).mp h
  have := encodeTree_injective hb (accountRlp_valid ha).1
  simp only [Tree.branch.injEq, List.cons.injEq, Tree.leaf.injEq, and_true] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  cases a
  cases b
  simp only at h1 h2 h3 h4
  rw [be_injective h1, be_injective h2, h3, h4]

/-- A state whose accounts are all `AccountOk` meets `account_complete`'s hypotheses for every
address: its accounts are valid, and the account read is `AccountOk` (the empty one is). -/
theorem accountOk_accountAt {S : State} (hS : ∀ p ∈ S, AccountOk p.2) (a : Bytes) :
    (∀ p ∈ S, AccountValid p.2) ∧ AccountOk (accountAt S a) := by
  refine ⟨fun p hp => accountValid_of_ok (hS p hp), ?_⟩
  unfold accountAt
  cases hf : S.find? (fun p => decide (p.1 = a)) with
  | none => exact ⟨by decide, by decide, keccak_length _, keccak_length _⟩
  | some p => exact hS p (List.mem_of_find?_eq_some hf)

/-- **Accounts, completeness.** In a state `S` of `AccountValid` accounts, for an address `a`
whose account is `AccountOk`, `account` accepts `accountProof S a`, the proof of `a` (geth's
`accountProof`), under `S`'s state root, and reads the account at `a` (the first with that
address, or the empty one), unless `clash S a` is a Keccak-256 collision: the first address of
`S` with `a`'s Keccak-256 is not `a`. -/
theorem account_complete {S : State} (hS : ∀ p ∈ S, AccountValid p.2) {a : Bytes}
    (ha : AccountOk (accountAt S a)) :
    account (stateRoot S) a (accountProof S a) = some (accountAt S a) ∨
      IsCollision (clash S a) := by
  have ha' : ∀ p, S.find? (fun p => decide (p.1 = a)) = some p → AccountOk p.2 := by
    intro p hf
    have : accountAt S a = p.2 := by unfold accountAt; rw [hf]
    exact this ▸ ha
  rcases get_secure accountRlp S a with hg | hc
  · left
    have hw : WellFormed (secure accountRlp S) :=
      wellFormed_secure fun p hp => (accountRlp_valid (hS p hp)).2
    unfold account
    rw [stateRoot, accountProof, lookup_complete hw (by simp [keccak_length, maxKey]), hg]
    unfold get accountAt
    rw [List.find?_map]
    simp only [Function.comp_def]
    cases hf : S.find? (fun p => decide (p.1 = a)) with
    | none => rfl
    | some p => exact accountRlp_ok (ha' p hf)
  · exact Or.inr hc

/-- **Accounts, completeness for full proofs.** `account` also accepts `accountProofFull S a`. -/
theorem account_complete_full {S : State} (hS : ∀ p ∈ S, AccountValid p.2) {a : Bytes}
    (ha : AccountOk (accountAt S a)) :
    account (stateRoot S) a (accountProofFull S a) = some (accountAt S a) ∨
      IsCollision (clash S a) := by
  have ha' : ∀ p, S.find? (fun p => decide (p.1 = a)) = some p → AccountOk p.2 := by
    intro p hf
    have : accountAt S a = p.2 := by unfold accountAt; rw [hf]
    exact this ▸ ha
  rcases get_secure accountRlp S a with hg | hc
  · left
    have hw : WellFormed (secure accountRlp S) :=
      wellFormed_secure fun p hp => (accountRlp_valid (hS p hp)).2
    unfold account
    have hkl : (keccak a).length ≤ maxKey := by simp [keccak_length, maxKey]
    rw [stateRoot, accountProofFull, lookup_complete_full hw hkl, hg]
    unfold get accountAt
    rw [List.find?_map]
    simp only [Function.comp_def]
    cases hf : S.find? (fun p => decide (p.1 = a)) with
    | none => rfl
    | some p => exact accountRlp_ok (ha' p hf)
  · exact Or.inr hc

/-- **Accounts, soundness.** In a state `S` of `AccountValid` accounts, an account that
`account` reads from any proof under `S`'s state root is the account at `a`, or `clash S a` is
a Keccak-256 collision, or the two byte strings `collision` computes from the root,
`keccak a`, that proof and the honest `accountProof S a` are a Keccak-256 collision. -/
theorem account_sound {S : State} (hS : ∀ p ∈ S, AccountValid p.2) {a proof : Bytes}
    {acct : Account} (h : account (stateRoot S) a proof = some acct) :
    acct = accountAt S a ∨ IsCollision (clash S a) ∨
      IsCollision (collision (stateRoot S) (keccak a) proof (accountProof S a)) := by
  have hw : WellFormed (secure accountRlp S) :=
    wellFormed_secure fun p hp => (accountRlp_valid (hS p hp)).2
  unfold account at h
  cases hl : lookup (stateRoot S) (keccak a) proof with
  | none => rw [hl] at h; contradiction
  | some f =>
    rw [hl] at h
    rcases lookup_sound hw hl with hf | hc
    · rcases get_secure accountRlp S a with hg | hc'
      · left
        rw [hf, hg] at h
        unfold get at h
        unfold accountAt
        rw [List.find?_map] at h
        simp only [Function.comp_def] at h
        cases hfd : S.find? (fun p => decide (p.1 = a)) with
        | none => rw [hfd] at h; exact (Option.some.inj h).symm
        | some p =>
          rw [hfd] at h
          exact accountOf_accountRlp (hS p (List.mem_of_find?_eq_some hfd)) h
      · exact Or.inr (Or.inl hc')
    · exact Or.inr (Or.inr hc)

/-! ### Storage -/

/-- The RLP of a storage value, what the storage trie holds (Yellow Paper, section 4.1): the
encoding of its minimal big-endian bytes. -/
def slotRlp (x : Nat) : Bytes := rlp (.leaf (be x))

/-- A contract's storage: values at slots, each nonzero and below 2^256 (a slot holding zero
is absent from the trie). A slot absent from it holds zero. -/
abbrev Storage := List (Bytes × Nat)

/-- A storage as its trie holds it (Yellow Paper, section 4.1: 256-bit integers, as their
RLP): every value nonzero (clients delete a slot set to zero, and `slotOf` refuses an encoded
zero) and below 2^256. -/
def StorageOk (T : Storage) : Prop := ∀ p ∈ T, 0 < p.2 ∧ p.2 < 2 ^ 256

/-- The value at `slot` in `T`: the first with that slot, or zero. -/
def slotAt (T : Storage) (slot : Bytes) : Nat :=
  match T.find? (fun p => p.1 = slot) with
  | some p => p.2
  | none => 0

/-- The storage root of `T`: the root of the secure trie of its values' RLP. -/
def storageRoot (T : Storage) : Bytes := root (secure slotRlp T)

/-- The proof of `slot`, as geth's `eth_getProof` returns it (a `storageProof`'s `proof`),
`proofOf` of the slot's Keccak-256. anvil (1.5.1) also lists the inline nodes on the path as items
(`storageProofFull`), which `lookup` accepts too; for an empty storage geth sends nothing, which
`lookup_empty` accepts. -/
def storageProof (T : Storage) (slot : Bytes) : Bytes := proofOf (secure slotRlp T) (keccak slot)

/-- The proof of `slot` when inline nodes on the path are also listed as items (as anvil's
`eth_getProof` returns). -/
def storageProofFull (T : Storage) (slot : Bytes) : Bytes :=
  proofOfFull (secure slotRlp T) (keccak slot)

theorem slotRlp_ok {x : Nat} (h0 : 0 < x) (hx : x < 2 ^ 256) :
    slotOf (slotRlp x) = some x ∧ slotRlp x ≠ [] ∧ (slotRlp x).length < 2 ^ 32 := by
  have hl := be_length_le (k := 32) (by simpa using hx)
  obtain ⟨v, hv⟩ := encodeBytes_some (x := be x) (by omega)
  have hr : slotRlp x = v := by rw [slotRlp, rlp]; simp only [encodeTree, hv]; rfl
  rw [hr]
  refine ⟨(slotOf_iff v x).mpr ⟨h0, hx, hv⟩, encodeTree_ne_nil (t := .leaf _) hv, ?_⟩
  have := encodeBytes_length_le hv
  omega

/-- **Storage, completeness.** In a storage `T` that is `StorageOk`, `storage` accepts
`storageProof T slot`, the proof of any slot (geth's `storageProof`'s `proof`),
under `T`'s storage root, and reads the value at the slot (the first with that slot, or zero),
unless `clash T slot` is a Keccak-256 collision: the first slot of `T` with the slot's
Keccak-256 is not that slot. -/
theorem storage_complete {T : Storage} (hT : StorageOk T) (slot : Bytes) :
    storage (storageRoot T) slot (storageProof T slot) = some (slotAt T slot) ∨
      IsCollision (clash T slot) := by
  rcases get_secure slotRlp T slot with hg | hc
  · left
    have hw : WellFormed (secure slotRlp T) :=
      wellFormed_secure fun p hp => (slotRlp_ok (hT p hp).1 (hT p hp).2).2
    unfold storage
    rw [storageRoot, storageProof, lookup_complete hw (by simp [keccak_length, maxKey]), hg]
    unfold get slotAt
    rw [List.find?_map]
    simp only [Function.comp_def]
    cases hf : T.find? (fun p => decide (p.1 = slot)) with
    | none => rfl
    | some p =>
      have hp := hT p (List.mem_of_find?_eq_some hf)
      exact (slotRlp_ok hp.1 hp.2).1
  · exact Or.inr hc

/-- **Storage, completeness for full proofs.** `storage` also accepts `storageProofFull T slot`
(including `< 32`-byte inline nodes on the path, as anvil's `eth_getProof` returns). -/
theorem storage_complete_full {T : Storage} (hT : StorageOk T) (slot : Bytes) :
    storage (storageRoot T) slot (storageProofFull T slot) = some (slotAt T slot) ∨
      IsCollision (clash T slot) := by
  rcases get_secure slotRlp T slot with hg | hc
  · left
    have hw : WellFormed (secure slotRlp T) :=
      wellFormed_secure fun p hp => (slotRlp_ok (hT p hp).1 (hT p hp).2).2
    unfold storage
    have hkl : (keccak slot).length ≤ maxKey := by simp [keccak_length, maxKey]
    rw [storageRoot, storageProofFull, lookup_complete_full hw hkl, hg]
    unfold get slotAt
    rw [List.find?_map]
    simp only [Function.comp_def]
    cases hf : T.find? (fun p => decide (p.1 = slot)) with
    | none => rfl
    | some p =>
      have hp := hT p (List.mem_of_find?_eq_some hf)
      exact (slotRlp_ok hp.1 hp.2).1
  · exact Or.inr hc

/-- **Storage, soundness.** A value that `storage` reads from any proof under the storage root
of a `StorageOk` storage `T` is the value at the slot, or `clash T slot` is a Keccak-256
collision, or the two byte strings `collision` computes from the root, `keccak slot`, that
proof and the honest `storageProof T slot` are a Keccak-256 collision. -/
theorem storage_sound {T : Storage} (hT : StorageOk T) {slot proof : Bytes}
    {x : Nat} (h : storage (storageRoot T) slot proof = some x) :
    x = slotAt T slot ∨ IsCollision (clash T slot) ∨
      IsCollision (collision (storageRoot T) (keccak slot) proof (storageProof T slot)) := by
  rcases storage_complete hT slot with hc | hc
  · by_cases he : x = slotAt T slot
    · exact Or.inl he
    · exact Or.inr (Or.inr (storage_binding h hc he))
  · exact Or.inr (Or.inl hc)

/-! ## Test vectors

The roots of `ethereum/tests`' `TrieTests/trieanyorder.json` (also in
`crates/verified/tests/fixtures`), which `lake build` evaluates in the interpreter: keys of
different lengths, keys that are prefixes of others (values in branches), inline nodes, and
binary keys. They check that the model is the trie Ethereum's clients build; they are tests, not
theorems. -/

open Common (ascii) in
#guard root [(ascii "A", ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")] ==
  [0xd2, 0x37, 0x86, 0xfb, 0x4a, 0x01, 0x0d, 0xa3, 0xce, 0x63, 0x9d, 0x66, 0xd5, 0xe9, 0x04, 0xa1,
    0x1d, 0xbc, 0x02, 0x74, 0x6d, 0x1c, 0xe2, 0x50, 0x29, 0xe5, 0x32, 0x90, 0xca, 0xbf, 0x28, 0xab]

open Common (ascii) in
#guard root [(ascii "doe", ascii "reindeer"), (ascii "dog", ascii "puppy"),
    (ascii "dogglesworth", ascii "cat")] ==
  [0x8a, 0xad, 0x78, 0x9d, 0xff, 0x2f, 0x53, 0x8b, 0xca, 0x5d, 0x8e, 0xa5, 0x6e, 0x8a, 0xbe, 0x10,
    0xf4, 0xc7, 0xba, 0x3a, 0x5d, 0xea, 0x95, 0xfe, 0xa4, 0xcd, 0x6e, 0x7c, 0x3a, 0x11, 0x68, 0xd3]

open Common (ascii) in
#guard root [(ascii "do", ascii "verb"), (ascii "horse", ascii "stallion"),
    (ascii "doge", ascii "coin"), (ascii "dog", ascii "puppy")] ==
  [0x59, 0x91, 0xbb, 0x8c, 0x65, 0x14, 0x14, 0x8a, 0x29, 0xdb, 0x67, 0x6a, 0x14, 0xac, 0x50, 0x6c,
    0xd2, 0xcd, 0x57, 0x75, 0xac, 0xe6, 0x3c, 0x30, 0xa4, 0xfe, 0x45, 0x77, 0x15, 0xe9, 0xac, 0x84]

open Common (ascii) in
#guard root [(ascii "foo", ascii "bar"), (ascii "food", ascii "bass")] ==
  [0x17, 0xbe, 0xaa, 0x16, 0x48, 0xba, 0xfa, 0x63, 0x3c, 0xda, 0x80, 0x9c, 0x90, 0xc0, 0x4a, 0xf5,
    0x0f, 0xc8, 0xae, 0xd3, 0xcb, 0x40, 0xd1, 0x6e, 0xfb, 0xdd, 0xee, 0x6f, 0xdf, 0x63, 0xc4, 0xc3]

open Common (ascii) in
#guard root [(ascii "be", ascii "e"), (ascii "dog", ascii "puppy"), (ascii "bed", ascii "d")] ==
  [0x3f, 0x67, 0xc7, 0xa4, 0x75, 0x20, 0xf7, 0x9f, 0xaa, 0x29, 0x25, 0x5d, 0x2d, 0x3c, 0x08, 0x4a,
    0x7a, 0x6d, 0xf0, 0x45, 0x31, 0x16, 0xed, 0x72, 0x32, 0xff, 0x10, 0x27, 0x7a, 0x8b, 0xe6, 0x8b]

open Common (ascii) in
#guard root [(ascii "test", ascii "test"), (ascii "te", ascii "testy")] ==
  [0x84, 0x52, 0x56, 0x8a, 0xf7, 0x0d, 0x8d, 0x14, 0x0f, 0x58, 0xd9, 0x41, 0x33, 0x85, 0x42, 0xf6,
    0x45, 0xfc, 0xca, 0x50, 0x09, 0x4b, 0x20, 0xf3, 0xc3, 0xd8, 0xc3, 0xdf, 0x49, 0x33, 0x79, 0x28]

#guard root [([0x00, 0x45], [0x01, 0x23, 0x45, 0x67, 0x89]),
    ([0x45, 0x00], [0x98, 0x76, 0x54, 0x32, 0x10])] ==
  [0x28, 0x55, 0x05, 0xfc, 0xab, 0xe8, 0x4b, 0xad, 0xc8, 0xaa, 0x31, 0x0e, 0x2a, 0xae, 0x17, 0xed,
    0xdc, 0x7d, 0x12, 0x0a, 0xab, 0xec, 0x8a, 0x47, 0x69, 0x02, 0xc8, 0x18, 0x4b, 0x3a, 0x35, 0x03]

/- A storage with an inline node on a slot's path (anvil 1.5.1):
slots 468858 and 1452710, holding 1 and 2, whose Keccak-256 share 10 leading nibbles. Below the
extension and the branch, each slot's leaf is 30 bytes, inline in the branch. Geth's proof of
468858 is the extension and the branch; anvil's also lists the inline leaf as a third item
(`storageProofFull`). `storage` reads 1 from both, and rejects an unrelated trailing item. -/
open Common (word) in
#guard (nibbles (keccak (word 468858))).take 10 == (nibbles (keccak (word 1452710))).take 10 &&
  (nibbles (keccak (word 468858)))[10]? != (nibbles (keccak (word 1452710)))[10]? &&
  (rlp (compose [(nibbles (keccak (word 468858)), slotRlp 1)] 11)).length == 30

open Common (word) in
#guard storage (storageRoot [(word 468858, 1), (word 1452710, 2)]) (word 468858)
  (storageProof [(word 468858, 1), (word 1452710, 2)] (word 468858)) == some 1

open Common (word) in
#guard storage (storageRoot [(word 468858, 1), (word 1452710, 2)]) (word 468858)
  (storageProofFull [(word 468858, 1), (word 1452710, 2)] (word 468858)) == some 1

open Common (word) in
#guard storage (storageRoot [(word 468858, 1), (word 1452710, 2)]) (word 468858)
  (storageProof [(word 468858, 1), (word 1452710, 2)] (word 468858) ++
    rlp (compose [(nibbles (keccak (word 1452710)), slotRlp 2)] 11)) == none

/- The state roots of `ethereum/tests`' `TrieTests/hex_encoded_securetrie_test.json`: accounts at
addresses, keyed by Keccak-256, each value an account's RLP (`accountRlp`). -/
#guard stateRoot [
    ([0xa9, 0x4f, 0x53, 0x74, 0xfc, 0xe5, 0xed, 0xbc, 0x8e, 0x2a,
      0x86, 0x97, 0xc1, 0x53, 0x31, 0x67, 0x7e, 0x6e, 0xbf, 0x0b],
      ⟨1, 99894951, emptyRoot,
        emptyCode⟩),
    ([0x09, 0x5e, 0x7b, 0xae, 0xa6, 0xa6, 0xc7, 0xc4, 0xc2, 0xdf,
      0xeb, 0x97, 0x7e, 0xfa, 0xc3, 0x26, 0xaf, 0x55, 0x2d, 0x87],
      ⟨1, 1, emptyRoot,
        [0x04, 0xbc, 0xcc, 0x5d, 0x94, 0xf4, 0xd1, 0xf9, 0x9a, 0xab, 0x44, 0x36,
        0x9a, 0x91, 0x01, 0x79, 0x93, 0x17, 0x72, 0xf2, 0xa5, 0xc0, 0x01, 0xc3,
        0x22, 0x9f, 0x57, 0x83, 0x1c, 0x10, 0x27, 0x69]⟩),
    ([0xd2, 0x57, 0x16, 0x07, 0xe2, 0x41, 0xec, 0xf5, 0x90, 0xed,
      0x94, 0xb1, 0x2d, 0x87, 0xc9, 0x4b, 0xab, 0xe3, 0x6d, 0xb6],
      ⟨1, 0, [0xba, 0x4b, 0x47, 0x86, 0x5c, 0x55, 0xa3, 0x41, 0xa4, 0xa7, 0x87, 0x59,
        0xbb, 0x91, 0x3c, 0xd1, 0x5c, 0x3e, 0xe8, 0xea, 0xf3, 0x0a, 0x62, 0xfa,
        0x8d, 0x1c, 0x88, 0x63, 0x11, 0x3d, 0x84, 0xe8],
        emptyCode⟩),
    ([0x62, 0xc0, 0x14, 0x74, 0xf0, 0x89, 0xb0, 0x7d, 0xae, 0x60,
      0x34, 0x91, 0x67, 0x5d, 0xc5, 0xb5, 0x74, 0x8f, 0x70, 0x49],
      ⟨0, 0, emptyRoot,
        emptyCode⟩),
    ([0x2a, 0xdc, 0x25, 0x66, 0x50, 0x18, 0xaa, 0x1f, 0xe0, 0xe6,
      0xbc, 0x66, 0x6d, 0xac, 0x8f, 0xc2, 0x69, 0x7f, 0xf9, 0xba],
      ⟨0, 105049, emptyRoot,
        emptyCode⟩)] ==
  [0x73, 0x0a, 0x44, 0x4e, 0x08, 0xab, 0x4b, 0x8d, 0xee, 0x14, 0x7c, 0x9b, 0x23, 0x2f, 0xc5, 0x2d,
    0x34, 0xa2, 0x23, 0xd6, 0x00, 0x03, 0x1c, 0x1e, 0x9d, 0x25, 0xbf, 0xc9, 0x85, 0xcb, 0xd7, 0x97]

#guard stateRoot [
    ([0xa9, 0x4f, 0x53, 0x74, 0xfc, 0xe5, 0xed, 0xbc, 0x8e, 0x2a,
      0x86, 0x97, 0xc1, 0x53, 0x31, 0x67, 0x7e, 0x6e, 0xbf, 0x0b],
      ⟨1, 999999999999878982, emptyRoot,
        emptyCode⟩),
    ([0x09, 0x5e, 0x7b, 0xae, 0xa6, 0xa6, 0xc7, 0xc4, 0xc2, 0xdf,
      0xeb, 0x97, 0x7e, 0xfa, 0xc3, 0x26, 0xaf, 0x55, 0x2d, 0x87],
      ⟨0, 100023, emptyRoot,
        [0x50, 0x16, 0x53, 0xf0, 0x28, 0x40, 0x67, 0x5b, 0x1a, 0xab, 0x03, 0x28,
        0xc6, 0x63, 0x47, 0x62, 0xaf, 0x5d, 0x51, 0x76, 0x4e, 0x78, 0xf9, 0x64,
        0x1c, 0xcc, 0xd9, 0xb2, 0x7b, 0x90, 0xdb, 0x4f]⟩),
    ([0x2a, 0xdc, 0x25, 0x66, 0x50, 0x18, 0xaa, 0x1f, 0xe0, 0xe6,
      0xbc, 0x66, 0x6d, 0xac, 0x8f, 0xc2, 0x69, 0x7f, 0xf9, 0xba],
      ⟨0, 21018, emptyRoot,
        emptyCode⟩)] ==
  [0xa7, 0xc7, 0x87, 0xbf, 0x47, 0x08, 0x08, 0x89, 0x63, 0x08, 0xc2, 0x15, 0xe2, 0x2c, 0x7a, 0x58,
    0x0a, 0x00, 0x87, 0xbb, 0x6d, 0xb6, 0xe8, 0x69, 0x5f, 0xb4, 0x75, 0x95, 0x37, 0x28, 0x3a, 0x83]

#guard stateRoot [
    ([0xa9, 0x4f, 0x53, 0x74, 0xfc, 0xe5, 0xed, 0xbc, 0x8e, 0x2a,
      0x86, 0x97, 0xc1, 0x53, 0x31, 0x67, 0x7e, 0x6e, 0xbf, 0x0b],
      ⟨1, 999999999999822787, emptyRoot,
        emptyCode⟩),
    ([0x09, 0x5e, 0x7b, 0xae, 0xa6, 0xa6, 0xc7, 0xc4, 0xc2, 0xdf,
      0xeb, 0x97, 0x7e, 0xfa, 0xc3, 0x26, 0xaf, 0x55, 0x2d, 0x87],
      ⟨0, 20100000, [0x65, 0xfe, 0xe2, 0xff, 0xfd, 0x7a, 0x68, 0x48, 0x8c, 0xf7, 0xef, 0x79,
        0xf3, 0x5f, 0x79, 0x79, 0x13, 0x31, 0x72, 0xac, 0x57, 0x27, 0xb5, 0xe0,
        0xcf, 0x32, 0x29, 0x53, 0xd1, 0x3d, 0xe4, 0x92],
        [0x6e, 0x5d, 0x8f, 0xec, 0x8b, 0x6b, 0x9b, 0xf4, 0x1c, 0x3f, 0xb9, 0xb6,
        0x16, 0x96, 0xd5, 0xc8, 0x7b, 0x66, 0xf6, 0xda, 0xa9, 0x8d, 0x5f, 0x02,
        0xba, 0x93, 0x61, 0xb0, 0xc6, 0x91, 0x64, 0x67]⟩),
    ([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01],
      ⟨0, 0, emptyRoot,
        emptyCode⟩),
    ([0x2a, 0xdc, 0x25, 0x66, 0x50, 0x18, 0xaa, 0x1f, 0xe0, 0xe6,
      0xbc, 0x66, 0x6d, 0xac, 0x8f, 0xc2, 0x69, 0x7f, 0xf9, 0xba],
      ⟨0, 77213, emptyRoot,
        emptyCode⟩)] ==
  [0x40, 0xb3, 0x7b, 0xe8, 0x8a, 0x49, 0xe2, 0xc0, 0x8b, 0x8d, 0x33, 0xfc, 0xb0, 0x3a, 0x06, 0x76,
    0xff, 0xd0, 0x48, 0x1d, 0xf5, 0x4d, 0xfe, 0xbd, 0x35, 0x12, 0xb8, 0xec, 0x54, 0xf4, 0x0c, 0xad]

end LeanLight.Spec.Mpt.Trie
