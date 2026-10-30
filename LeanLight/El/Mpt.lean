import LeanLight.El.Header

/-!
# Merkle-Patricia proof specification

A modified Merkle-Patricia trie (Yellow Paper, Appendix D) commits to a map from keys to
values by the Keccak-256 of its root node. A proof of a key (EIP-1186's `eth_getProof`) is the
nodes on the path from the root, each the RLP list of a node: a branch of 17 items, sixteen
children then a value, or a leaf or extension of 2 items, a hex-prefix path (Appendix C) then
the value or the child. A child shorter than 32 bytes sits inline in its parent; any other is
named by its hash and is the proof's next node. If the proof stream also lists an inline child
as a standalone RLP list item next (as anvil's `eth_getProof` does), `node` verifies that its
list payload matches the parent's inline payload and consumes it; if omitted (as geth's
`eth_getProof` does), `node` leaves the stream at the following hashed node.

`walk` reads a proof against a key: each node is a list payload,
`step` says what it says about the key from nibble `nib`, and `lookup` accepts only a proof
whose every node is used. A key is at most 32 bytes; the empty trie, whose root is
`emptyRoot`, has no node, and two proofs say it holds nothing (`lookup_empty`): the empty
proof, and its root's own encoding `0x80` alone, which anvil returns for a slot of an account
without storage.

**Binding** (`binding`): two proofs that `lookup` accepts for one key under one root, with
different results, contain two different byte strings with the same Keccak-256, and
`collision` returns them. No axiom: the theorem is about Keccak-256 as it is computed
(`Spec.Keccak.keccak256`), and a forged proof is exactly as hard as a Keccak-256 collision.
The same holds of accounts and storage slots read through proofs (`account_binding`,
`storage_binding`).

**Accounts and storage**: `accountOf` reads exactly the canonical RLP of `[nonce, balance,
storageRoot, codeHash]` (`accountOf_iff`); `slotOf` exactly the canonical RLP of a nonzero
scalar (`slotOf_iff`).
-/

namespace LeanLight.Spec.Mpt

open LeanLight.Spec.Rlp LeanLight.Spec.RlpDecode
open LeanLight.Spec.Header (keccak payloadOf window_all window_drop itemsF_leaves encodeTrees_spans)

/-- The longest key: Ethereum's tries are keyed by 32-byte hashes. -/
def maxKey : Nat := 32

/-- The root of the empty trie: Keccak-256 of the empty byte array's encoding. -/
def emptyRoot : Bytes := keccak [0x80]

/-- The code hash of an account without code. -/
def emptyCode : Bytes := keccak []

/-- Nibble `j` of a byte string, high nibble first. -/
def nibble (key : Bytes) (j : Nat) : Nat :=
  if j % 2 = 0 then (key[j / 2]?.getD 0).toNat / 16 else (key[j / 2]?.getD 0).toNat % 16

/-- What a walk ends with: the key is absent, or this value is stored at it. -/
inductive Found where
  | absent
  | value (v : Bytes)
deriving DecidableEq, Repr

/-- The next node: the proof's next node, which must have this hash, or a node inline in its
parent, given by its list payload. -/
inductive Next where
  | hashed (h : Bytes)
  | inline (payload : Bytes)
deriving DecidableEq, Repr

/-- What one node says: the walk ends, or goes on to a node with the nibbles consumed. -/
inductive Step where
  | found (f : Found)
  | next (n : Next) (nib : Nat)
deriving DecidableEq, Repr

/-- The node an item `c` of node `p` names: inline when it is a list shorter than 32 bytes, by
its hash when it is 32 bytes; empty, it proves absence from a branch. -/
def child (p : Bytes) (c : Span) (nib : Nat) (inBranch : Bool) : Option Step :=
  if c.list then
    if c.pos ≤ c.stop ∧ c.stop - c.pos < 32 then some (.next (.inline (window p c.start c.stop)) nib)
    else none
  else if c.start ≤ c.stop ∧ c.stop - c.start = 32 then
    some (.next (.hashed (window p c.start c.stop)) nib)
  else if inBranch = true ∧ c.start = c.stop then some (.found .absent)
  else none

/-- Whether `path` is a hex-prefix path in `p`: a nonempty byte array of at most 33 bytes (the
flag and a 32-byte key's 64 nibbles) whose first nibble is a flag from 0 to 3 (2 and 3 for a
leaf, 1 and 3 for an odd number of nibbles), followed by a zero nibble when the number is
even. -/
def pathOk (p : Bytes) (path : Span) : Bool :=
  !path.list && decide (path.start < path.stop) && decide (path.stop ≤ p.length) &&
    decide (path.stop - path.start ≤ 33) &&
    decide ((p[path.start]?.getD 0).toNat / 16 ≤ 3) &&
    (decide ((p[path.start]?.getD 0).toNat / 16 % 2 = 1) ||
      decide ((p[path.start]?.getD 0).toNat % 16 = 0))

/-- Whether the `len` nibbles of the path at `start`, after its flag nibble (and the zero
nibble when even), are the key's from nibble `nib`. -/
def pathMatches (p : Bytes) (start : Nat) (odd : Bool) (key : Bytes) (nib len : Nat) : Bool :=
  (List.range len).all fun i => nibble (p.drop start) (i + if odd then 1 else 2) = nibble key (nib + i)

/-- What a leaf or an extension says: a leaf holds the value when its path is the rest of
the key, and proves absence otherwise; an extension's path must be a nonempty prefix of the
rest of the key, and names the next node. -/
def short (p : Bytes) (path c : Span) (key : Bytes) (nib : Nat) : Option Step :=
  if pathOk p path then
    let flag := (p[path.start]?.getD 0).toNat / 16
    let odd := decide (flag % 2 = 1)
    let n := path.stop - path.start
    let len := if odd then 2 * n - 1 else 2 * n - 2
    let rest := 2 * key.length - nib
    if 2 ≤ flag then
      if !(!c.list && decide (c.start < c.stop)) then none
      else if len = rest ∧ pathMatches p path.start odd key nib len then
        some (.found (.value (window p c.start c.stop)))
      else some (.found .absent)
    else if len = 0 then none
    else if len ≤ rest ∧ pathMatches p path.start odd key nib len then child p c (nib + len) false
    else some (.found .absent)
  else none

/-- What a node, given by its list payload `p`, says about `key` from nibble `nib`. -/
def step (key : Bytes) (nib : Nat) (p : Bytes) : Option Step :=
  match itemsAt p 0 p.length with
  | none => none
  | some cs =>
    if cs.length = 17 then
      if nib = 2 * key.length then
        let v := cs[16]?.getD default
        if v.list then none
        else if v.start = v.stop then some (.found .absent)
        else some (.found (.value (window p v.start v.stop)))
      else child p (cs[nibble key nib]?.getD default) (nib + 1) true
    else if cs.length = 2 then short p (cs[0]?.getD default) (cs[1]?.getD default) key nib
    else none

/-- What remains of `stream` after an inline node `q`, consuming a matching copy at the front if
present. -/
def afterInline (q stream : Bytes) : Bytes :=
  match itemAt stream 0 stream.length with
  | some it =>
    if it.list = true ∧ window stream it.start it.stop = q then stream.drop it.stop else stream
  | none => stream

/-- The node `nx` names: its list payload and what follows it in the proof `stream`. A hashed
node is the stream's first item, a list whose Keccak-256 is the hash; an inline node is already in
its parent, and if the stream also lists it next (as some `eth_getProof` endpoints do), that copy
is consumed when its payload matches `q`. -/
def node (nx : Next) (stream : Bytes) : Option (Bytes × Bytes) :=
  match nx with
  | .hashed h =>
    match itemAt stream 0 stream.length with
    | some it =>
      if it.list = true ∧ keccak (window stream 0 it.stop) = h then
        some (window stream it.start it.stop, stream.drop it.stop)
      else none
    | none => none
  | .inline q => some (q, afterInline q stream)

/-- The walk from node `nx` with `nib` nibbles of the key consumed: what it ends with, and the
proof left over. `n` is fuel. -/
def walk : Nat → (key : Bytes) → (nib : Nat) → Next → (stream : Bytes) → Option (Found × Bytes)
  | 0, _, _, _, _ => none
  | n + 1, key, nib, nx, stream =>
    match node nx stream with
    | none => none
    | some (q, rest) =>
      match step key nib q with
      | none => none
      | some (.found f) => some (f, rest)
      | some (.next nx' nib') => walk n key nib' nx' rest

/-- What the trie whose root hash is `root` holds at `key`, as `proof` proves it. Under
`emptyRoot`, the empty proof and `[0x80]`, the root's encoding, prove the key absent. -/
def lookup (root key proof : Bytes) : Option Found :=
  if maxKey < key.length then none
  else if (proof = [] ∨ proof = [0x80]) ∧ root = emptyRoot then some .absent
  else
    match walk (2 * key.length + 1) key 0 (.hashed root) proof with
    | some (f, rest) => if rest = [] then some f else none
    | none => none

/-! ## Binding -/

/-- Two items read at the front of two streams whose encodings are equal have equal payloads:
an item is determined by the bytes it spans. -/
theorem itemAt_raw {s₁ s₂ : Bytes} {i₁ i₂ : Span} (h₁ : itemAt s₁ 0 s₁.length = some i₁)
    (h₂ : itemAt s₂ 0 s₂.length = some i₂) (h : window s₁ 0 i₁.stop = window s₂ 0 i₂.stop) :
    i₁ = i₂ ∧ window s₁ i₁.start i₁.stop = window s₂ i₂.start i₂.stop := by
  unfold itemAt at h₁ h₂
  split at h₁
  · split at h₂
    · rename_i hb₁ hb₂
      cases hd₁ : decodeHead (window s₁ 0 s₁.length) with
      | none => simp [hd₁] at h₁
      | some k₁ =>
        cases hd₂ : decodeHead (window s₂ 0 s₂.length) with
        | none => simp [hd₂] at h₂
        | some k₂ =>
          rw [hd₁] at h₁
          rw [hd₂] at h₂
          simp only [Option.map_some, Option.some.injEq] at h₁ h₂
          subst h₁ h₂
          simp only [Nat.zero_add] at h ⊢
          rw [window_all] at hd₁ hd₂
          have e₁ : window s₁ 0 k₁.size = s₁.take k₁.size := by simp [window]
          have e₂ : window s₂ 0 k₂.size = s₂.take k₂.size := by simp [window]
          rw [e₁, e₂] at h
          have t₁ := decodeHead_take hd₁ (s₂.drop k₂.size)
          rw [h, List.take_append_drop] at t₁
          rw [hd₂] at t₁
          cases t₁
          refine ⟨rfl, ?_⟩
          simp only [window]
          rw [show s₁.take k₁.size = s₂.take k₁.size from h]
    · contradiction
  · contradiction

/-- A Keccak-256 collision: two different byte strings with the same Keccak-256. -/
def IsCollision (p : Bytes × Bytes) : Prop := p.1 ≠ p.2 ∧ keccak p.1 = keccak p.2

theorem node_inline (q stream : Bytes) :
    node (.inline q) stream = some (q, afterInline q stream) :=
  rfl

/-- The two byte strings `collideWalk` finds where two walks first read different nodes for
the same hash. -/
def collideWalk : Nat → (key : Bytes) → (nib : Nat) → Next → Bytes → Bytes → Bytes × Bytes
  | 0, _, _, _, _, _ => ([], [])
  | n + 1, key, nib, nx, s₁, s₂ =>
    match nx with
    | .hashed _ =>
      match itemAt s₁ 0 s₁.length, itemAt s₂ 0 s₂.length with
      | some i₁, some i₂ =>
        if window s₁ 0 i₁.stop ≠ window s₂ 0 i₂.stop then (window s₁ 0 i₁.stop, window s₂ 0 i₂.stop)
        else
          match step key nib (window s₁ i₁.start i₁.stop) with
          | some (.next nx' nib') => collideWalk n key nib' nx' (s₁.drop i₁.stop) (s₂.drop i₂.stop)
          | _ => ([], [])
      | _, _ => ([], [])
    | .inline q =>
      match step key nib q with
      | some (.next nx' nib') => collideWalk n key nib' nx' (afterInline q s₁) (afterInline q s₂)
      | _ => ([], [])

/-- Where two walks of the same key through the same nodes end differently, `collideWalk` finds
a Keccak-256 collision. -/
theorem collideWalk_spec {n : Nat} {key : Bytes} {nib : Nat} {nx : Next} {s₁ s₂ : Bytes}
    {f₁ f₂ : Found} {r₁ r₂ : Bytes} (h₁ : walk n key nib nx s₁ = some (f₁, r₁))
    (h₂ : walk n key nib nx s₂ = some (f₂, r₂)) (hne : f₁ ≠ f₂) :
    IsCollision (collideWalk n key nib nx s₁ s₂) := by
  induction n generalizing nib nx s₁ s₂ with
  | zero => simp [walk] at h₁
  | succ n ih =>
    simp only [walk] at h₁ h₂
    cases nx with
    | hashed h =>
      simp only [node] at h₁ h₂
      cases hi₁ : itemAt s₁ 0 s₁.length with
      | none => simp [hi₁] at h₁
      | some i₁ =>
        cases hi₂ : itemAt s₂ 0 s₂.length with
        | none => simp [hi₂] at h₂
        | some i₂ =>
          rw [hi₁] at h₁
          rw [hi₂] at h₂
          simp only at h₁ h₂
          by_cases hc₁ : i₁.list = true ∧ keccak (window s₁ 0 i₁.stop) = h
          · rw [if_pos hc₁] at h₁
            by_cases hc₂ : i₂.list = true ∧ keccak (window s₂ 0 i₂.stop) = h
            · rw [if_pos hc₂] at h₂
              simp only at h₁ h₂
              simp only [collideWalk, hi₁, hi₂]
              by_cases hr : window s₁ 0 i₁.stop = window s₂ 0 i₂.stop
              · rw [if_neg (fun h' => h' hr)]
                obtain ⟨rfl, hp⟩ := itemAt_raw hi₁ hi₂ hr
                rw [← hp] at h₂
                cases hs : step key nib (window s₁ i₁.start i₁.stop) with
                | none => simp [hs] at h₁
                | some st =>
                  rw [hs] at h₁ h₂
                  cases st with
                  | found f =>
                    simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
                    exact absurd (h₁.1.symm.trans h₂.1) hne
                  | next nx' nib' =>
                    simp only
                    exact ih h₁ h₂
              · rw [if_pos hr]
                exact ⟨hr, hc₁.2.trans hc₂.2.symm⟩
            · rw [if_neg hc₂] at h₂; simp at h₂
          · rw [if_neg hc₁] at h₁; simp at h₁
    | inline q =>
      rw [node_inline] at h₁ h₂
      dsimp only at h₁ h₂
      simp only [collideWalk]
      cases hs : step key nib q with
      | none => simp [hs] at h₁
      | some st =>
        rw [hs] at h₁ h₂
        cases st with
        | found f =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
          exact absurd (h₁.1.symm.trans h₂.1) hne
        | next nx' nib' =>
          simp only
          exact ih h₁ h₂

/-- The first node of a proof: the item at its front. -/
def firstNode (proof : Bytes) : Bytes :=
  match itemAt proof 0 proof.length with
  | some it => window proof 0 it.stop
  | none => []

/-- The two byte strings `binding` says collide: for two accepted proofs of one key under one
root, the first nodes they read differently for the same hash, or, when one proof is the
empty trie's, `[0x80]` and the other's first node. -/
def collision (root key p₁ p₂ : Bytes) : Bytes × Bytes :=
  if p₁ = [] ∨ p₁ = [0x80] then ([0x80], firstNode p₂)
  else if p₂ = [] ∨ p₂ = [0x80] then (firstNode p₁, [0x80])
  else collideWalk (2 * key.length + 1) key 0 (.hashed root) p₁ p₂

/-- A nonempty proof that walks reads, at its front, a list whose Keccak-256 is the root. -/
theorem walk_first {n : Nat} {key : Bytes} {root proof : Bytes} {f : Found} {r : Bytes}
    (h : walk n key 0 (.hashed root) proof = some (f, r)) :
    keccak (firstNode proof) = root ∧ firstNode proof ≠ [0x80] := by
  cases n with
  | zero => simp [walk] at h
  | succ n =>
    simp only [walk, node] at h
    cases hi : itemAt proof 0 proof.length with
    | none => simp [hi] at h
    | some it =>
      rw [hi] at h
      simp only at h
      by_cases hc : it.list = true ∧ keccak (window proof 0 it.stop) = root
      · simp only [firstNode, hi]
        refine ⟨hc.2, ?_⟩
        intro h80
        obtain ⟨-, -, -, -, -, -, hl, henc⟩ := itemAt_span hi
        rw [hc.1] at henc
        obtain ⟨b, rest, he, hb⟩ := encodeList_head henc
        rw [h80] at he
        cases he
        simp at hb
      · rw [if_neg hc] at h; simp at h

/-- The walk reads no node from the empty trie's proofs: neither is a list. -/
theorem walk_emptyProof {n : Nat} {key root proof : Bytes} (hp : proof = [] ∨ proof = [0x80]) :
    walk n key 0 (.hashed root) proof = none := by
  cases n with
  | zero => rfl
  | succ n =>
    have h80 : itemAt [0x80] 0 1 = some ⟨false, 0, 1, 1⟩ := by decide
    rcases hp with rfl | rfl
    · simp [walk, node, itemAt]
    · simp [walk, node, h80]

/-- What `lookup` accepts from one of the empty trie's proofs: absence, under the empty
root. -/
theorem lookup_emptyProof {root key proof : Bytes} {f : Found}
    (hp : proof = [] ∨ proof = [0x80]) (h : lookup root key proof = some f) :
    root = emptyRoot ∧ f = .absent := by
  unfold lookup at h
  split at h
  · contradiction
  · split at h
    · rename_i hc; cases h; exact ⟨hc.2, rfl⟩
    · rw [walk_emptyProof hp] at h; contradiction

/-- What `lookup` accepts from any other proof: where the walk from the root ends. -/
theorem lookup_walk {root key proof : Bytes} {f : Found} (hp : ¬(proof = [] ∨ proof = [0x80]))
    (h : lookup root key proof = some f) :
    ∃ r, walk (2 * key.length + 1) key 0 (.hashed root) proof = some (f, r) := by
  unfold lookup at h
  split at h
  · contradiction
  · rw [if_neg (fun hc => hp hc.1)] at h
    split at h
    · rename_i f' r hw
      split at h
      · cases h; exact ⟨r, hw⟩
      · contradiction
    · contradiction

/-- **The empty trie.** Both of its proofs, the empty one and `[0x80]`, prove every key of at
most 32 bytes absent from it. -/
theorem lookup_empty {key proof : Bytes} (hk : key.length ≤ maxKey)
    (hp : proof = [] ∨ proof = [0x80]) : lookup emptyRoot key proof = some .absent := by
  unfold lookup
  rw [if_neg (by omega), if_pos ⟨hp, rfl⟩]

/-- **Binding.** Two proofs `lookup` accepts for one key under one root, with different
results, hold two different byte strings with the same Keccak-256: `collision` returns them. -/
theorem binding {root key p₁ p₂ : Bytes} {f₁ f₂ : Found} (h₁ : lookup root key p₁ = some f₁)
    (h₂ : lookup root key p₂ = some f₂) (hne : f₁ ≠ f₂) :
    IsCollision (collision root key p₁ p₂) := by
  by_cases hp₁ : p₁ = [] ∨ p₁ = [0x80]
  · obtain ⟨hr, rfl⟩ := lookup_emptyProof hp₁ h₁
    have hp₂ : ¬(p₂ = [] ∨ p₂ = [0x80]) := fun hp₂ => hne (lookup_emptyProof hp₂ h₂).2.symm
    obtain ⟨r, hw⟩ := lookup_walk hp₂ h₂
    obtain ⟨hk₂, hn₂⟩ := walk_first hw
    rw [collision, if_pos hp₁]
    refine ⟨fun h => hn₂ h.symm, ?_⟩
    rw [hk₂, hr, emptyRoot]
  · by_cases hp₂ : p₂ = [] ∨ p₂ = [0x80]
    · obtain ⟨hr, rfl⟩ := lookup_emptyProof hp₂ h₂
      obtain ⟨r, hw⟩ := lookup_walk hp₁ h₁
      obtain ⟨hk₁, hn₁⟩ := walk_first hw
      rw [collision, if_neg hp₁, if_pos hp₂]
      refine ⟨hn₁, ?_⟩
      rw [hk₁, hr, emptyRoot]
    · obtain ⟨r₁, hw₁⟩ := lookup_walk hp₁ h₁
      obtain ⟨r₂, hw₂⟩ := lookup_walk hp₂ h₂
      rw [collision, if_neg hp₁, if_neg hp₂]
      exact collideWalk_spec hw₁ hw₂ hne

/-! ## The walk's progress -/

/-- A child consumes no nibble itself: it names the next node at the nibble it was given (the
branch or extension that read it has already counted its own). -/
theorem child_nib {p : Bytes} {c : Span} {nib nib' : Nat} {b : Bool} {nx : Next}
    (h : child p c nib b = some (.next nx nib')) : nib' = nib := by
  unfold child at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · split at h
    · cases h; rfl
    · split at h
      · cases h
      · contradiction

theorem ite_some_found {C : Prop} [Decidable C] {f g : Found} {nx : Next} {n : Nat}
    (h : (if C then some (Step.found f) else some (Step.found g)) = some (.next nx n)) : False := by
  by_cases hc : C
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; cases h

/-- An extension's tail: what it names consumes its path's nibbles, at least one. -/
theorem ext_progress {L R nib nib' : Nat} {M : Bool} {ch : Option Step} {nx : Next}
    (hch : ∀ nx n', ch = some (.next nx n') → n' = nib + L)
    (h : (if L = 0 then none else if L ≤ R ∧ M = true then ch else some (.found .absent)) =
      some (.next nx nib')) : L ≠ 0 ∧ L ≤ R ∧ nib' = nib + L := by
  by_cases h0 : L = 0
  · rw [if_pos h0] at h; cases h
  · rw [if_neg h0] at h
    by_cases hm : L ≤ R ∧ M = true
    · rw [if_pos hm] at h; exact ⟨h0, hm.1, hch _ _ h⟩
    · rw [if_neg hm] at h; cases h

theorem short_progress {p : Bytes} {path c : Span} {key : Bytes} {nib nib' : Nat} {nx : Next}
    (h : short p path c key nib = some (.next nx nib')) :
    nib < nib' ∧ nib' ≤ 2 * key.length := by
  unfold short at h
  by_cases hp : pathOk p path = true
  · rw [if_pos hp] at h
    simp only at h
    by_cases hf : 2 ≤ (p[path.start]?.getD 0).toNat / 16
    · rw [if_pos hf] at h
      by_cases hc : (!(!c.list && decide (c.start < c.stop))) = true
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc] at h
        exact (ite_some_found h).elim
    · rw [if_neg hf] at h
      have hch : ∀ (L : Nat) nx n', child p c (nib + L) false = some (.next nx n') → n' = nib + L :=
        fun L nx n' hc => child_nib hc
      by_cases ho : decide ((p[path.start]?.getD 0).toNat / 16 % 2 = 1) = true
      · simp only [ho, if_true] at h
        obtain ⟨h0, hle, he⟩ := ext_progress (hch _) h
        omega
      · simp only [ho, Bool.false_eq_true, if_false] at h
        obtain ⟨h0, hle, he⟩ := ext_progress (hch _) h
        omega
  · rw [if_neg hp] at h; cases h

/-- A node that names the next one consumes at least one nibble, and never more than the key
has, for a walk that has not passed the key's end. -/
theorem step_progress {key : Bytes} {nib nib' : Nat} {q : Bytes} {nx : Next}
    (hn : nib ≤ 2 * key.length) (h : step key nib q = some (.next nx nib')) :
    nib < nib' ∧ nib' ≤ 2 * key.length := by
  unfold step at h
  split at h
  · contradiction
  · rename_i cs hcs
    by_cases h17 : cs.length = 17
    · rw [if_pos h17] at h
      by_cases hk : nib = 2 * key.length
      · rw [if_pos hk] at h
        simp only at h
        split at h
        · contradiction
        · split at h
          · cases h
          · cases h
      · rw [if_neg hk] at h
        have := child_nib h
        omega
    · rw [if_neg h17] at h
      by_cases h2 : cs.length = 2
      · rw [if_pos h2] at h
        exact short_progress h
      · rw [if_neg h2] at h
        cases h

/-- Enough fuel is enough: every node but the last consumes a nibble. -/
theorem walk_fuel : ∀ (n m : Nat) (key : Bytes) (nib : Nat) (nx : Next) (s : Bytes),
    nib ≤ 2 * key.length → 2 * key.length - nib < n → 2 * key.length - nib < m →
    walk n key nib nx s = walk m key nib nx s
  | 0, _, _, _, _, _, _, h, _ => by omega
  | _ + 1, 0, _, _, _, _, _, _, h => by omega
  | n + 1, m + 1, key, nib, nx, s, hn, h1, h2 => by
    simp only [walk]
    cases node nx s with
    | none => rfl
    | some qr =>
      obtain ⟨q, rest⟩ := qr
      simp only
      cases hs : step key nib q with
      | none => rfl
      | some st =>
        cases st with
        | found f => rfl
        | next nx' nib' =>
          simp only
          obtain ⟨hlt, hle⟩ := step_progress hn hs
          exact walk_fuel n m key nib' nx' rest hle (by omega) (by omega)

/-! ## Accounts and storage slots -/

/-- An account, as the state trie stores it. -/
structure Account where
  nonce : Nat
  balance : Nat
  storageRoot : Bytes
  codeHash : Bytes
deriving DecidableEq, Repr

/-- The empty account, which an absent one is. -/
def emptyAccount : Account := ⟨0, 0, emptyRoot, emptyCode⟩

/-- Whether `v` is a scalar of at most `max` bytes: no leading zero byte. -/
def scalarOk (v : Bytes) (max : Nat) : Bool :=
  decide (v.length ≤ max) && (decide (v = []) || decide (v[0]?.getD 0 ≠ 0))

/-- The account a leaf value holds, read as `lkd_verified::mpt::account_at` reads it: the
canonical list of a nonce of at most 8 bytes, a balance of at most 16, then two 32-byte
hashes. -/
def accountOf (v : Bytes) : Option Account :=
  match itemAt v 0 v.length with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = v.length then
      match itemsAt v top.start top.stop with
      | none => none
      | some fs =>
        if fs.length = 4 ∧ fs.all (fun it => !it.list) = true ∧
            scalarOk (payloadOf v (fs[0]?.getD default)) 8 = true ∧
            scalarOk (payloadOf v (fs[1]?.getD default)) 16 = true ∧
            (payloadOf v (fs[2]?.getD default)).length = 32 ∧
            (payloadOf v (fs[3]?.getD default)).length = 32 then
          some ⟨beValue (payloadOf v (fs[0]?.getD default)),
                beValue (payloadOf v (fs[1]?.getD default)),
                payloadOf v (fs[2]?.getD default), payloadOf v (fs[3]?.getD default)⟩
        else none
    else none

/-- The value a storage leaf holds, read as `lkd_verified::mpt::slot_at` reads it: the
canonical encoding of a nonzero scalar of at most 32 bytes. -/
def slotOf (v : Bytes) : Option Nat :=
  match itemAt v 0 v.length with
  | none => none
  | some it =>
    if it.list = false ∧ it.stop = v.length ∧ scalarOk (payloadOf v it) 32 = true ∧
        it.start ≠ it.stop then
      some (beValue (payloadOf v it))
    else none

/-- The account at `address` in the state whose root is `root`, as `proof` proves it: the
empty account when absent. -/
def account (root address proof : Bytes) : Option Account :=
  match lookup root (keccak address) proof with
  | none => none
  | some .absent => some emptyAccount
  | some (.value v) => accountOf v

/-- The value of storage slot `slot` under `root`, as `proof` proves it: zero when absent. -/
def storage (root slot proof : Bytes) : Option Nat :=
  match lookup root (keccak slot) proof with
  | none => none
  | some .absent => some 0
  | some (.value v) => slotOf v

/-- A forged account is a Keccak-256 collision: two accepted proofs of different accounts at
one address under one state root hold two byte strings with the same hash. -/
theorem account_binding {root address p₁ p₂ : Bytes} {a₁ a₂ : Account}
    (h₁ : account root address p₁ = some a₁) (h₂ : account root address p₂ = some a₂)
    (hne : a₁ ≠ a₂) : IsCollision (collision root (keccak address) p₁ p₂) := by
  unfold account at h₁ h₂
  cases hl₁ : lookup root (keccak address) p₁ with
  | none => simp [hl₁] at h₁
  | some f₁ =>
    cases hl₂ : lookup root (keccak address) p₂ with
    | none => simp [hl₂] at h₂
    | some f₂ =>
      apply binding hl₁ hl₂
      rintro rfl
      rw [hl₁] at h₁
      rw [hl₂] at h₂
      apply hne
      cases f₁ with
      | absent => simp at h₁ h₂; rw [← h₁, ← h₂]
      | value v => simp at h₁ h₂; rw [h₁] at h₂; cases h₂; rfl

/-- A forged storage value is a Keccak-256 collision. -/
theorem storage_binding {root slot p₁ p₂ : Bytes} {x₁ x₂ : Nat}
    (h₁ : storage root slot p₁ = some x₁) (h₂ : storage root slot p₂ = some x₂) (hne : x₁ ≠ x₂) :
    IsCollision (collision root (keccak slot) p₁ p₂) := by
  unfold storage at h₁ h₂
  cases hl₁ : lookup root (keccak slot) p₁ with
  | none => simp [hl₁] at h₁
  | some f₁ =>
    cases hl₂ : lookup root (keccak slot) p₂ with
    | none => simp [hl₂] at h₂
    | some f₂ =>
      apply binding hl₁ hl₂
      rintro rfl
      rw [hl₁] at h₁
      rw [hl₂] at h₂
      apply hne
      cases f₁ with
      | absent => simp at h₁ h₂; rw [← h₁, ← h₂]
      | value v => simp at h₁ h₂; rw [h₁] at h₂; cases h₂; rfl

/-! ## What accounts and slots are read from -/

/-- The fields of a canonical RLP list of byte arrays spanning `v`. -/
def flatFields (v : Bytes) : Option (List Bytes) :=
  match itemAt v 0 v.length with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = v.length then
      match itemsAt v top.start top.stop with
      | none => none
      | some its => if its.all (fun it => !it.list) = true then some (its.map (payloadOf v)) else none
    else none

/-- `flatFields` reads exactly the canonical encodings of lists of byte arrays. -/
theorem flatFields_iff (v : Bytes) (fs : List Bytes) :
    flatFields v = some fs ↔ encodeTree (.branch (fs.map .leaf)) = some v := by
  constructor
  · intro hd
    unfold flatFields at hd
    split at hd
    · contradiction
    · rename_i top htop
      split at hd
      · rename_i hc
        split at hd
        · contradiction
        · rename_i its hits
          split at hd
          · rename_i hall
            cases hd
            obtain ⟨-, -, -, -, -, -, -, htopenc⟩ := itemAt_span htop
            obtain ⟨hspans, hflat⟩ := itemsAt_spans hits
            have hleaf : ∀ it ∈ its, encodeBytes (payloadOf v it) =
                some (window v it.pos it.stop) := by
              intro it hit
              obtain ⟨-, -, hat⟩ := hspans it hit
              obtain ⟨hp, -, -, -, -, -, -, henc⟩ := itemAt_span hat
              have hl : it.list = false := by
                have := List.all_eq_true.mp hall it hit
                simpa using this
              rw [hl, hp] at henc
              exact henc
            simp only [encodeTree, List.map_map]
            have := encodeTrees_spans v its hleaf
            simp only [Function.comp_def]
            rw [this, hflat, Option.bind_some]
            rw [hc.1, hc.2, window_all] at htopenc
            rw [hc.2]
            exact htopenc
          · contradiction
      · contradiction
  · intro henc
    simp only [encodeTree] at henc
    cases hs : encodeTrees (fs.map .leaf) with
    | none => simp [hs] at henc
    | some s =>
      rw [hs, Option.bind_some] at henc
      have henc' : encodeItem true s = some v := henc
      have hsuf := encodeItem_suffix henc'
      have htop := itemAt_encodeItem henc' (Nat.le_refl _) (r := [])
        (by rw [window_all, List.append_nil])
      unfold flatFields
      rw [htop]
      simp only [true_and]
      rw [if_pos (by omega)]
      have hw : window v (0 + (v.length - s.length)) v.length = s := by
        rw [window_drop, window_all, hsuf.2]
      obtain ⟨its, h1, h2, h3⟩ := itemsF_leaves v (Nat.le_refl _) fs _ hs hw
      have hitems : itemsAt v (0 + (v.length - s.length)) (0 + v.length) = some its := by
        unfold itemsAt
        rw [if_pos ⟨by omega, by omega⟩, show 0 + v.length - (0 + (v.length - s.length)) + 1 =
          v.length - (0 + (v.length - s.length)) + 1 by omega]
        rw [show 0 + v.length = v.length by omega]
        exact h1
      rw [hitems]
      simp only
      rw [if_pos (List.all_eq_true.mpr fun it hit => by simp [h3 it hit]), h2]

/-- What `scalarOk` accepts is the minimal big-endian bytes of its value. -/
theorem scalarOk_be {v : Bytes} {max : Nat} (h : scalarOk v max = true) :
    be (beValue v) = v ∧ beValue v < 256 ^ max := by
  simp only [scalarOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨hl, hz⟩ := h
  refine ⟨be_beValue _ _ rfl ?_, ?_⟩
  · intro b hb
    rcases hz with rfl | hz
    · simp at hb
    · cases v with
      | nil => simp at hb
      | cons c cs => simp at hb hz; rw [← hb]; exact hz
  · exact Nat.lt_of_lt_of_le (beValue_lt v) (Nat.pow_le_pow_right (by omega) hl)

/-- And every minimal big-endian byte string of a value below `256 ^ max` passes it. -/
theorem scalarOk_of_lt {x max : Nat} (h : x < 256 ^ max) : scalarOk (be x) max = true := by
  simp only [scalarOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨be_length_le h, ?_⟩
  by_cases hx : x = 0
  · left; rw [hx, be_zero]
  · right; exact be_head_ne_zero hx

/-- The account fields `accountOf` reads from a field list. -/
def accountOfFields (fs : List Bytes) : Option Account :=
  if fs.length = 4 ∧ scalarOk (fs[0]?.getD []) 8 = true ∧ scalarOk (fs[1]?.getD []) 16 = true ∧
      (fs[2]?.getD []).length = 32 ∧ (fs[3]?.getD []).length = 32 then
    some ⟨beValue (fs[0]?.getD []), beValue (fs[1]?.getD []), fs[2]?.getD [], fs[3]?.getD []⟩
  else none

theorem accountOf_eq (v : Bytes) : accountOf v = (flatFields v).bind accountOfFields := by
  unfold accountOf flatFields
  split
  · rfl
  · rename_i top htop
    split
    · split
      · rfl
      · rename_i its hits
        by_cases hall : its.all (fun it => !it.list) = true
        · rw [if_pos hall, Option.bind_some]
          unfold accountOfFields
          have hd : ∀ i : Nat, (its.map (payloadOf v))[i]?.getD [] = payloadOf v (its[i]?.getD default) := by
            intro i
            by_cases hi : i < its.length
            · simp [List.getElem?_eq_getElem hi]
            · simp [List.getElem?_eq_none (by omega : its.length ≤ i), payloadOf, window,
                show (default : Span) = ⟨false, 0, 0, 0⟩ from rfl]
          simp only [List.length_map, hd]
          by_cases hc : its.length = 4 ∧ scalarOk (payloadOf v (its[0]?.getD default)) 8 = true ∧
              scalarOk (payloadOf v (its[1]?.getD default)) 16 = true ∧
              (payloadOf v (its[2]?.getD default)).length = 32 ∧
              (payloadOf v (its[3]?.getD default)).length = 32
          · rw [if_pos ⟨hc.1, hall, hc.2⟩, if_pos hc]
          · rw [if_neg (fun h => hc ⟨h.1, h.2.2⟩), if_neg hc]
        · rw [if_neg hall, if_neg (fun h => hall h.2.1)]
          rfl
    · rfl

/-- `accountOf` reads exactly the canonical RLP of `[nonce, balance, storageRoot, codeHash]`
with a nonce below 2^64, a balance below 2^128 and two 32-byte hashes. -/
theorem accountOf_iff (v : Bytes) (a : Account) :
    accountOf v = some a ↔ a.nonce < 2 ^ 64 ∧ a.balance < 2 ^ 128 ∧ a.storageRoot.length = 32 ∧
      a.codeHash.length = 32 ∧
      encodeTree (.branch [.leaf (be a.nonce), .leaf (be a.balance), .leaf a.storageRoot,
        .leaf a.codeHash]) = some v := by
  rw [accountOf_eq]
  constructor
  · intro h
    cases hf : flatFields v with
    | none => simp [hf] at h
    | some fs =>
      rw [hf, Option.bind_some] at h
      unfold accountOfFields at h
      split at h
      · rename_i hc
        cases h
        obtain ⟨h4, h0, h1, h2, h3⟩ := hc
        obtain ⟨hb0, hl0⟩ := scalarOk_be h0
        obtain ⟨hb1, hl1⟩ := scalarOk_be h1
        refine ⟨by simpa using hl0, by simpa using hl1, h2, h3, ?_⟩
        simp only
        rw [hb0, hb1]
        have := (flatFields_iff v fs).mp hf
        match fs, h4 with
        | [f0, f1, f2, f3], _ => simpa using this
      · contradiction
  · rintro ⟨hn, hb, hs, hc, henc⟩
    have hf := (flatFields_iff v [be a.nonce, be a.balance, a.storageRoot, a.codeHash]).mpr
      (by simpa using henc)
    rw [hf, Option.bind_some]
    unfold accountOfFields
    simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero, Option.getD_some,
      List.getElem?_cons_succ]
    rw [if_pos ⟨by simp, scalarOk_of_lt (by simpa using hn), scalarOk_of_lt (by simpa using hb), hs,
      hc⟩, beValue_be, beValue_be]

/-- `slotOf` reads exactly the canonical encoding of a nonzero scalar below 2^256. -/
theorem slotOf_iff (v : Bytes) (x : Nat) :
    slotOf v = some x ↔ 0 < x ∧ x < 2 ^ 256 ∧ encodeBytes (be x) = some v := by
  constructor
  · intro h
    unfold slotOf at h
    split at h
    · contradiction
    · rename_i it hit
      split at h
      · rename_i hc
        cases h
        obtain ⟨hl, hs, hok, hne⟩ := hc
        obtain ⟨-, -, -, -, -, -, -, henc⟩ := itemAt_span hit
        rw [hl, hs, window_all] at henc
        obtain ⟨hbe, hlt⟩ := scalarOk_be hok
        have hwl : (payloadOf v it).length = it.stop - it.start := by
          simp only [payloadOf]
          rw [window_length (by omega)]
        have hpw : payloadOf v it = window v it.start v.length := by simp [payloadOf, hs]
        refine ⟨?_, by simpa using hlt, by rw [hbe, hpw]; exact henc⟩
        apply Nat.pos_of_ne_zero
        intro h0
        rw [h0, be_zero] at hbe
        have := congrArg List.length hbe
        simp only [List.length_nil] at this
        obtain ⟨-, h1, h2, -⟩ := itemAt_span hit
        omega
      · contradiction
  · rintro ⟨hpos, hlt, henc⟩
    have henc' : encodeItem false (be x) = some v := henc
    have hit := itemAt_encodeItem henc' (Nat.le_refl _) (r := []) (by rw [window_all, List.append_nil])
    have hsuf := encodeItem_suffix henc'
    unfold slotOf
    rw [hit]
    simp only
    have hp : payloadOf v ⟨false, 0, 0 + (v.length - (be x).length), 0 + v.length⟩ = be x := by
      simp only [payloadOf, Nat.zero_add]
      have := window_drop v 0 (v.length - (be x).length) v.length
      rw [Nat.zero_add] at this
      rw [this, window_all, hsuf.2]
    have hne := be_ne_nil (Nat.pos_iff_ne_zero.mp hpos)
    have hlen := List.length_pos_iff.mpr hne
    rw [if_pos ⟨by simp, by omega, by rw [hp]; exact scalarOk_of_lt (by simpa using hlt), by omega⟩, hp,
      beValue_be]

/-! ## Over a `ByteArray`: what runs

`accountB` and `storageB` are `account` and `storage` with the proof a `ByteArray`
(`accountB_eq`, `storageB_eq`). The walk reads the proof in place, from an offset: each node it
reaches is copied once to hash it and once to read its items, with `itemsAtB`; a leaf's value
is read with `itemAtB` and `itemsAtB` too. The root, the key and the address stay short lists. -/

open LeanLight.Lc.Bytes (byteAt byteAt_eq extract extract_eq slice slice_eq size_eq)
open LeanLight.Spec.Header (keccakB keccakB_eq payloadOfB payloadOfB_eq)

/-- `child`, over a `ByteArray`. -/
def childB (p : ByteArray) (c : Span) (nib : Nat) (inBranch : Bool) : Option Step :=
  if c.list then
    if c.pos ≤ c.stop ∧ c.stop - c.pos < 32 then some (.next (.inline (slice p c.start c.stop)) nib)
    else none
  else if c.start ≤ c.stop ∧ c.stop - c.start = 32 then
    some (.next (.hashed (slice p c.start c.stop)) nib)
  else if inBranch = true ∧ c.start = c.stop then some (.found .absent)
  else none

/-- `pathOk`, over a `ByteArray`. -/
def pathOkB (p : ByteArray) (path : Span) : Bool :=
  !path.list && decide (path.start < path.stop) && decide (path.stop ≤ p.size) &&
    decide (path.stop - path.start ≤ 33) &&
    decide ((byteAt p path.start).toNat / 16 ≤ 3) &&
    (decide ((byteAt p path.start).toNat / 16 % 2 = 1) ||
      decide ((byteAt p path.start).toNat % 16 = 0))

/-- Nibble `j` of the bytes of `p` from `start`, high nibble first. -/
def nibbleB (p : ByteArray) (start j : Nat) : Nat :=
  if j % 2 = 0 then (byteAt p (start + j / 2)).toNat / 16 else (byteAt p (start + j / 2)).toNat % 16

/-- `pathMatches`, over a `ByteArray`. -/
def pathMatchesB (p : ByteArray) (start : Nat) (odd : Bool) (key : Bytes) (nib len : Nat) : Bool :=
  (List.range len).all fun i => nibbleB p start (i + if odd then 1 else 2) = nibble key (nib + i)

/-- `short`, over a `ByteArray`. -/
def shortB (p : ByteArray) (path c : Span) (key : Bytes) (nib : Nat) : Option Step :=
  if pathOkB p path then
    let flag := (byteAt p path.start).toNat / 16
    let odd := decide (flag % 2 = 1)
    let n := path.stop - path.start
    let len := if odd then 2 * n - 1 else 2 * n - 2
    let rest := 2 * key.length - nib
    if 2 ≤ flag then
      if !(!c.list && decide (c.start < c.stop)) then none
      else if len = rest ∧ pathMatchesB p path.start odd key nib len then
        some (.found (.value (slice p c.start c.stop)))
      else some (.found .absent)
    else if len = 0 then none
    else if len ≤ rest ∧ pathMatchesB p path.start odd key nib len then childB p c (nib + len) false
    else some (.found .absent)
  else none

/-- `step`, over a `ByteArray`: what a node, given by its list payload `p`, says about `key`
from nibble `nib`. -/
def stepB (key : Bytes) (nib : Nat) (p : ByteArray) : Option Step :=
  match itemsAtB p 0 p.size with
  | none => none
  | some cs =>
    if cs.length = 17 then
      if nib = 2 * key.length then
        let v := cs[16]?.getD default
        if v.list then none
        else if v.start = v.stop then some (.found .absent)
        else some (.found (.value (slice p v.start v.stop)))
      else childB p (cs[nibble key nib]?.getD default) (nib + 1) true
    else if cs.length = 2 then shortB p (cs[0]?.getD default) (cs[1]?.getD default) key nib
    else none

/-- `node`, over a `ByteArray`: the proof is `proof` from `off` on. The node `nx` names, its
list payload copied, and the offset the proof goes on from. -/
def nodeB (nx : Next) (proof : ByteArray) (off : Nat) : Option (ByteArray × Nat) :=
  match nx with
  | .hashed h =>
    match itemAtB proof off proof.size with
    | some it =>
      if it.list = true ∧ keccakB (extract proof off it.stop) = h then
        some (extract proof it.start it.stop, it.stop)
      else none
    | none => none
  | .inline q =>
    match itemAtB proof off proof.size with
    | some it =>
      if it.list = true ∧ slice proof it.start it.stop = q then
        some (⟨q.toArray⟩, it.stop)
      else some (⟨q.toArray⟩, off)
    | none => some (⟨q.toArray⟩, off)

/-- `walk`, over a `ByteArray`: the proof is `proof` from `off` on, and what is left of it is
given by the offset it starts from. `n` is fuel. -/
def walkB (proof : ByteArray) : Nat → (key : Bytes) → (nib : Nat) → Next → (off : Nat) →
    Option (Found × Nat)
  | 0, _, _, _, _ => none
  | n + 1, key, nib, nx, off =>
    match nodeB nx proof off with
    | none => none
    | some (q, off') =>
      match stepB key nib q with
      | none => none
      | some (.found f) => some (f, off')
      | some (.next nx' nib') => walkB proof n key nib' nx' off'

/-- `lookup`, over a `ByteArray` (`lookupB_eq`). -/
def lookupB (root key : Bytes) (proof : ByteArray) : Option Found :=
  if maxKey < key.length then none
  else if (proof.size = 0 ∨ (proof.size = 1 ∧ byteAt proof 0 = 0x80)) ∧ root = emptyRoot then
    some .absent
  else
    match walkB proof (2 * key.length + 1) key 0 (.hashed root) 0 with
    | some (f, off) => if proof.size ≤ off then some f else none
    | none => none

/-- `accountOf`, over a `ByteArray`. -/
def accountOfB (v : ByteArray) : Option Account :=
  match itemAtB v 0 v.size with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = v.size then
      match itemsAtB v top.start top.stop with
      | none => none
      | some fs =>
        if fs.length = 4 ∧ fs.all (fun it => !it.list) = true ∧
            scalarOk (payloadOfB v (fs[0]?.getD default)) 8 = true ∧
            scalarOk (payloadOfB v (fs[1]?.getD default)) 16 = true ∧
            (payloadOfB v (fs[2]?.getD default)).length = 32 ∧
            (payloadOfB v (fs[3]?.getD default)).length = 32 then
          some ⟨beValue (payloadOfB v (fs[0]?.getD default)),
                beValue (payloadOfB v (fs[1]?.getD default)),
                payloadOfB v (fs[2]?.getD default), payloadOfB v (fs[3]?.getD default)⟩
        else none
    else none

/-- `slotOf`, over a `ByteArray`. -/
def slotOfB (v : ByteArray) : Option Nat :=
  match itemAtB v 0 v.size with
  | none => none
  | some it =>
    if it.list = false ∧ it.stop = v.size ∧ scalarOk (payloadOfB v it) 32 = true ∧
        it.start ≠ it.stop then
      some (beValue (payloadOfB v it))
    else none

/-- `account`, with the proof a `ByteArray` (`accountB_eq`): what the light client runs. -/
def accountB (root address : Bytes) (proof : ByteArray) : Option Account :=
  match lookupB root (keccak address) proof with
  | none => none
  | some .absent => some emptyAccount
  | some (.value v) => accountOfB ⟨v.toArray⟩

/-- `storage`, with the proof a `ByteArray` (`storageB_eq`): what the light client runs. -/
def storageB (root slot : Bytes) (proof : ByteArray) : Option Nat :=
  match lookupB root (keccak slot) proof with
  | none => none
  | some .absent => some 0
  | some (.value v) => slotOfB ⟨v.toArray⟩

theorem childB_eq (p : ByteArray) (c : Span) (nib : Nat) (inBranch : Bool) :
    childB p c nib inBranch = child p.data.toList c nib inBranch := by
  simp only [childB, child, slice_eq]
  rfl

theorem pathOkB_eq (p : ByteArray) (path : Span) : pathOkB p path = pathOk p.data.toList path := by
  simp only [pathOkB, pathOk, byteAt_eq, size_eq]

theorem nibbleB_eq (p : ByteArray) (start j : Nat) :
    nibbleB p start j = nibble (p.data.toList.drop start) j := by
  simp only [nibbleB, nibble, byteAt_eq, List.getElem?_drop]

theorem pathMatchesB_eq (p : ByteArray) (start : Nat) (odd : Bool) (key : Bytes) (nib len : Nat) :
    pathMatchesB p start odd key nib len = pathMatches p.data.toList start odd key nib len := by
  simp only [pathMatchesB, pathMatches, nibbleB_eq]

theorem shortB_eq (p : ByteArray) (path c : Span) (key : Bytes) (nib : Nat) :
    shortB p path c key nib = short p.data.toList path c key nib := by
  simp only [shortB, short, pathOkB_eq, pathMatchesB_eq, childB_eq, byteAt_eq, slice_eq]
  rfl

theorem stepB_eq (key : Bytes) (nib : Nat) (p : ByteArray) :
    stepB key nib p = step key nib p.data.toList := by
  simp only [stepB, step, itemsAtB_eq, size_eq, childB_eq, shortB_eq, slice_eq]
  rfl

/-- The bytes of a proof from an offset on: windows of them are windows of the proof. -/
theorem window_drop_off (l : Bytes) (off a b : Nat) :
    window (l.drop off) a b = window l (off + a) (off + b) := by
  simp only [window, List.take_drop, List.drop_drop]

theorem itemAtB_off (proof : ByteArray) (off : Nat) :
    itemAtB proof off proof.size =
      (itemAt (proof.data.toList.drop off) 0 (proof.data.toList.drop off).length).map
        (Span.shift off) := by
  rw [itemAtB_eq, ← size_eq,
    itemAt_window proof.data.toList (s := off) (e := proof.data.toList.length) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _),
    Nat.sub_self, List.length_drop]
  simp only [window, List.take_of_length_le (Nat.le_refl _)]

theorem nodeB_eq (nx : Next) (proof : ByteArray) (off : Nat) :
    (nodeB nx proof off).map (fun r => (r.1.data.toList, proof.data.toList.drop r.2)) =
      node nx (proof.data.toList.drop off) := by
  cases nx with
  | inline q =>
    simp only [nodeB, node, afterInline, itemAtB_off]
    cases itemAt (proof.data.toList.drop off) 0 (proof.data.toList.drop off).length with
    | none => simp
    | some it =>
      simp only [Option.map_some, Span.shift, slice_eq]
      have h2 : (proof.data.toList.take (it.stop + off)).drop (it.start + off) =
          window (proof.data.toList.drop off) it.start it.stop := by
        rw [window_drop_off, Nat.add_comm off, Nat.add_comm off]; rfl
      have h3 : proof.data.toList.drop (it.stop + off) =
          (proof.data.toList.drop off).drop it.stop := by
        rw [List.drop_drop, Nat.add_comm]
      rw [h2]
      by_cases hc : it.list = true ∧ window (proof.data.toList.drop off) it.start it.stop = q
      · rw [ite_eq_left hc, ite_eq_left hc]
        simp [h3]
      · rw [ite_eq_right hc, ite_eq_right hc]
        simp
  | hashed h =>
    simp only [nodeB, node, itemAtB_off]
    cases itemAt (proof.data.toList.drop off) 0 (proof.data.toList.drop off).length with
    | none => rfl
    | some it =>
      simp only [Option.map_some, Span.shift, keccakB_eq, extract_eq]
      have h1 : (proof.data.toList.take (it.stop + off)).drop off =
          window (proof.data.toList.drop off) 0 it.stop := by
        rw [window_drop_off, Nat.add_zero, Nat.add_comm]; rfl
      have h2 : (proof.data.toList.take (it.stop + off)).drop (it.start + off) =
          window (proof.data.toList.drop off) it.start it.stop := by
        rw [window_drop_off, Nat.add_comm off, Nat.add_comm off]; rfl
      have h3 : proof.data.toList.drop (it.stop + off) =
          (proof.data.toList.drop off).drop it.stop := by
        rw [List.drop_drop, Nat.add_comm]
      rw [h1]
      by_cases hc : it.list = true ∧ keccak (window (proof.data.toList.drop off) 0 it.stop) = h
      · rw [if_pos hc, if_pos hc]
        simp only [Option.map_some, extract_eq, h2, h3]
      · rw [if_neg hc, if_neg hc]
        rfl

theorem walkB_eq (proof : ByteArray) : ∀ (n : Nat) (key : Bytes) (nib : Nat) (nx : Next)
    (off : Nat), (walkB proof n key nib nx off).map (fun r => (r.1, proof.data.toList.drop r.2)) =
      walk n key nib nx (proof.data.toList.drop off)
  | 0, _, _, _, _ => rfl
  | n + 1, key, nib, nx, off => by
    have hn := nodeB_eq nx proof off
    simp only [walkB, walk]
    cases hB : nodeB nx proof off with
    | none =>
      rw [hB] at hn
      rw [← hn]
      rfl
    | some r =>
      obtain ⟨q, off'⟩ := r
      rw [hB] at hn
      rw [← hn]
      simp only [Option.map_some, stepB_eq]
      cases step key nib q.data.toList with
      | none => rfl
      | some st =>
        cases st with
        | found f => rfl
        | next nx' nib' => exact walkB_eq proof n key nib' nx' off'

theorem emptyProof_iff (proof : ByteArray) :
    (proof.size = 0 ∨ (proof.size = 1 ∧ byteAt proof 0 = 0x80)) ↔
      (proof.data.toList = [] ∨ proof.data.toList = [0x80]) := by
  rw [← size_eq, byteAt_eq]
  generalize proof.data.toList = l
  match l with
  | [] => simp
  | [b] => simp
  | _ :: _ :: _ => simp

theorem lookupB_eq (root key : Bytes) (proof : ByteArray) :
    lookupB root key proof = lookup root key proof.data.toList := by
  unfold lookupB lookup
  by_cases hk : maxKey < key.length
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]
    by_cases he : (proof.data.toList = [] ∨ proof.data.toList = [0x80]) ∧ root = emptyRoot
    · rw [if_pos he, if_pos ⟨(emptyProof_iff proof).mpr he.1, he.2⟩]
    · rw [if_neg he, if_neg (fun c => he ⟨(emptyProof_iff proof).mp c.1, c.2⟩)]
      have hw := walkB_eq proof (2 * key.length + 1) key 0 (.hashed root) 0
      rw [List.drop_zero] at hw
      rw [← hw]
      cases walkB proof (2 * key.length + 1) key 0 (.hashed root) 0 with
      | none => rfl
      | some r =>
        obtain ⟨f, off⟩ := r
        simp only [Option.map_some, List.drop_eq_nil_iff, size_eq]

theorem accountOfB_eq (v : ByteArray) : accountOfB v = accountOf v.data.toList := by
  have hp : payloadOfB v = payloadOf v.data.toList := funext (payloadOfB_eq v)
  simp only [accountOfB, accountOf, itemAtB_eq, itemsAtB_eq, hp, size_eq]

theorem slotOfB_eq (v : ByteArray) : slotOfB v = slotOf v.data.toList := by
  have hp : payloadOfB v = payloadOf v.data.toList := funext (payloadOfB_eq v)
  simp only [slotOfB, slotOf, itemAtB_eq, hp, size_eq]

theorem accountB_eq (root address : Bytes) (proof : ByteArray) :
    accountB root address proof = account root address proof.data.toList := by
  simp only [accountB, account, lookupB_eq]
  cases lookup root (keccak address) proof.data.toList with
  | none => rfl
  | some f =>
    cases f with
    | absent => rfl
    | value v => exact accountOfB_eq ⟨v.toArray⟩

theorem storageB_eq (root slot : Bytes) (proof : ByteArray) :
    storageB root slot proof = storage root slot proof.data.toList := by
  simp only [storageB, storage, lookupB_eq]
  cases lookup root (keccak slot) proof.data.toList with
  | none => rfl
  | some f =>
    cases f with
    | absent => rfl
    | value v => exact slotOfB_eq ⟨v.toArray⟩

end LeanLight.Spec.Mpt
