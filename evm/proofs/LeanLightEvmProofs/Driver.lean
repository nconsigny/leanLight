import LeanLightEvmProofs.Hashes.Suffice
import LeanLightProofs.Driver
import LeanLightProofs.History
import LeanLightEvm.Driver

/-!
# The checked call at the light client's anchor: what an answer of the driver means

`LeanLightEvm.Driver.run` reads its input from fetched bytes through leanLight's readers, then
runs `LeanLightEvm.call`. This module composes what leanLight proves about those readers and its
store with `call_agrees`:

* `factsAt_holdIn`: the facts `Driver.factsAt` reads under a state root hold in every EthLib
  state `F` that `Represents` the world state `S` (with storage `stor`) whose trie has that root,
  unless Keccak-256 collides on byte strings the statement names (`Collision`).
* `inputAt_agrees`: so an answer `call` gives on `Driver.inputAt`'s input is the plain run's on
  every such `F` (`reference`), and a refusal the plain run's refusal, under the hypotheses of
  `CallAgrees` that are about `F` alone (`StorageAtAccounts`, `CodesAvailable`) and the chain's
  ancestors (`AncestorsOf`), or a named collision.
* `run_agrees`: an answer `Driver.run` returns was given at the store's anchor (`Store.anchored`),
  under the EL header `Anchor.bind` keeps for it, and is the plain run's on every state that
  represents the world state with that header's state root, or a named collision;
  `reaches_run_agrees` adds what leanLight proves of every store its client reaches
  (`LeanLight.Lc.Driver.AnchorProved`: the anchor signed by two thirds of a committee carried by
  signed branches from the checkpoint, fresh, and the header bound by `Anchor.bind_spec`).

The two models of one state: `F`, EthLib's (`State`: accounts, storage and code in tree maps), is
what the EVM runs on; `S` and `stor`, the Yellow Paper's world state as leanLight's trie
specification has it (`Spec.Mpt.Trie`: accounts at addresses, each address's storage), are what a
state root commits to. `Represents F S stor` says they are one state (its fields).
-/

namespace LeanLightEvmProofs.Driver

open LeanLight
open LeanLight.Lc
open LeanLightEvm
open LeanLightEvm.Driver
open EthLib.Base
open EthLib.Execution.State

/-! ## Two constants, both hashes -/

/-- EthLib's empty storage root is leanLight's (two Keccak-256 implementations of `0x80`). -/
theorem emptyStorageRoot_toList : EMPTY_STORAGE_ROOT.toList = Spec.Mpt.emptyRoot := by
  decide +kernel

/-- EthLib's empty code hash is leanLight's (two Keccak-256 implementations of no bytes). -/
theorem emptyCodeHash_toList : EMPTY_CODE_HASH.toList = Spec.Mpt.emptyCode := by
  decide +kernel

/-! ## The two models of a state -/

/-- `F` (EthLib's state) and `S`, `stor` (the world state of leanLight's trie specification) are
one state:

- `accounts`: the account `S` holds at each address is `F`'s, with the storage root of
  `stor a`, or the empty account where `F` has none;
- `storage`: `stor a` holds `F`'s words at `a`;
- `storageOk`, `valid`: the storages and the accounts are as a trie holds them (nonzero words
  below 2^256; nonces and balances below 2^256, 32-byte hashes);
- `code`: `F` holds code under its own Keccak-256 (EthLib's);
- `noEmpty`: `F` holds no empty account (EIP-161's: nonce 0, balance 0, no code), as no state has
  from Spurious Dragon's clearing on, and as EIP-7523 makes a rule past the Merge. -/
structure Represents (F : State) (S : Spec.Mpt.Trie.State)
    (stor : Address → Spec.Mpt.Trie.Storage) : Prop where
  accounts : ∀ a : Address, Spec.Mpt.Trie.accountAt S a.toList =
    match F.accounts[a]? with
    | none => Spec.Mpt.emptyAccount
    | some acc => ⟨acc.nonce, acc.balance.toNat, Spec.Mpt.Trie.storageRoot (stor a),
        acc.codeHash.toList⟩
  storage : ∀ (a : Address) (k : Bytes32),
    (F.getStorage a k).toNat = Spec.Mpt.Trie.slotAt (stor a) k.toList
  storageOk : ∀ a, Spec.Mpt.Trie.StorageOk (stor a)
  valid : ∀ p ∈ S, Spec.Mpt.Trie.AccountValid p.2
  code : ∀ (h : Hash32) (c : ByteArray), F.code[h]? = some c →
    EthLib.Cryptography.Hash.Keccak.keccak256 c = h
  noEmpty : ∀ (a : Address) (acc : Account), F.accounts[a]? = some acc →
    acc.nonce ≠ 0 ∨ acc.balance ≠ 0 ∨ acc.codeHash ≠ EMPTY_CODE_HASH

/-- `Represents` can hold: the empty state is represented by the empty world state, so the
theorems below are not about an empty set of states. -/
theorem represents_empty :
    Represents { accounts := ∅, storage := ∅, code := ∅ } [] (fun _ => []) where
  accounts a := by simp [Spec.Mpt.Trie.accountAt]
  storage a k := by
    simp [State.getStorage, StorageMap.slot, Spec.Mpt.Trie.slotAt]
  storageOk a := by simp [Spec.Mpt.Trie.StorageOk]
  valid p hp := by simp at hp
  code h c hc := by simp at hc
  noEmpty a acc h := by simp at h

/-- The Keccak-256 collisions that could make a fetched proof or code disagree with the state:
each disjunct names two byte strings, built from the fetched bytes `fx` and the honest tries of
`S` and `stor`, that are different and hash alike. None holds unless Keccak-256 (leanLight's, or
EthLib's for code) has a collision on exactly those bytes.

- an account's proof against the honest one (`Spec.Mpt.collision`), or two addresses of `S` with
  one Keccak-256 (`Spec.Mpt.Trie.clash`);
- a slot's proof against the honest one, or two slots with one Keccak-256;
- for an account whose storage root is the empty trie's, the empty proof against the honest proof
  of any slot of `stor a`, or two of its slots with one Keccak-256;
- fetched code against the code `F` holds under the same hash. -/
def Collision (F : State) (S : Spec.Mpt.Trie.State) (stor : Address → Spec.Mpt.Trie.Storage)
    (fx : Fetched) : Prop :=
  (∃ p ∈ fx.accounts,
    Spec.Mpt.IsCollision (Spec.Mpt.Trie.clash S p.address.toList) ∨
    Spec.Mpt.IsCollision (Spec.Mpt.collision (Spec.Mpt.Trie.stateRoot S)
      (Spec.Common.keccak p.address.toList) p.nodes.data.toList
      (Spec.Mpt.Trie.accountProof S p.address.toList))) ∨
  (∃ p ∈ fx.accounts, ∃ q ∈ p.slots,
    Spec.Mpt.IsCollision (Spec.Mpt.Trie.clash (stor p.address) q.1.toList) ∨
    Spec.Mpt.IsCollision (Spec.Mpt.collision (Spec.Mpt.Trie.storageRoot (stor p.address))
      (Spec.Common.keccak q.1.toList) q.2.data.toList
      (Spec.Mpt.Trie.storageProof (stor p.address) q.1.toList))) ∨
  (∃ p ∈ fx.accounts, ∃ k : Bytes32,
    Spec.Mpt.IsCollision (Spec.Mpt.Trie.clash (stor p.address) k.toList) ∨
    Spec.Mpt.IsCollision (Spec.Mpt.collision (Spec.Mpt.Trie.storageRoot (stor p.address))
      (Spec.Common.keccak k.toList) [] (Spec.Mpt.Trie.storageProof (stor p.address) k.toList))) ∨
  (∃ q ∈ fx.code, ∃ (h : Hash32) (c' : ByteArray),
    EthLib.Cryptography.Hash.Keccak.keccak256 q.2 = h ∧ F.code[h]? = some c' ∧ q.2 ≠ c' ∧
      EthLib.Cryptography.Hash.Keccak.keccak256 c' = h)

/-! ## What the readers read -/

/-- A proof's slots as `Facts.storageAt` takes them. -/
abbrev slotsOf (p : AccountProof) : List (List UInt8 × ByteArray) :=
  p.slots.map fun (k, nodes) => (k.toList, nodes)

/-- `p`, one of `ps`, is a proof of `a` that `Facts.storageAt` accepts under `root`, reading the
account `acct` and the words `vs`. -/
def Verified (root : List UInt8) (ps : List AccountProof) (a : Address)
    (acct : Spec.Mpt.Account) (vs : List Nat) (p : AccountProof) : Prop :=
  p ∈ ps ∧ p.address = a ∧ LeanLight.Lc.Facts.storageAt root a.toList p.nodes (slotsOf p) = some (acct, vs)

/-- Every account fact and every slot fact of `f` was read from a proof of `ps` that verified
under `root`: an account fact is `factOf` of the account read; a slot fact is one of the words
read with it, of an account that is not absent. -/
structure FromProofs (root : List UInt8) (ps : List AccountProof) (f : Facts) : Prop where
  accounts : ∀ (a : Address) (fact : AccountFact), f.accounts[a]? = some fact →
    ∃ p acct vs, Verified root ps a acct vs p ∧ fact = factOf acct
  slots : ∀ (a : Address) (k : Bytes32) (v : U256), (f.slots.getD a ∅)[k]? = some v →
    ∃ p acct vs, Verified root ps a acct vs p ∧ factOf acct ≠ .absent ∧
      ∃ x, (k, x) ∈ (p.slots.map (·.1)).zip vs ∧ v = BitVec.ofNat 256 x

theorem fromProofs_empty (root : List UInt8) (ps : List AccountProof) :
    FromProofs root ps {} where
  accounts a fact h := by simp at h
  slots a k v h := by simp at h

/-- A fold of inserts over key-word pairs: a key's value comes from a pair, or was there. -/
theorem foldl_insert_slots (k : Bytes32) (v : U256) :
    ∀ (zs : List (Bytes32 × Nat)) (m : Std.ExtTreeMap Bytes32 U256),
      (zs.foldl (fun m (kv : Bytes32 × Nat) => m.insert kv.1 (BitVec.ofNat 256 kv.2)) m)[k]? = some v →
      (∃ x, (k, x) ∈ zs ∧ v = BitVec.ofNat 256 x) ∨ m[k]? = some v
  | [], _, h => .inr h
  | (k', x) :: zs, m, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insert_slots k v zs _ h with ⟨y, hy, rfl⟩ | h
    · exact .inl ⟨y, List.mem_cons_of_mem _ hy, rfl⟩
    · by_cases hk : k' = k
      · subst hk
        rw [Maps.getElem?_insert_self] at h
        cases h
        exact .inl ⟨x, List.mem_cons_self .., rfl⟩
      · rw [Maps.getElem?_insert_ne hk] at h
        exact .inr h

/-- `addRead` keeps `FromProofs` for a proof that verified. -/
theorem fromProofs_addRead {root : List UInt8} {ps : List AccountProof} {f : Facts}
    {p : AccountProof} {acct : Spec.Mpt.Account} {vs : List Nat} (hf : FromProofs root ps f)
    (hv : Verified root ps p.address acct vs p) :
    FromProofs root ps (addRead f p.address acct (p.slots.map (·.1)) vs) := by
  have hacc : ∀ (a : Address) (fact : AccountFact),
      (f.accounts.insert p.address (factOf acct))[a]? = some fact →
      ∃ p acct vs, Verified root ps a acct vs p ∧ fact = factOf acct := by
    intro a fact h
    by_cases ha : p.address = a
    · subst ha
      rw [Maps.getElem?_insert_self] at h
      cases h
      exact ⟨p, acct, vs, hv, rfl⟩
    · rw [Maps.getElem?_insert_ne ha] at h
      exact hf.accounts a fact h
  cases hfa : factOf acct with
  | absent =>
    have hval : addRead f p.address acct (p.slots.map (·.1)) vs =
        { f with accounts := f.accounts.insert p.address .absent } := by
      simp only [addRead, hfa]
    rw [hval]
    exact ⟨by rw [← hfa]; exact hacc, hf.slots⟩
  | present n bal ch r =>
    have hne : factOf acct ≠ .absent := by rw [hfa]; exact fun h => by cases h
    have hval : addRead f p.address acct (p.slots.map (·.1)) vs =
        { f with accounts := f.accounts.insert p.address (.present n bal ch r)
                 slots := if (p.slots.map (·.1)).isEmpty then f.slots else
                   f.slots.insert p.address (((p.slots.map (·.1)).zip vs).foldl
                     (fun m (kv : Bytes32 × Nat) => m.insert kv.1 (BitVec.ofNat 256 kv.2))
                     (f.slots.getD p.address ∅)) } := by
      simp only [addRead, hfa]
    rw [hval]
    refine ⟨by rw [← hfa]; exact hacc, ?_⟩
    intro a k v h
    dsimp only at h
    split at h
    · exact hf.slots a k v h
    · by_cases ha : p.address = a
      · subst ha
        rw [Std.ExtTreeMap.getD_insert_self] at h
        rcases foldl_insert_slots k v _ _ h with ⟨x, hx, rfl⟩ | h
        · exact ⟨p, acct, vs, hv, hne, x, hx, rfl⟩
        · exact hf.slots _ k v h
      · rw [Std.ExtTreeMap.getD_insert, ite_eq_right (by simpa using ha)] at h
        exact hf.slots a k v h

/-- `readAccounts` keeps `FromProofs` for proofs drawn from `ps`, and never changes the code. -/
theorem readAccounts_spec {root : List UInt8} {ps : List AccountProof} :
    ∀ (qs : List AccountProof) (f f' : Facts), (∀ q ∈ qs, q ∈ ps) → FromProofs root ps f →
      readAccounts root qs f = .ok f' → FromProofs root ps f' ∧ f'.code = f.code
  | [], f, f', _, hf, h => by
    simp only [readAccounts, Except.ok.injEq] at h
    subst h
    exact ⟨hf, rfl⟩
  | q :: qs, f, f', hq, hf, h => by
    simp only [readAccounts] at h
    split at h
    · cases h
    · rename_i acct vs hs
      have hv : Verified root ps q.address acct vs q := ⟨hq q (List.mem_cons_self ..), rfl, hs⟩
      obtain ⟨h1, h2⟩ := readAccounts_spec qs _ f' (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))
        (fromProofs_addRead hf hv) h
      refine ⟨h1, ?_⟩
      rw [h2]
      cases hfa : factOf acct <;> simp only [addRead, hfa]

/-- What `readCode` adds: code under the code hash of an account `proved` holds as present, for
fetched code given for that account, never under the empty code's hash; the accounts and slots
as they were. -/
theorem readCode_spec {proved : Facts} :
    ∀ (cs : List (Address × ByteArray)) (f f' : Facts), readCode proved cs f = .ok f' →
      f'.accounts = f.accounts ∧ f'.slots = f.slots ∧
      ∀ (h : Hash32) (c : ByteArray), f'.code[h]? = some c → f.code[h]? = some c ∨
        ∃ a, (a, c) ∈ cs ∧ h ≠ EMPTY_CODE_HASH ∧
          ∃ n b r, proved.accounts[a]? = some (.present n b h r)
  | [], f, f', h => by
    simp only [readCode, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, fun _ _ hc => .inl hc⟩
  | (a, code) :: cs, f, f', h => by
    simp only [readCode] at h
    split at h
    · rename_i n b ch r hpa
      split at h
      · split at h
        · obtain ⟨h1, h2, h3⟩ := readCode_spec cs f f' h
          refine ⟨h1, h2, fun h' c hc => ?_⟩
          rcases h3 h' c hc with hc | ⟨a', ha', hne, hp⟩
          · exact .inl hc
          · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hne, hp⟩
        · rename_i hne
          obtain ⟨h1, h2, h3⟩ := readCode_spec cs _ f' h
          refine ⟨h1, h2, fun h' c hc => ?_⟩
          rcases h3 h' c hc with hc | ⟨a', ha', hne', hp⟩
          · by_cases hh : ch = h'
            · subst hh
              rw [Maps.getElem?_insert_self] at hc
              cases hc
              exact .inr ⟨a, List.mem_cons_self .., by simpa using hne, n, b, r, hpa⟩
            · rw [Maps.getElem?_insert_ne hh] at hc
              exact .inl hc
          · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hne', hp⟩
      · cases h
    · cases h

/-- What `factsAt` reads: every account and slot fact from a fetched proof that verified under
`root` (`FromProofs`), and every code under the code hash of a present account it was fetched
for, never under the empty code's hash. -/
theorem factsAt_spec {root : List UInt8} {fx : Fetched} {f : Facts}
    (h : factsAt root fx = .ok f) :
    FromProofs root fx.accounts f ∧
      ∀ (h : Hash32) (c : ByteArray), f.code[h]? = some c →
        ∃ a, (a, c) ∈ fx.code ∧ h ≠ EMPTY_CODE_HASH ∧
          ∃ n b r, f.accounts[a]? = some (.present n b h r) := by
  unfold factsAt at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i proved hp
    obtain ⟨hfp, hcode⟩ := readAccounts_spec fx.accounts {} proved (fun _ h => h)
      (fromProofs_empty root fx.accounts) hp
    obtain ⟨h1, h2, h3⟩ := readCode_spec fx.code proved f h
    refine ⟨⟨fun a fact ha => hfp.accounts a fact (h1 ▸ ha),
      fun a k v hs => hfp.slots a k v (h2 ▸ hs)⟩, fun h' c hc => ?_⟩
    rcases h3 h' c hc with hc | ⟨a, ha, hne, hp⟩
    · rw [hcode] at hc
      simp at hc
    · exact ⟨a, ha, hne, h1 ▸ hp⟩

/-! ## Each fact, against the represented state -/

/-- Keccak-256 gives 32 bytes (`Spec.MptTrie`'s private `keccak_length`, its proof). -/
private theorem keccak_length (bs : List UInt8) : (Spec.Common.keccak bs).length = 32 := by
  have push : ∀ (g : Nat → UInt8) (l : List Nat) (acc : ByteArray),
      (l.foldl (fun b a => b.push (g a)) acc).size = acc.size + l.length := by
    intro g l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih, ByteArray.size_push, List.length_cons]
      omega
  simp only [Spec.Common.keccak, Spec.Keccak.keccak256, Spec.Keccak.squeeze]
  simp
  rw [push]
  rfl

/-- Under the empty trie's root, the empty proof reads every slot as zero. -/
theorem storage_emptyRoot (k : List UInt8) : Spec.Mpt.storage Spec.Mpt.emptyRoot k [] = some 0 := by
  unfold Spec.Mpt.storage
  rw [Spec.Mpt.lookup_empty (by simp [keccak_length, Spec.Mpt.maxKey]) (.inl rfl)]

theorem bytes32_toList (v : Vector UInt8 32) : bytes32 v.toList = v := by
  unfold bytes32 toVector
  rw [dite_eq_left (by simp)]
  rfl

theorem toList_of_bytes32 {l : List UInt8} (h : bytes32 l = EMPTY_STORAGE_ROOT) :
    l = EMPTY_STORAGE_ROOT.toList := by
  unfold bytes32 toVector at h
  split at h
  · rw [← h]; rfl
  · exfalso
    have hz : (Vector.replicate 32 (0 : UInt8)) ≠ EMPTY_STORAGE_ROOT := by decide +kernel
    exact hz h

/-- R0 on code: every code fact sits under its Keccak-256 (EthLib's). -/
theorem check_code {f : Facts} (h : f.check = .ok ()) {hh : Hash32} {c : ByteArray}
    (hc : f.code[hh]? = some c) : EthLib.Cryptography.Hash.Keccak.keccak256 c = hh := by
  unfold Facts.check at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i u hcode
  have hall := Loops.forIn_except_ok _ (fun x => by
    obtain ⟨h', c'⟩ := x
    dsimp only
    split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl) f.code.toList hcode (hh, c)
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hc)
  dsimp only at hall
  split at hall
  · cases hall
  · rename_i hne
    have hb : (EthLib.Cryptography.Hash.Keccak.keccak256 c == hh) = true := by
      cases hq : (EthLib.Cryptography.Hash.Keccak.keccak256 c == hh)
      · simp [bne, hq] at hne
      · rfl
    exact eq_of_beq hb

variable {F : State} {S : Spec.Mpt.Trie.State} {stor : Address → Spec.Mpt.Trie.Storage}
  {fx : Fetched}

/-- An account a verified proof reads is the state's, short of a collision `Collision` names. -/
theorem account_read (hrep : Represents F S stor) (hnc : ¬ Collision F S stor fx) {a : Address}
    {p : AccountProof} {acct : Spec.Mpt.Account} {vs : List Nat}
    (hv : Verified (Spec.Mpt.Trie.stateRoot S) fx.accounts a acct vs p) :
    acct = Spec.Mpt.Trie.accountAt S a.toList := by
  obtain ⟨hp, rfl, hs⟩ := hv
  obtain ⟨ha, -⟩ := LeanLight.Lc.Facts.storageAt_spec hs
  rcases Spec.Mpt.Trie.account_sound hrep.valid ha with h | h | h
  · exact h
  · exact absurd (Or.inl ⟨p, hp, .inl h⟩) hnc
  · exact absurd (Or.inl ⟨p, hp, .inr h⟩) hnc

/-- What an account fact read from a verified proof says of `F`: absent, or `F`'s account. -/
theorem fact_holds (hrep : Represents F S stor) (hnc : ¬ Collision F S stor fx) {a : Address}
    {p : AccountProof} {acct : Spec.Mpt.Account} {vs : List Nat}
    (hv : Verified (Spec.Mpt.Trie.stateRoot S) fx.accounts a acct vs p) :
    match factOf acct with
    | .absent => F.accounts[a]? = none
    | .present n b ch _ => F.accounts[a]? = some ⟨n, b, ch⟩ := by
  have hacct := account_read hrep hnc hv
  rw [hrep.accounts a] at hacct
  cases hF : F.accounts[a]? with
  | none =>
    rw [hF] at hacct
    simp only at hacct
    subst hacct
    simp [factOf]
  | some acc =>
    rw [hF] at hacct
    simp only at hacct
    subst hacct
    by_cases he : (⟨acc.nonce, acc.balance.toNat, Spec.Mpt.Trie.storageRoot (stor a),
        acc.codeHash.toList⟩ : Spec.Mpt.Account) = Spec.Mpt.emptyAccount
    · exfalso
      simp only [Spec.Mpt.emptyAccount, Spec.Mpt.Account.mk.injEq] at he
      obtain ⟨hn, hb, -, hc⟩ := he
      rw [← emptyCodeHash_toList] at hc
      rcases hrep.noEmpty a acc hF with h | h | h
      · exact h hn
      · exact h (BitVec.eq_of_toNat_eq (by simpa using hb))
      · exact h (Vector.toList_inj.mp hc)
    · simp only [factOf, he, ↓reduceIte, bytes32_toList, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The words `Facts.storageAt` reads, slot by slot: each key read with its word comes from a
fetched slot proof that `Spec.Mpt.storage` accepts with that word under `root`. -/
theorem zip_storage {root : List UInt8} :
    ∀ (sl : List (Bytes32 × ByteArray)) (vs : List Nat),
      (sl.map fun (k, nodes) => (k.toList, nodes)).map
          (fun s => Spec.Mpt.storage root s.1 s.2.data.toList) = vs.map some →
      ∀ (k : Bytes32) (x : Nat), (k, x) ∈ (sl.map (·.1)).zip vs →
        ∃ nodes, (k, nodes) ∈ sl ∧ Spec.Mpt.storage root k.toList nodes.data.toList = some x
  | [], vs, h, k, x, hm => by simp at hm
  | (k0, n0) :: sl, [], h, k, x, hm => by simp at h
  | (k0, n0) :: sl, v0 :: vs, h, k, x, hm => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h0, h⟩ := h
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨n0, List.mem_cons_self .., h0⟩
    · obtain ⟨nodes, hn, hs⟩ := zip_storage sl vs h k x hm
      exact ⟨nodes, List.mem_cons_of_mem _ hn, hs⟩

/-- A slot fact read from a verified proof is `F`'s word, short of a collision `Collision`
names. -/
theorem slot_holds (hrep : Represents F S stor) (hnc : ¬ Collision F S stor fx) {a : Address}
    {p : AccountProof} {acct : Spec.Mpt.Account} {vs : List Nat}
    (hv : Verified (Spec.Mpt.Trie.stateRoot S) fx.accounts a acct vs p)
    (hne : factOf acct ≠ .absent) {k : Bytes32} {x : Nat}
    (hx : (k, x) ∈ (p.slots.map (·.1)).zip vs) : F.getStorage a k = BitVec.ofNat 256 x := by
  have hacct := account_read hrep hnc hv
  obtain ⟨hp, hpa, hs⟩ := hv
  obtain ⟨-, hmap⟩ := LeanLight.Lc.Facts.storageAt_spec hs
  obtain ⟨nodes, hn, hst⟩ := zip_storage p.slots vs hmap k x hx
  -- the account is present in `F` (its fact is not absent), with `stor a`'s root
  have hroot : acct.storageRoot = Spec.Mpt.Trie.storageRoot (stor a) := by
    rw [hrep.accounts a] at hacct
    cases hF : F.accounts[a]? with
    | none =>
      rw [hF] at hacct
      simp only at hacct
      subst hacct
      exact absurd (by simp [factOf]) hne
    | some acc =>
      rw [hF] at hacct
      simp only at hacct
      rw [hacct]
  rw [hroot] at hst
  subst hpa
  rcases Spec.Mpt.Trie.storage_sound (hrep.storageOk p.address) hst with h | h | h
  · apply BitVec.eq_of_toNat_eq
    rw [hrep.storage, ← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := BitVec.isLt (F.getStorage p.address k)
    rw [hrep.storage, ← h] at this
    exact this
  · exact absurd (Or.inr (Or.inl ⟨p, hp, (k, nodes), hn, .inl h⟩)) hnc
  · exact absurd (Or.inr (Or.inl ⟨p, hp, (k, nodes), hn, .inr h⟩)) hnc

/-- An account read with the empty storage root has no nonzero word in `F`, short of a
collision `Collision` names. -/
theorem emptyRoot_holds (hrep : Represents F S stor) (hnc : ¬ Collision F S stor fx) {a : Address}
    {p : AccountProof} {acct : Spec.Mpt.Account} {vs : List Nat}
    (hv : Verified (Spec.Mpt.Trie.stateRoot S) fx.accounts a acct vs p)
    (hne : factOf acct ≠ .absent) (hr : bytes32 acct.storageRoot = EMPTY_STORAGE_ROOT)
    (k : Bytes32) : F.getStorage a k = 0 := by
  have hacct := account_read hrep hnc hv
  obtain ⟨hp, hpa, -⟩ := hv
  have hroot : acct.storageRoot = Spec.Mpt.Trie.storageRoot (stor a) := by
    rw [hrep.accounts a] at hacct
    cases hF : F.accounts[a]? with
    | none =>
      rw [hF] at hacct
      simp only at hacct
      subst hacct
      exact absurd (by simp [factOf]) hne
    | some acc =>
      rw [hF] at hacct
      simp only at hacct
      rw [hacct]
  have hempty : Spec.Mpt.Trie.storageRoot (stor a) = Spec.Mpt.emptyRoot := by
    rw [← hroot, toList_of_bytes32 hr, emptyStorageRoot_toList]
  have hst := storage_emptyRoot k.toList
  rw [← hempty] at hst
  subst hpa
  rcases Spec.Mpt.Trie.storage_sound (hrep.storageOk p.address) hst with h | h | h
  · apply BitVec.eq_of_toNat_eq
    rw [hrep.storage, ← h]
    rfl
  · exact absurd (Or.inr (Or.inr (Or.inl ⟨p, hp, k, .inl h⟩))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inl ⟨p, hp, k, .inr h⟩))) hnc

/-- **The facts `factsAt` reads hold in every represented state**, short of a collision
`Collision` names: for `F` that `Represents` the world state `S` (with storage `stor`) whose
trie's root is the one read under, and that holds every account's code (`CodesAvailable`),
the facts of a fetch `fx` that `call`'s R0 accepted hold in `F` (`Facts.HoldIn`). -/
theorem factsAt_holdIn (hrep : Represents F S stor) (hcodes : CodesAvailable F) {f : Facts}
    (h : factsAt (Spec.Mpt.Trie.stateRoot S) fx = .ok f) (hcheck : f.check = .ok ()) :
    f.HoldIn F ∨ Collision F S stor fx := by
  by_cases hnc : Collision F S stor fx
  · exact .inr hnc
  refine .inl ?_
  obtain ⟨hfp, hcode⟩ := factsAt_spec h
  have hacc : ∀ (a : Address) (fact : AccountFact), f.accounts[a]? = some fact →
      match fact with
      | .absent => F.accounts[a]? = none
      | .present n b ch _ => F.accounts[a]? = some ⟨n, b, ch⟩ := by
    intro a fact ha
    obtain ⟨p, acct, vs, hv, rfl⟩ := hfp.accounts a fact ha
    exact fact_holds hrep hnc hv
  refine ⟨hacc, ?_, ?_, ?_⟩
  · intro a n b ch ha k
    obtain ⟨p, acct, vs, hv, hfa⟩ := hfp.accounts a _ ha
    have hne : factOf acct ≠ .absent := by rw [← hfa]; exact fun h => by cases h
    have hr : bytes32 acct.storageRoot = EMPTY_STORAGE_ROOT := by
      unfold factOf at hfa
      split at hfa
      · cases hfa
      · simp only [AccountFact.present.injEq, Option.some.injEq] at hfa
        exact hfa.2.2.2.symm
    exact emptyRoot_holds hrep hnc hv hne hr k
  · intro a k v hs
    obtain ⟨p, acct, vs, hv, hne, x, hx, rfl⟩ := hfp.slots a k v hs
    exact slot_holds hrep hnc hv hne hx
  · intro hh c hc
    have hkc := check_code hcheck hc
    obtain ⟨a, hac, hne, n, b, r, hpa⟩ := hcode hh c hc
    have hFa : F.accounts[a]? = some ⟨n, b, hh⟩ := hacc a _ hpa
    obtain ⟨code, hgc⟩ := hcodes a
    simp only [State.getAccountOptional, hFa, Option.getD_some] at hgc
    unfold State.getCode at hgc
    simp only [hne, ↓reduceIte] at hgc
    split at hgc
    · rename_i code' hcode'
      cases hgc
      have hkc' := hrep.code hh code hcode'
      by_cases hcc : c = code
      · rw [hcc]; exact hcode'
      · exact absurd (Or.inr (Or.inr (Or.inr ⟨(a, c), hac, hh, code, hkc, hcode', hcc, hkc'⟩))) hnc
    · cases hgc

/-! ## The ancestors -/

/-- What `ancestorsFrom` reads: one hash a slot proof, each block's hash as `History.blockHash`
reads it (the EIP-2935 history contract's account holding its code, and the block's slot a
nonzero word, under `stateRoot`; `LeanLight.Lc.History.blockHash_spec`). -/
theorem ancestorsFrom_spec {root : List UInt8} {ap : ByteArray} :
    ∀ (n : Nat) (sps : List ByteArray) (hs : List Hash32), ancestorsFrom root ap n sps = .ok hs →
      hs.length = sps.length ∧ ∀ (j : Nat) (hj : j < sps.length) (hh : j < hs.length),
        ∃ w, History.blockHash root ap sps[j] (n + j) = some w ∧ hs[j] = bytes32 w
  | n, [], hs, h => by
    simp only [ancestorsFrom, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  | n, sp :: sps, hs, h => by
    simp only [ancestorsFrom] at h
    split at h
    · rename_i w hw
      cases hr : ancestorsFrom root ap (n + 1) sps with
      | error e => simp [hr, Functor.map, Except.map] at h
      | ok hs' =>
        simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hj⟩ := ancestorsFrom_spec (n + 1) sps hs' hr
        refine ⟨by simp [hl], fun j hj1 hj2 => ?_⟩
        cases j with
        | zero => exact ⟨w, by simpa using hw, rfl⟩
        | succ j =>
          obtain ⟨w', hw', he⟩ := hj j (by simpa using hj1) (by simpa using hj2)
          exact ⟨w', by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw', by simpa using he⟩
    · cases h

/-! ## The call at the anchor -/

theorem check_of_answer {b : Budgets} {i : Input} {a : Answer} (h : call b i = .answer a) :
    i.facts.check = .ok () := by
  unfold call at h
  split at h
  · cases h
  · rename_i rules hr
    exact (checkInput_ok hr).2

theorem check_of_refused {b : Budgets} {i : Input} {r : Refusal} (h : call b i = .refused r) :
    i.facts.check = .ok () := by
  unfold call at h
  split at h
  · cases h
  · rename_i rules hr
    exact (checkInput_ok hr).2

/-- What `inputAt` builds: the facts `factsAt` reads under the header's state root, and the
ancestors `ancestorsOf` reads under it, or none without history proofs. -/
theorem inputAt_spec {c : LeanLight.Lc.Forks.Chain} {table : List ChainRules}
    {el : Spec.Header.Header} {fs : List (List UInt8)} {r : Request} {round : Nat} {i : Input}
    (h : inputAt c table el fs fx r round = .ok i) :
    factsAt el.stateRoot fx = .ok i.facts ∧ i.request = r ∧ i.table = table ∧
      i.chainId = c.chainId ∧ headerOf fs = some i.header ∧
      (match fx.history with
       | none => i.ancestors = none
       | some (ap, sps) => ∃ hs, ancestorsOf el.stateRoot el.number ap sps = .ok hs ∧
           i.ancestors = some hs) := by
  unfold inputAt at h
  cases hh : headerOf fs with
  | none => simp [hh, throw, throwThe, MonadExceptOf.throw] at h
  | some header =>
    cases hf : factsAt el.stateRoot fx with
    | error e => simp [hh, hf, bind, Except.bind] at h
    | ok facts =>
      cases hx : fx.history with
      | none =>
        simp only [hh, hf, hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some aps =>
        obtain ⟨ap, sps⟩ := aps
        cases ha : ancestorsOf el.stateRoot el.number ap sps with
        | error e =>
          simp [hh, hf, hx, ha, bind, Except.bind, Functor.map, Except.map] at h
        | ok hs =>
          simp only [hh, hf, hx, ha, bind, Except.bind, pure, Except.pure, Functor.map,
            Except.map, Except.ok.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl, rfl, rfl, hs, ha, rfl⟩

/-- **An answer or a refusal of `call` on `inputAt`'s input is the plain run's**, on every EthLib
state `F` that represents the world state `S` (storage `stor`) whose trie's root is the bound
header's state root, whose storage sits at existing accounts and which holds every account's
code, for the chain's ancestors `full` (`AncestorsOf`); or Keccak-256 collides on bytes
`Collision` names. -/
theorem inputAt_agrees {c : LeanLight.Lc.Forks.Chain} {table : List ChainRules}
    {el : Spec.Header.Header} {fs : List (List UInt8)} {r : Request} {round : Nat} {i : Input}
    (h : inputAt c table el fs fx r round = .ok i) (b : Budgets) (hrep : Represents F S stor)
    (hroot : Spec.Mpt.Trie.stateRoot S = el.stateRoot) (hstor : StorageAtAccounts F)
    (hcodes : CodesAvailable F) {full : List Hash32} (hanc : AncestorsOf i full) :
    ((∀ a, call b i = .answer a → reference b i full F = some (.ok a.result)) ∧
      (∀ r', call b i = .refused r' → reference b i full F = some (.error r'))) ∨
      Collision F S stor fx := by
  have hf := (inputAt_spec h).1
  rw [← hroot] at hf
  by_cases hnc : Collision F S stor fx
  · exact .inr hnc
  refine .inl ⟨fun a ha => ?_, fun r' hr => ?_⟩
  · have hhold := (factsAt_holdIn hrep hcodes hf (check_of_answer ha)).resolve_right hnc
    exact (call_agrees b i F full hstor hcodes hhold hanc).1 a ha
  · have hhold := (factsAt_holdIn hrep hcodes hf (check_of_refused hr)).resolve_right hnc
    exact (call_agrees b i F full hstor hcodes hhold hanc).2 r' hr

/-- **What a run of the driver means.** If `Driver.run` returns `ran`, then the store had an
anchor `anc` at the clock (`Store.anchored`), `Anchor.bind` keeps the fetched RLP as its EL header
`ran.el`, the outcome is `call`'s on `ran.input`, and an answer (a refusal) is the plain run's
answer (refusal) on every EthLib state `F` that represents the world state `S` whose trie's root
is that header's state root (`Represents`), whose storage sits at existing accounts and which
holds every account's code, for the chain's ancestors `full`; or Keccak-256 collides on bytes
`Collision` names. -/
theorem run_agrees {c : LeanLight.Lc.Forks.Chain} {s : Store.Store} {now : Nat} {rlp : ByteArray}
    {table : List ChainRules} {b : Budgets} {r : Request} {round : Nat} {ran : Ran}
    (h : run c s now rlp table b fx r round = .ok ran) :
    ∃ anc, Store.anchored c s now = some anc ∧ ran.beacon = anc.header ∧
      Anchor.bind c anc.header rlp = some ran.el ∧ ran.outcome = call b ran.input ∧
      ∀ (F : State) (S : Spec.Mpt.Trie.State) (stor : Address → Spec.Mpt.Trie.Storage)
        (full : List Hash32), Represents F S stor →
        Spec.Mpt.Trie.stateRoot S = ran.el.stateRoot → StorageAtAccounts F →
        CodesAvailable F → AncestorsOf ran.input full →
        ((∀ a, ran.outcome = .answer a → reference b ran.input full F = some (.ok a.result)) ∧
          (∀ r', ran.outcome = .refused r' → reference b ran.input full F = some (.error r'))) ∨
          Collision F S stor fx := by
  unfold run at h
  cases ha : Store.anchored c s now with
  | none => simp [ha, throw, throwThe, MonadExceptOf.throw] at h
  | some anc =>
    cases hb : Anchor.bind c anc.header rlp with
    | none => simp [ha, hb, throw, throwThe, MonadExceptOf.throw] at h
    | some el =>
      cases hfs : Anchor.fieldsB rlp with
      | none => simp [ha, hb, hfs, throw, throwThe, MonadExceptOf.throw] at h
      | some fs =>
        cases hi : inputAt c table el fs fx r round with
        | error e => simp [ha, hb, hfs, hi, bind, Except.bind] at h
        | ok i =>
          simp only [ha, hb, hfs, hi, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          refine ⟨anc, rfl, rfl, hb, rfl, ?_⟩
          intro F S stor full hrep hroot hstor hcodes hanc
          exact inputAt_agrees hi b hrep hroot hstor hcodes hanc

/-- The ancestors `ancestorsOf` holds: `min 256 number` hashes, the `j`-th the hash of block
`number - min 256 number + j` as `History.blockHash` reads it under `root` from the history
contract's proofs. -/
theorem ancestorsOf_spec {root : List UInt8} {number : Nat} {ap : ByteArray}
    {sps : List ByteArray} {hs : List Hash32} (h : ancestorsOf root number ap sps = .ok hs) :
    hs.length = min 256 number ∧ ∀ (j : Nat) (hj : j < sps.length) (hh : j < hs.length),
      ∃ w, History.blockHash root ap sps[j] (number - min 256 number + j) = some w ∧
        hs[j] = bytes32 w := by
  unfold ancestorsOf at h
  dsimp only at h
  split at h
  · rename_i hl
    obtain ⟨h1, h2⟩ := ancestorsFrom_spec _ sps hs h
    exact ⟨h1.trans hl, h2⟩
  · cases h

/-- The field list `Anchor.fieldsB` reads from an RLP that `Anchor.bind` keeps is the header's,
and the RLP hashes to the beacon header's execution block hash (`Anchor.bind_spec`, for the
field list `bind` itself reads). -/
theorem bind_fields {c : LeanLight.Lc.Forks.Chain} {b : Store.Header} {rlp : ByteArray}
    {h : Spec.Header.Header} {fs : List (List UInt8)} (hb : Anchor.bind c b rlp = some h)
    (hfs : Anchor.fieldsB rlp = some fs) :
    Spec.Header.ofFields fs = some h ∧
      Spec.Common.keccak rlp.data.toList = b.elHash.data.toList := by
  unfold Anchor.bind at hb
  split at hb
  · cases hb
  · rename_i h' hv
    rw [hfs] at hb
    simp only at hb
    split at hb
    · injection hb with hb
      subst hb
      rw [Spec.Header.verifyB_eq] at hv
      unfold Spec.Header.verify at hv
      split at hv
      · rename_i hk
        rw [Anchor.fieldsB_eq] at hfs
        rw [Anchor.decode_fieldsL, hfs, Option.bind_some] at hv
        exact ⟨hv, hk⟩
      · cases hv
    · cases hb

/-- **The checked call at a store the client reached** (`run_agrees`, with what leanLight proves
of the store, `LeanLight.Lc.Driver.reaches_anchored` and `Anchor.bind_spec`). If the store `s`
is reached from the checkpoint `root` (`Reaches`: one `Store.bootstrap` then `Store.receive`
steps, as `LeanLight.Lc.Driver.start` and `feed` give) and `Driver.run` returns `ran`, then:

- the anchor `anc` it ran at is `AnchorProved`: the store is not halted and fresh at the clock,
  and the anchor, the finalized header and the current committee are carried from `root` by
  signature checks that passed with at least two thirds of an authenticated committee (what a
  passed check means rests on leanLight's BLS hypotheses and `Committee.Consistent`, which this
  module does not import: `LeanLightProofs.Signers`);
- the EVM's header was read (`Driver.headerOf`) from the field list `fs` whose canonical RLP is
  the fetched `rlp`, whose Keccak-256 is the anchor's execution block hash, and `Anchor.bind`
  keeps `ran.el` (decoded from the same fields) for it;
- the outcome is `call`'s on `ran.input`, and an answer (a refusal) is the plain run's on every
  EthLib state `F` that represents the world state with `ran.el`'s state root (`run_agrees`), or
  Keccak-256 collides on bytes `Collision` names. -/
theorem reaches_run_agrees {c : LeanLight.Lc.Forks.Chain} {root : ByteArray} {s : Store.Store}
    {now : Nat} {rlp : ByteArray} {table : List ChainRules} {b : Budgets} {r : Request}
    {round : Nat} {ran : Ran} (hs : LeanLight.Lc.Driver.Reaches c root s)
    (h : run c s now rlp table b fx r round = .ok ran) :
    ∃ anc fs, LeanLight.Lc.Driver.AnchorProved c root s now anc ∧ ran.beacon = anc.header ∧
      Anchor.bind c anc.header rlp = some ran.el ∧
      Spec.Rlp.encodeTree (.branch (fs.map .leaf)) = some rlp.data.toList ∧
      Spec.Common.keccak rlp.data.toList = anc.header.elHash.data.toList ∧
      Spec.Header.ofFields fs = some ran.el ∧ headerOf fs = some ran.input.header ∧
      ran.outcome = call b ran.input ∧
      ∀ (F : State) (S : Spec.Mpt.Trie.State) (stor : Address → Spec.Mpt.Trie.Storage)
        (full : List Hash32), Represents F S stor →
        Spec.Mpt.Trie.stateRoot S = ran.el.stateRoot → StorageAtAccounts F →
        CodesAvailable F → AncestorsOf ran.input full →
        ((∀ a, ran.outcome = .answer a → reference b ran.input full F = some (.ok a.result)) ∧
          (∀ r', ran.outcome = .refused r' → reference b ran.input full F = some (.error r'))) ∨
          Collision F S stor fx := by
  obtain ⟨anc, ha, hbeacon, hb, hout, hagree⟩ := run_agrees h
  -- the field list `run` read, the same `Anchor.bind` hashed
  unfold run at h
  simp only [ha, hb] at h
  cases hfs : Anchor.fieldsB rlp with
  | none => simp [hfs, throw, throwThe, MonadExceptOf.throw] at h
  | some fs =>
    cases hi : inputAt c table ran.el fs fx r round with
    | error e => simp [hfs, hi, bind, Except.bind] at h
    | ok i =>
      simp only [hfs, hi, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      have hin : ran.input = i := by rw [← h]
      obtain ⟨hof, hk⟩ := bind_fields hb hfs
      have henc : Spec.Rlp.encodeTree (.branch (fs.map .leaf)) = some rlp.data.toList :=
        Anchor.fieldsL_encode (by rw [← Anchor.fieldsB_eq]; exact hfs)
      refine ⟨anc, fs, LeanLight.Lc.Driver.reaches_anchored hs ha, hbeacon, hb, henc, hk, hof,
        hin ▸ (inputAt_spec hi).2.2.2.2.1, hout, hagree⟩

end LeanLightEvmProofs.Driver
