import LeanLightEvmProofs.Checks

/-!
# The checks give agreement on what the run accessed

R0 (`Facts.check`) and the findings of complete checks (`checkRun_sound`) make the state built
from the facts, `S = Facts.toState f`, agree with every full state `F` the facts hold in, whose
storage sits at existing accounts, on four sets that the run's end state names: the accessed
accounts (with the sender and the recipient), the whole storage of the accessed deployment
candidates, the accessed slots, and the code of the accessed accounts. These are EthLib's
`AgreesOnTracker` sets (`Proofs/State/Agreement.lean`), with the sender and the recipient added.
-/

namespace LeanLightEvmProofs

open LeanLightEvm
open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.Transactions (CallOutput)

/-- The block a call runs on: a state with no write yet. -/
abbrev blockOf (S : State) : BlockState := ⟨S, ∅, ∅, ∅, ∅⟩

theorem getAccountOptional_blockOf (S : State) (a : Address) :
    (TransactionState.ofBlock (blockOf S)).getAccountOptional a = S.accounts[a]? := by
  simp [TransactionState.ofBlock, TransactionState.getAccountOptional, State.getAccountOptional]

theorem getAccount_blockOf (S : State) (a : Address) :
    (TransactionState.ofBlock (blockOf S)).getAccount a = (S.accounts[a]?).getD EMPTY_ACCOUNT := by
  simp [TransactionState.getAccount, getAccountOptional_blockOf]

theorem getStorage_blockOf (S : State) (a : Address) (k : Bytes32) :
    (TransactionState.ofBlock (blockOf S)).getStorage a k = S.getStorage a k := by
  simp [TransactionState.ofBlock, TransactionState.getStorage, StorageMap.slot]

theorem getCode_blockOf (S : State) (c : Hash32) :
    (TransactionState.ofBlock (blockOf S)).getCode c = S.getCode c := by
  unfold TransactionState.getCode
  by_cases h : c = EMPTY_CODE_HASH
  · simp [h, State.getCode]
  · simp [h, TransactionState.ofBlock]

/-- The sets the agreement is on, for the call `r` whose run ended in `o`, over the block `S`. -/
structure Sets (r : Request) (o : CallOutput) (S : State) where
  /-- Accounts accessed, the sender and the recipient included. -/
  account : Address → Prop := fun a => a ∈ accessedAccounts r o
  /-- Accessed accounts with nonce 0 and no code in `S`: deployment candidates. -/
  allStorage : Address → Prop := fun a => a ∈ accessedAccounts r o ∧
    ((TransactionState.ofBlock (blockOf S)).getAccount a).nonce = 0 ∧
    ((TransactionState.ofBlock (blockOf S)).getAccount a).codeHash = EMPTY_CODE_HASH
  /-- Accessed slots. -/
  slot : Address → Bytes32 → Prop := TransactionState.accessedSlot o.state
  /-- The code hashes, in `S`, of the accessed accounts. -/
  code : Hash32 → Prop := fun c => ∃ a, a ∈ accessedAccounts r o ∧
    ((TransactionState.ofBlock (blockOf S)).getAccount a).codeHash = c

/-- The sets, as `Sets`' defaults give them. -/
abbrev sets (r : Request) (o : CallOutput) (S : State) : Sets r o S := {}

/-- An address the facts say is absent has no storage in `S`, and none in `F`. -/
private theorem storage_absent {f : Facts} {F : State} (hcheck : f.check = .ok ())
    (hF : f.HoldIn F) (hstor : StorageAtAccounts F) {a : Address}
    (habs : f.accounts[a]? = some .absent) (k : Bytes32) :
    F.getStorage a k = 0 ∧ f.toState.getStorage a k = 0 := by
  refine ⟨Classical.byContradiction fun hne => ?_, ?_⟩
  · have := hstor a k hne
    rw [hF.accounts a .absent habs] at this
    cases this
  · rw [getStorage_toState, Std.ExtTreeMap.getD_eq_getD_getElem?]
    cases hs : f.slots[a]? with
    | none => simp
    | some slots =>
      obtain ⟨_, _, _, _, hacc, -⟩ := check_slots hcheck hs
      rw [habs] at hacc
      cases hacc

/-- An address whose proved storage root is the empty root has no storage in `S`, and none in
`F`. -/
private theorem storage_emptyRoot {f : Facts} {F : State} (hcheck : f.check = .ok ())
    (hF : f.HoldIn F) {a : Address} {nonce : Nat} {balance : U256} {codeHash : Hash32}
    (hpre : f.accounts[a]? = some (.present nonce balance codeHash (some EMPTY_STORAGE_ROOT)))
    (k : Bytes32) :
    F.getStorage a k = 0 ∧ f.toState.getStorage a k = 0 := by
  refine ⟨hF.emptyRoots a nonce balance codeHash hpre k, ?_⟩
  rw [getStorage_toState, Std.ExtTreeMap.getD_eq_getD_getElem?]
  cases hs : f.slots[a]? with
  | none => simp
  | some slots =>
    obtain ⟨_, _, _, root, hacc, hzero⟩ := check_slots hcheck hs
    rw [hpre] at hacc
    cases hacc
    simp only [Option.getD_some]
    cases hv : slots[k]? with
    | none => rfl
    | some v => exact hzero rfl k v hv

/-- A slot the facts fix has the same word in `S` and in `F`. -/
private theorem storage_known {f : Facts} {F : State} (hcheck : f.check = .ok ())
    (hF : f.HoldIn F) (hstor : StorageAtAccounts F) {a : Address} {k : Bytes32}
    (hk : f.slotKnown a k = true) : F.getStorage a k = f.toState.getStorage a k := by
  unfold Facts.slotKnown Facts.storageEmpty at hk
  rcases Bool.or_eq_true_iff.mp hk with he | hc
  · split at he
    · rename_i habs
      obtain ⟨h1, h2⟩ := storage_absent hcheck hF hstor habs k
      rw [h1, h2]
    · rename_i nonce balance codeHash root hpre
      have : root = EMPTY_STORAGE_ROOT := by simpa using he
      subst this
      obtain ⟨h1, h2⟩ := storage_emptyRoot hcheck hF hpre k
      rw [h1, h2]
    · cases he
  · rw [getStorage_toState]
    rw [Std.ExtTreeMap.contains_iff_mem, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hc
    cases hv : (f.slots.getD a ∅)[k]? with
    | none => rw [hv] at hc; cases hc
    | some v =>
      rw [hF.slots a k v hv]
      rfl

/-- **R0 to R4 give agreement.** For a run of `r` that ended in `o`, on the facts' state: if R0
holds, every accessed account passed R1, R3 and R4, and every accessed slot R2, then `S` and
every full state `F` the facts hold in, with storage only at existing accounts, agree on the
accessed accounts (with the sender and the recipient), the whole storage of the accessed
deployment candidates, the accessed slots and the code of the accessed accounts. -/
theorem agrees_of_checks {f : Facts} {F : State} {r : Request} {o : CallOutput}
    (hcheck : f.check = .ok ()) (hF : f.HoldIn F) (hstor : StorageAtAccounts F)
    (hacc : ∀ a ∈ accessedAccounts r o, AccountChecked f a)
    (hslots : ∀ a keys, (accessedSlots o)[a]? = some keys → ∀ k ∈ keys, f.slotKnown a k = true) :
    BlockState.AgreesOn (sets r o f.toState).account (sets r o f.toState).allStorage
      (sets r o f.toState).slot (sets r o f.toState).code (blockOf f.toState) (blockOf F) := by
  refine ⟨fun a ha => ?_, fun a k ha => ?_, fun a k ha => ?_, fun c hc => ?_⟩
  · -- accounts
    rw [getAccountOptional_blockOf, getAccountOptional_blockOf, accounts_toState]
    obtain ⟨fact, hfact, -⟩ := hacc a ha
    have := hF.accounts a fact hfact
    rw [hfact]
    cases fact with
    | absent => exact this
    | present => exact this
  · -- whole storage of candidates
    obtain ⟨ha, hnonce, hcode⟩ := ha
    rw [getStorage_blockOf, getStorage_blockOf]
    obtain ⟨fact, hfact, hgood⟩ := hacc a ha
    cases fact with
    | absent =>
      obtain ⟨h1, h2⟩ := storage_absent hcheck hF hstor hfact k
      rw [h1, h2]
    | present nonce balance codeHash root =>
      rw [getAccount_blockOf, accounts_toState, hfact] at hnonce hcode
      have hroot := (hgood _ _ _ _ rfl).2 hnonce hcode
      subst hroot
      obtain ⟨h1, h2⟩ := storage_emptyRoot hcheck hF hfact k
      rw [h1, h2]
  · -- accessed slots
    rw [getStorage_blockOf, getStorage_blockOf]
    obtain ⟨keys, hkeys, hk⟩ := mem_accessedSlots ha
    exact storage_known hcheck hF hstor (hslots a keys hkeys k hk)
  · -- code
    obtain ⟨a, ha, rfl⟩ := hc
    rw [getCode_blockOf, getCode_blockOf, getAccount_blockOf, accounts_toState]
    obtain ⟨fact, hfact, hgood⟩ := hacc a ha
    rw [hfact]
    cases fact with
    | absent =>
      show F.getCode EMPTY_CODE_HASH = f.toState.getCode EMPTY_CODE_HASH
      simp [State.getCode]
    | present nonce balance codeHash root =>
      show F.getCode codeHash = f.toState.getCode codeHash
      by_cases he : codeHash = EMPTY_CODE_HASH
      · simp [State.getCode, he]
      · have hc := (hgood _ _ _ _ rfl).1 he
        rw [Std.ExtTreeMap.contains_iff_mem, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hc
        cases hv : f.code[codeHash]? with
        | none => rw [hv] at hc; cases hc
        | some bytes =>
          unfold State.getCode
          rw [hF.code codeHash bytes hv, code_toState, hv]

end LeanLightEvmProofs
