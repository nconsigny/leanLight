import LeanLightEvm.Call
import LeanLightEvmProofs.Maps
import LeanLightEvmProofs.Loops

/-!
# The facts as a state

What `Facts.toState` holds, key by key, and what `Facts.check` (R0) establishes about the facts.
-/

namespace LeanLightEvmProofs

open LeanLightEvm
open EthLib.Base
open EthLib.Execution.State

/-- The account `toState` holds at an address: the fact's, when it is present. -/
def factAccount : Option AccountFact → Option Account
  | some (.present nonce balance codeHash _) => some ⟨nonce, balance, codeHash⟩
  | _ => none

theorem accounts_toState (f : Facts) (a : Address) :
    f.toState.accounts[a]? = factAccount f.accounts[a]? := by
  unfold Facts.toState
  dsimp only
  rw [Maps.foldl_step _ (fun _ fact => factAccount (some fact)) _
    (fun _ _ fact => by cases fact <;> rfl)]
  cases f.accounts[a]? with
  | none => rfl
  | some fact => cases fact <;> rfl

/-- The nonzero slots of one account's slot facts, or none when it has none. -/
def nonzeroSlots (slots : Std.ExtTreeMap Bytes32 U256) : Option (Std.ExtTreeMap Bytes32 U256) :=
  let nonzero := slots.filter fun _ v => v != 0
  if nonzero.isEmpty then none else some nonzero

theorem storage_toState (f : Facts) (a : Address) :
    f.toState.storage[a]? = f.slots[a]?.bind nonzeroSlots := by
  unfold Facts.toState
  dsimp only
  rw [Maps.foldl_step _ (fun _ slots => nonzeroSlots slots) _ (fun _ _ slots => by
    unfold Maps.insertStep nonzeroSlots
    dsimp only
    split <;> rfl)]

/-- A key's value among the nonzero slots, read as a word, is its value among all of them. -/
theorem getD_nonzeroSlots (slots : Std.ExtTreeMap Bytes32 U256) (k : Bytes32) :
    ((nonzeroSlots slots).bind fun s => s[k]?).getD 0 = (slots[k]?).getD 0 := by
  have hf : (slots.filter fun _ v => v != 0)[k]? = slots[k]?.filter fun v => v != 0 := by
    rw [Std.ExtTreeMap.getElem?_filter]
    cases slots[k]? <;> simp [Option.pfilter, Option.filter]
  unfold nonzeroSlots
  dsimp only
  split
  · rename_i hempty
    rw [Std.ExtTreeMap.isEmpty_iff] at hempty
    have hk : (slots.filter fun _ v => v != 0)[k]? = none := by rw [hempty]; simp
    rw [hf] at hk
    cases hv : slots[k]? with
    | none => rfl
    | some v =>
      rw [hv] at hk
      simp only [Option.filter_some] at hk
      split at hk
      · cases hk
      · rename_i hz
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hz
        simp [hz]
  · simp only [Option.bind_some]
    rw [hf]
    cases hv : slots[k]? with
    | none => rfl
    | some v =>
      simp only [Option.filter_some]
      split
      · rfl
      · rename_i hz
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hz
        simp [hz]

/-- The word `toState` holds at a slot: the slot fact's, or 0. -/
theorem getStorage_toState (f : Facts) (a : Address) (k : Bytes32) :
    f.toState.getStorage a k = ((f.slots.getD a ∅)[k]?).getD 0 := by
  unfold State.getStorage StorageMap.slot
  rw [storage_toState, Std.ExtTreeMap.getD_eq_getD_getElem?]
  cases f.slots[a]? with
  | none => simp
  | some slots =>
    simp only [Option.bind_some, Option.getD_some]
    exact getD_nonzeroSlots slots k

theorem code_toState (f : Facts) : f.toState.code = f.code := rfl

/-- R0 on slots: every slot fact belongs to a present account, and none is nonzero under the
empty storage root. -/
theorem check_slots {f : Facts} (h : f.check = .ok ()) {a : Address}
    {slots : Std.ExtTreeMap Bytes32 U256} (hs : f.slots[a]? = some slots) :
    ∃ nonce balance codeHash root, f.accounts[a]? = some (.present nonce balance codeHash root) ∧
      (root = some EMPTY_STORAGE_ROOT → ∀ (k : Bytes32) (v : U256), slots[k]? = some v → v = 0) := by
  unfold Facts.check at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i u hcode
  split at h
  · cases h
  rename_i v hslots
  have hall := Loops.forIn_except_ok _ (fun x => by
    obtain ⟨a, slots⟩ := x
    dsimp only
    split
    · split
      · exact .inr ⟨_, rfl⟩
      · exact .inl rfl
    · exact .inr ⟨_, rfl⟩) f.slots.toList hslots (a, slots)
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hs)
  dsimp only at hall
  split at hall
  · rename_i nonce balance codeHash root hacc
    refine ⟨nonce, balance, codeHash, root, hacc, fun hroot (k : Bytes32) (v : U256) hk => ?_⟩
    split at hall
    · cases hall
    · rename_i hno
      subst hroot
      simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true, List.any_eq_false] at hno
      have := hno (k, v) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk)
      simpa using this
  · cases hall

end LeanLightEvmProofs
