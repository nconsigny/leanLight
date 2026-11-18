import Std.Data.ExtTreeMap
import Std.Data.ExtTreeSet

/-!
# Folds over `Std`'s tree maps and sets

`LeanLightEvm` builds maps and sets by folding inserts over other maps (`Facts.toState`,
`accessedAccounts`, `accessedSlots`). These lemmas say what such a fold holds, key by key, for
keys with a lawful order (`Address`, `Bytes32`: vectors of bytes).
-/

namespace LeanLightEvmProofs.Maps

open Std

variable {α : Type} [Ord α] [TransOrd α] [LawfulEqOrd α]

section Map

variable {β γ : Type}

/-- One step of a fold that, at each key, inserts what `g` gives, or nothing. -/
def insertStep (g : α → β → Option γ) (acc : ExtTreeMap α γ compare) (a : α) (b : β) :
    ExtTreeMap α γ compare :=
  match g a b with
  | some c => acc.insert a c
  | none => acc

/-- An insert at another key leaves a key's value. -/
theorem getElem?_insert_ne {m : ExtTreeMap α γ compare} {a x : α} {c : γ} (h : a ≠ x) :
    (m.insert a c)[x]? = m[x]? := by
  rw [ExtTreeMap.getElem?_insert]
  have : compare a x ≠ .eq := fun e => h (compare_eq_iff_eq.mp e)
  simp [this]

/-- An insert at a key gives that key its value. -/
theorem getElem?_insert_self {m : ExtTreeMap α γ compare} {a : α} {c : γ} :
    (m.insert a c)[a]? = some c := by
  rw [ExtTreeMap.getElem?_insert]
  simp

/-- A fold over pairs none of which has key `x` leaves `x`'s value. -/
theorem foldl_insertStep_other (g : α → β → Option γ) (x : α) :
    ∀ (L : List (α × β)) (acc : ExtTreeMap α γ compare), (∀ p ∈ L, p.1 ≠ x) →
      (L.foldl (fun acc p => insertStep g acc p.1 p.2) acc)[x]? = acc[x]?
  | [], _, _ => rfl
  | (a, b) :: t, acc, h => by
    rw [List.foldl_cons]
    rw [foldl_insertStep_other g x t _ (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    have hne : a ≠ x := h (a, b) (List.mem_cons_self ..)
    unfold insertStep
    split
    · exact getElem?_insert_ne hne
    · rfl

/-- A fold over pairs with distinct keys, one of them `(x, v)`, gives `x` what `g x v` gives,
from a start that holds nothing at `x`. -/
theorem foldl_insertStep_mem (g : α → β → Option γ) (x : α) (v : β) :
    ∀ (L : List (α × β)) (acc : ExtTreeMap α γ compare), L.Pairwise (fun p q => p.1 ≠ q.1) →
      (x, v) ∈ L → acc[x]? = none →
      (L.foldl (fun acc p => insertStep g acc p.1 p.2) acc)[x]? = g x v
  | [], _, _, hm, _ => absurd hm (List.not_mem_nil)
  | (a, b) :: t, acc, hp, hm, hacc => by
    rw [List.foldl_cons]
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hm with he | ht
    · cases he
      rw [foldl_insertStep_other g x t _ (fun p hq => fun e => hp.1 p hq e.symm)]
      unfold insertStep
      split
      · rename_i c hc
        rw [getElem?_insert_self, hc]
      · rename_i hc
        rw [hacc, hc]
    · have hne : a ≠ x := fun e => hp.1 (x, v) ht (by simp [e])
      refine foldl_insertStep_mem g x v t _ hp.2 ht ?_
      unfold insertStep
      split
      · rw [getElem?_insert_ne hne, hacc]
      · exact hacc

/-- The keys of a map's list are distinct. -/
theorem pairwise_toList (m : ExtTreeMap α β compare) :
    m.toList.Pairwise (fun p q => p.1 ≠ q.1) :=
  ExtTreeMap.distinct_keys_toList.imp fun h e => h (compare_eq_iff_eq.mpr e)

/-- A fold of `insertStep g` from the empty map holds, at each key, what `g` gives of the
key's value. -/
theorem foldl_insertStep (m : ExtTreeMap α β compare) (g : α → β → Option γ) (x : α) :
    (m.foldl (insertStep g) ∅)[x]? = m[x]?.bind (g x) := by
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  cases hx : m[x]? with
  | some v =>
    exact foldl_insertStep_mem g x v m.toList ∅ (pairwise_toList m)
      (ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hx) (by simp)
  | none =>
    rw [foldl_insertStep_other g x m.toList ∅]
    · simp
    · intro p hp e
      have := ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp
      rw [e, hx] at this
      cases this

omit [LawfulEqOrd α] in
/-- A map with an insert is not empty. -/
theorem isEmpty_insert_map (m : ExtTreeMap α γ compare) (a : α) (c : γ) :
    (m.insert a c).isEmpty = false := by
  rw [ExtTreeMap.isEmpty_eq_false_iff]
  intro h
  have : a ∈ m.insert a c := ExtTreeMap.mem_insert_self
  rw [h] at this
  exact ExtTreeMap.not_mem_empty this

/-- `foldl_insertStep` for a fold whose step is `insertStep g` written otherwise. -/
theorem foldl_step (m : ExtTreeMap α β compare) (g : α → β → Option γ)
    (step : ExtTreeMap α γ compare → α → β → ExtTreeMap α γ compare)
    (hstep : ∀ acc a b, step acc a b = insertStep g acc a b) (x : α) :
    (m.foldl step ∅)[x]? = m[x]?.bind (g x) := by
  have : step = insertStep g := funext fun acc => funext fun a => funext fun b => hstep acc a b
  subst this
  exact foldl_insertStep m g x

end Map

section Set

/-- What a fold of inserts adds to a set: its start, and each element inserted. -/
theorem mem_foldl_insert {δ : Type} (f : δ → α) :
    ∀ (L : List δ) (s : ExtTreeSet α compare) (x : α),
      x ∈ L.foldl (fun s d => s.insert (f d)) s ↔ x ∈ s ∨ ∃ d ∈ L, f d = x
  | [], s, x => by simp
  | d :: t, s, x => by
    rw [List.foldl_cons, mem_foldl_insert f t, ExtTreeSet.mem_insert, compare_eq_iff_eq]
    constructor
    · rintro ((h | h) | ⟨d', hd', h⟩)
      · exact .inr ⟨d, List.mem_cons_self .., h⟩
      · exact .inl h
      · exact .inr ⟨d', List.mem_cons_of_mem _ hd', h⟩
    · rintro (h | ⟨d', hd', h⟩)
      · exact .inl (.inr h)
      · rcases List.mem_cons.mp hd' with e | e
        · subst e
          exact .inl (.inl h)
        · exact .inr ⟨d', e, h⟩

omit [LawfulEqOrd α] in
/-- A set with an insert is not empty. -/
theorem isEmpty_insert_set (s : ExtTreeSet α compare) (a : α) : (s.insert a).isEmpty = false := by
  rw [ExtTreeSet.isEmpty_eq_false_iff]
  intro h
  have : a ∈ s.insert a := ExtTreeSet.mem_insert_self
  rw [h] at this
  exact ExtTreeSet.not_mem_empty this

/-- `mem_foldl_insert` for a fold that inserts the elements themselves. -/
theorem mem_foldl_insert_id (L : List α) (s : ExtTreeSet α compare) (x : α) :
    x ∈ L.foldl (fun s a => s.insert a) s ↔ x ∈ s ∨ x ∈ L := by
  rw [show (fun (s : ExtTreeSet α compare) (a : α) => s.insert a) =
    (fun s d => s.insert (id d)) from rfl, mem_foldl_insert id]
  simp

end Set

end LeanLightEvmProofs.Maps
