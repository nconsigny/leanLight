import LeanLightEvmProofs.Facts
import EthLib.Execution.Proofs.State.Agreement

/-!
# What the checks after the run establish

`checkRun`'s findings, once complete (`Findings.complete`) and with no deployment candidate
proved to hold storage (`Findings.nonEmpty = []`), say for every account and slot the run
accessed what the agreement needs: R1 (a fact for each accessed account), R2 (each accessed
slot fixed by the facts), R3 (an accessed deployment candidate's storage root is the empty
root) and R4 (the code of each accessed account held), and R5 (each `BLOCKHASH` within the
window asked for a hash among those held).
-/

namespace LeanLightEvmProofs

open LeanLightEvm
open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.Transactions (CallOutput)

/-! ## The accessed accounts and slots -/

theorem mem_accessedAccounts {r : Request} {o : CallOutput} {a : Address} :
    a ∈ accessedAccounts r o ↔
      a = r.sender ∨ r.to = some a ∨ a ∈ o.state.accountReads ∨ a ∈ o.state.accountWrites := by
  unfold accessedAccounts
  dsimp only
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Maps.mem_foldl_insert Prod.fst,
    Std.ExtTreeSet.foldl_eq_foldl_toList, Maps.mem_foldl_insert_id]
  have hw : (∃ d, d ∈ o.state.accountWrites.toList ∧ d.fst = a) ↔ a ∈ o.state.accountWrites := by
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
    constructor
    · rintro ⟨⟨b, v⟩, hp, rfl⟩
      rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp]
      rfl
    · intro h
      cases hv : o.state.accountWrites[a]? with
      | none => rw [hv] at h; cases h
      | some v => exact ⟨(a, v), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hv, rfl⟩
  rw [hw, Std.ExtTreeSet.mem_toList]
  cases hto : r.to with
  | none =>
    simp only [Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq, Std.ExtTreeSet.not_mem_empty,
      or_false, reduceCtorEq, false_or]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h.symm
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inl h.symm)
      · exact .inl (.inr h)
      · exact .inr h
  | some b =>
    simp only [Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq, Std.ExtTreeSet.not_mem_empty,
      or_false, Option.some.injEq]
    constructor
    · rintro (((h | h) | h) | h)
      · exact .inr (.inl h)
      · exact .inl h.symm
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    · rintro (h | h | h | h)
      · exact .inl (.inl (.inr h.symm))
      · exact .inl (.inl (.inl h))
      · exact .inl (.inr h)
      · exact .inr h

/-- The step of `accessedSlots`' fold over the written slots. -/
private def slotStep (m : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (p : Address × Std.ExtTreeMap Bytes32 U256) : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32) :=
  m.insert p.1 (p.2.foldl (fun s k _ => s.insert k) (m.getD p.1 ∅))

private theorem getD_slotStep_mono {m : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)}
    {p : Address × Std.ExtTreeMap Bytes32 U256} {x : Address} {k : Bytes32}
    (h : k ∈ m.getD x ∅) : k ∈ (slotStep m p).getD x ∅ := by
  unfold slotStep
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getElem?_insert]
  split
  · rename_i he
    rw [Std.compare_eq_iff_eq] at he
    subst he
    simp only [Option.getD_some]
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Maps.mem_foldl_insert Prod.fst]
    exact .inl h
  · rw [← Std.ExtTreeMap.getD_eq_getD_getElem?]
    exact h

private theorem getD_foldl_slotStep_mono {x : Address} {k : Bytes32} :
    ∀ (L : List (Address × Std.ExtTreeMap Bytes32 U256))
      (m : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)),
      k ∈ m.getD x ∅ → k ∈ (L.foldl slotStep m).getD x ∅
  | [], _, h => h
  | _ :: t, _, h => getD_foldl_slotStep_mono t _ (getD_slotStep_mono h)

private theorem getD_foldl_slotStep_hit {x : Address} {k : Bytes32}
    {slots : Std.ExtTreeMap Bytes32 U256 compare} (hk : slots[k]?.isSome = true)
    (L : List (Address × Std.ExtTreeMap Bytes32 U256 compare))
    (m : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) (h : (x, slots) ∈ L) :
    k ∈ (L.foldl slotStep m).getD x ∅ := by
  induction L generalizing m with
  | nil => exact absurd h List.not_mem_nil
  | cons p t ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with e | e
    · subst e
      refine getD_foldl_slotStep_mono t _ ?_
      unfold slotStep
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?, Maps.getElem?_insert_self]
      simp only [Option.getD_some]
      rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Maps.mem_foldl_insert Prod.fst]
      cases hv : slots[k]? with
      | none => rw [hv] at hk; cases hk
      | some v => exact .inr ⟨(k, v), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hv, rfl⟩
    · exact ih _ e

/-- Every slot the run read or wrote is among `accessedSlots`. -/
theorem mem_accessedSlots {o : CallOutput} {a : Address} {k : Bytes32}
    (h : TransactionState.accessedSlot o.state a k) :
    ∃ keys, (accessedSlots o)[a]? = some keys ∧ k ∈ keys := by
  have hmem : k ∈ (accessedSlots o).getD a ∅ := by
    unfold accessedSlots
    dsimp only
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    show k ∈ (o.state.storageWrites.toList.foldl slotStep o.state.storageReads).getD a ∅
    rcases h with h | h
    · exact getD_foldl_slotStep_mono _ _ h
    · unfold StorageMap.slot at h
      cases hs : o.state.storageWrites[a]? with
      | none => rw [hs] at h; cases h
      | some slots =>
        rw [hs] at h
        exact getD_foldl_slotStep_hit h _ _
          (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hs)
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?] at hmem
  cases hv : (accessedSlots o)[a]? with
  | none => rw [hv] at hmem; simp at hmem
  | some keys => rw [hv] at hmem; exact ⟨keys, rfl, hmem⟩

/-! ## The findings -/

/-- Findings that make `call` ask for something or refuse: any of R1 to R4 found something. -/
def Flagged (fd : Findings) : Prop :=
  fd.accounts.isEmpty = false ∨ fd.code ≠ [] ∨ fd.roots ≠ [] ∨ fd.nonEmpty ≠ [] ∨
    fd.slots.isEmpty = false

/-- What one accessed account must satisfy for its step of `checkRun` to flag nothing: it has a
fact (R1); if present, its code is held unless empty (R4), and if a deployment candidate, its
storage root is the empty root (R3). -/
def AccountChecked (f : Facts) (a : Address) : Prop :=
  ∃ fact, f.accounts[a]? = some fact ∧
    ∀ nonce balance codeHash root, fact = .present nonce balance codeHash root →
      (codeHash ≠ EMPTY_CODE_HASH → f.code.contains codeHash = true) ∧
      (nonce = 0 → codeHash = EMPTY_CODE_HASH → root = some EMPTY_STORAGE_ROOT)

theorem checkRun_ancestors (f : Facts) (h : Header) (anc : Option (List Hash32)) (r : Request)
    (o : CallOutput) (notes : Notes) :
    (checkRun f h anc r o notes).ancestors =
      notes.blockNumbers.toList.any fun b => decide ((blockHashes h anc).length < h.number - b) := by
  unfold checkRun
  simp only [Id.run, bind, pure]
  refine Loops.forIn_id_keep (fun s : Findings => s.ancestors = _) _ ?_ ?_ _ _ ?_
  · intro x b b' hb hf
    cases hb
    refine Loops.forIn_id_keep (fun s : Findings => s.ancestors = _) _ ?_ ?_ _ _ hf
    · intro k c c' hc hf'
      try dsimp only at hc
      split at hc <;> cases hc <;> exact hf'
    · intro k c
      try dsimp only
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  · intro x b
    exact ⟨_, rfl⟩
  · refine Loops.forIn_id_keep (fun s : Findings => s.ancestors = _) _ ?_ ?_ _ _ rfl
    · intro a b b' hb hf
      try dsimp only at hb
      split at hb
      · cases hb; exact hf
      · cases hb; exact hf
      · repeat' (first | split at hb | (cases hb; exact hf))
    · intro a b
      try dsimp only
      repeat' (first | split | exact ⟨_, rfl⟩)

/-- Complete findings with no candidate proved to hold storage flag nothing. -/
theorem not_flagged {fd : Findings} (hc : fd.complete = true) (hn : fd.nonEmpty = []) :
    ¬ Flagged fd := by
  unfold Findings.complete at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hcode, hroots⟩, hacc⟩, hslots⟩, -⟩ := hc
  rintro (h | h | h | h | h)
  · rw [hacc] at h; cases h
  · exact h (List.isEmpty_iff.mp hcode)
  · exact h (List.isEmpty_iff.mp hroots)
  · exact h hn
  · rw [hslots] at h; cases h

/-- Findings whose every field holds at least what another's does are flagged when it is. -/
theorem Flagged.mono {fd fd' : Findings} (hf : Flagged fd)
    (h1 : fd.accounts.isEmpty = false → fd'.accounts.isEmpty = false)
    (h2 : fd.code ≠ [] → fd'.code ≠ []) (h3 : fd.roots ≠ [] → fd'.roots ≠ [])
    (h4 : fd.nonEmpty ≠ [] → fd'.nonEmpty ≠ [])
    (h5 : fd.slots.isEmpty = false → fd'.slots.isEmpty = false) : Flagged fd' := by
  rcases hf with h | h | h | h | h
  · exact .inl (h1 h)
  · exact .inr (.inl (h2 h))
  · exact .inr (.inr (.inl (h3 h)))
  · exact .inr (.inr (.inr (.inl (h4 h))))
  · exact .inr (.inr (.inr (.inr (h5 h))))

/-- The inner loop of `checkRun`'s second loop keeps a flag. -/
private theorem flagged_keep_slots (f : Facts) (a : Address) (keys : List Bytes32)
    (init : Findings) (h : Flagged init) :
    Flagged (forIn (m := Id) keys init fun k (s : Findings) =>
      if (!f.slotKnown a k) = true then
        ForInStep.yield { s with slots := s.slots.insert a ((s.slots.getD a ∅).insert k) }
      else ForInStep.yield s).run := by
  refine Loops.forIn_id_keep Flagged _ ?_ ?_ keys init h
  · intro k b b' hb hf
    split at hb <;> cases hb
    · rcases hf with h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (Maps.isEmpty_insert_map _ _ _))))
    · exact hf
  · intro k b
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- An accessed account that fails R1, R3 or R4 flags `checkRun`'s findings. -/
theorem checkRun_flagged_account {f : Facts} {h : Header} {anc : Option (List Hash32)}
    {r : Request} {o : CallOutput} {notes : Notes} {a : Address}
    (ha : a ∈ accessedAccounts r o) (hbad : ¬ AccountChecked f a) :
    Flagged (checkRun f h anc r o notes) := by
  unfold checkRun
  simp only [Id.run, bind, pure]
  refine Loops.forIn_id_keep Flagged _ ?_ ?_ _ _ ?_
  · intro x b b' hb hf
    cases hb
    exact flagged_keep_slots f x.1 x.2.toList b hf
  · intro x b
    exact ⟨_, rfl⟩
  refine Loops.forIn_id_flag Flagged _ ?_ ?_ (a₀ := a) ?_ _ _ (Std.ExtTreeSet.mem_toList.mpr ha)
  · intro x b b' hb hf
    try dsimp only at hb
    repeat' (first | split at hb | (cases hb; (refine Flagged.mono hf ?_ ?_ ?_ ?_ ?_ <;> intro hh <;>
      first | exact hh | exact List.cons_ne_nil _ _ | exact Maps.isEmpty_insert_set _ _)))
  · intro x b
    try dsimp only
    repeat' (first | split | exact ⟨_, rfl⟩)
  · intro b b' hb
    try dsimp only at hb
    unfold AccountChecked at hbad
    split at hb
    · cases hb
      exact .inl (Maps.isEmpty_insert_set _ _)
    · rename_i hacc
      exact absurd ⟨_, hacc, fun _ _ _ _ e => by cases e⟩ hbad
    · rename_i nonce balance codeHash root hacc
      have hbad' : ¬ ((codeHash ≠ EMPTY_CODE_HASH → f.code.contains codeHash = true) ∧
          (nonce = 0 → codeHash = EMPTY_CODE_HASH → root = some EMPTY_STORAGE_ROOT)) :=
        fun hok => hbad ⟨_, hacc, fun n b c rt e => by cases e; exact hok⟩
      by_cases hcode : codeHash ≠ EMPTY_CODE_HASH ∧ f.code.contains codeHash = false
      · have hc : (codeHash != EMPTY_CODE_HASH && !f.code.contains codeHash) = true := by
          simp [hcode.1, hcode.2]
        simp only [hc, ↓reduceIte] at hb
        repeat' (first | split at hb | (cases hb; exact .inr (.inl (List.cons_ne_nil _ _))))
      · have hcand : nonce = 0 ∧ codeHash = EMPTY_CODE_HASH ∧ root ≠ some EMPTY_STORAGE_ROOT := by
          refine Classical.byContradiction fun hn => hbad' ⟨fun hne => ?_, fun h0 he => ?_⟩
          · cases hk : f.code.contains codeHash
            · exact absurd ⟨hne, hk⟩ hcode
            · rfl
          · exact Classical.byContradiction fun hr => hn ⟨h0, he, hr⟩
        obtain ⟨h0, he, hr⟩ := hcand
        subst h0 he
        have hc : (EMPTY_CODE_HASH != EMPTY_CODE_HASH && !f.code.contains EMPTY_CODE_HASH) = false :=
          by simp
        have hc' : ((0 : Nat) == 0 && EMPTY_CODE_HASH == EMPTY_CODE_HASH) = true := by simp
        simp only [hc, hc', Bool.false_eq_true, ↓reduceIte] at hb
        split at hb
        · cases hb
          exact .inr (.inr (.inl (List.cons_ne_nil _ _)))
        · rename_i rt
          have hne : (rt != EMPTY_STORAGE_ROOT) = true := by
            simp only [bne_iff_ne, ne_eq]
            exact fun e => hr (by rw [e])
          simp only [hne, ↓reduceIte] at hb
          cases hb
          exact .inr (.inr (.inr (.inl (List.cons_ne_nil _ _))))

/-- An accessed slot the facts do not fix flags `checkRun`'s findings. -/
theorem checkRun_flagged_slot {f : Facts} {h : Header} {anc : Option (List Hash32)}
    {r : Request} {o : CallOutput} {notes : Notes} {a : Address} {keys : Std.ExtTreeSet Bytes32}
    {k : Bytes32} (hkeys : (accessedSlots o)[a]? = some keys) (hk : k ∈ keys)
    (hbad : f.slotKnown a k = false) :
    Flagged (checkRun f h anc r o notes) := by
  unfold checkRun
  simp only [Id.run, bind, pure]
  refine Loops.forIn_id_flag Flagged _ ?_ ?_ (a₀ := (a, keys)) ?_ _ _
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hkeys)
  · intro x b b' hb hf
    cases hb
    exact flagged_keep_slots f x.1 x.2.toList b hf
  · intro x b
    exact ⟨_, rfl⟩
  · intro b b' hb
    cases hb
    refine Loops.forIn_id_flag Flagged _ ?_ ?_ (a₀ := k) ?_ _ _ (Std.ExtTreeSet.mem_toList.mpr hk)
    · intro k' c c' hc hf
      split at hc <;> cases hc
      · exact Flagged.mono hf id id id id (fun _ => Maps.isEmpty_insert_map _ _ _)
      · exact hf
    · intro k' c
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · intro c c' hc
      have : (!f.slotKnown a k) = true := by simp [hbad]
      simp only [this, ↓reduceIte] at hc
      cases hc
      exact .inr (.inr (.inr (.inr (Maps.isEmpty_insert_map _ _ _))))

/-- What complete findings with no candidate proved to hold storage establish: R1, R3 and R4 for
every accessed account, R2 for every accessed slot, R5 for every `BLOCKHASH` noted. -/
theorem checkRun_sound {f : Facts} {h : Header} {anc : Option (List Hash32)}
    {r : Request} {o : CallOutput} {notes : Notes}
    (hc : (checkRun f h anc r o notes).complete = true)
    (hn : (checkRun f h anc r o notes).nonEmpty = []) :
    (∀ a ∈ accessedAccounts r o, AccountChecked f a) ∧
    (∀ a keys, (accessedSlots o)[a]? = some keys → ∀ k ∈ keys, f.slotKnown a k = true) ∧
    (∀ b ∈ notes.blockNumbers, h.number - b ≤ (blockHashes h anc).length) := by
  have hnot := not_flagged hc hn
  refine ⟨fun a ha => Classical.byContradiction fun hbad =>
      hnot (checkRun_flagged_account ha hbad), fun a keys hkeys k hk => ?_, fun b hb => ?_⟩
  · cases hs : f.slotKnown a k
    · exact absurd (checkRun_flagged_slot hkeys hk hs) hnot
    · rfl
  · unfold Findings.complete at hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hanc := hc.2
    rw [checkRun_ancestors] at hanc
    simp only [List.any_eq_false, decide_eq_true_eq, Std.ExtTreeSet.mem_toList] at hanc
    exact Nat.le_of_not_lt (hanc b hb)

end LeanLightEvmProofs
