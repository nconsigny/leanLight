import LeanLight.Codec
import LeanLightProofs.Forks
import Mathlib.Data.Finset.Card

/-!
# The store: what an update can and cannot do (25d to 25i)

About `LeanLight.Store`, the code `lkd-lc` runs. Every theorem is about `receive`, the one way an
update enters a store, and `bootstrap`, the one way a store begins; `LeanLightProofs.Driver`
shows the driver reaches stores only through them.

**How `receive` decides** (`receive_cases`): an update leaves the store exactly as it was, or it
`Passed` every check before and including BLS (not halted, `formOk`, a committee held for its
signature period, the age bound, the signature) and `afterBls` decides the rest.

* **25d, domains and forks.** The signature is checked under the participants' aggregate key
  (their sum on a committee as the chain holds one, `LeanLightProofs.Signers`), the fork
  version at the epoch of `max(signature_slot, 1) − 1`, `compute_domain(DOMAIN_SYNC_COMMITTEE,
  version, genesis_validators_root)` and the signing root of the attested header's root
  (`verifySignature_iff`); bytes are decoded only as the fork their tag names, which must be the
  attested slot's (`decodeUpdate_fork`, `decodeBootstrap_fork`); a change of `signature_slot`
  within one period and one fork version changes neither `formOk`, nor the committee chosen,
  nor the signature check (`formOk_signatureSlot`, `verifySignature_signatureSlot`), and only
  `isBetter`'s last key (`rank_signatureSlot`).
* **25e, bootstrap** (`bootstrap_sound`): a store starts only from a header valid at its slot's
  fork whose root is the configured checkpoint, a committee proved by its branch at the fork's
  gindex under the header's state root, as many keys as the preset's committee (`ofSync_keys`), and a
  checkpoint younger than `MAX_AGE`; it starts with nothing anchored and no next committee.
* **25f, acceptance.** The finalized header moves only forward, to one valid at its slot's fork
  and proved by a finality branch under the state root of an attested header two thirds of the
  current or next committee signed (`receive_finalized`); a next committee enters only as the
  committee of an update whose branch proved its root, an all-zero branch
  carrying none (`receive_next`, `nextOk_empty`); the current committee only becomes the old next
  (`receive_current`); no period is skipped (`receive_period`, `committeeFor_live`); every verdict
  past the checks before BLS rests on two thirds (`passed_supermajority`); the anchor only moves
  to a newer attested header of such an update, valid at its fork, a header at the same slot
  never replacing it (`receive_anchor`); `isBetter` is a strict lexicographic order
  (`isBetter_iff_rank`, `isBetter_irrefl`, `isBetter_trans`).
* **25g, conflicts.** A halted store changes nothing and anchors nothing (`receive_halted`,
  `anchored_halted`); a verdict `conflict` halts the store with both sides, after BLS
  (`receive_conflict`); any update that `Passed` and conflicts halts it, live or past committee,
  relevant or not (`receive_halts_on_conflict`); what the store keeps for comparison comes from
  updates that `Passed` (`receive_checkpoints`, `receive_roots`); two sets of at least two
  thirds of a committee overlap in at least a third, 172 of 512 (`overlap`, `overlap_512`).
* **25h, age.** Every accepted update had `effNow − slotTime(finalized) ≤ MAX_AGE` before and
  after its attested slot counted (`receive_accepted_fresh`); every anchor answered is within it
  (`anchored_fresh`); the bootstrap too (`bootstrap_sound`).
* **25i, the clock.** `effNow` is the clock or the newest verified attested slot's time,
  whichever is later (`effNow_eq`); only an update that `Passed`, BLS included, moves the newest
  slot (`receive_newestSlot`); a later clock never makes an update acceptable
  (`fresh_antitone`, `receive_accepted_antitone`); "clock behind" is the clock's slot before the
  newest verified one (`clockBehind_iff`).

What is not proved here: that `process` is the specification's `process_light_client_update`
without the forced update and the optimistic header (reviewed against consensus-specs, and
checked by its `sync` vectors, `leanlight-store-test`), and that the SSZ decoders are
`deserialize` (25a, tested).
-/

namespace LeanLight.Lc.Store

open LeanLight.Lc.Forks (Chain Preset ForkName computeDomain signingRoot domainSyncCommittee)
open LeanLight.Lc.Ssz (isValidNormalizedBranch zeroChunk)

/-! ## The checks before BLS -/

/-- Every check `receive` makes up to and including BLS passed: the store is not halted; the
update's form (`formOk`); the store holds `com` for its signature period, the current or next one
(`live`) or a past one; the age bound at `now`; and the signature under `com`. -/
structure Passed (c : Chain) (s : Store) (now : Nat) (u : Update) (com : Committee) (live : Bool) :
    Prop where
  notHalted : s.halted = none
  form : formOk c u = true
  committee : committeeFor c s (c.periodAt u.signatureSlot) = some (com, live)
  fresh : fresh c s now = true
  signature : verifySignature c com u = true

/-- An update leaves the store as it was, or it passed every check and `afterBls` decides. -/
theorem receive_cases (c : Chain) (s : Store) (now : Nat) (u : Update) :
    (receive c s now u).1 = s ∨
      ∃ com live, Passed c s now u com live ∧ receive c s now u = afterBls c s now u live := by
  unfold receive
  split
  · exact .inl rfl
  · rename_i hh
    split
    · exact .inl rfl
    · rename_i hf
      split
      · exact .inl rfl
      · rename_i com live hcom
        split
        · exact .inl rfl
        · rename_i hfr
          split
          · exact .inl rfl
          · rename_i hsig
            refine .inr ⟨com, live, ⟨?_, ?_, hcom, ?_, ?_⟩, rfl⟩
            · simpa using hh
            · simpa using hf
            · simpa using hfr
            · simpa using hsig

/-- The verdicts of an update that did not pass: the store is unchanged. -/
theorem receive_cases_verdict (c : Chain) (s : Store) (now : Nat) (u : Update) :
    (receive c s now u = (s, .halted) ∧ s.halted.isSome) ∨ receive c s now u = (s, .malformed) ∨
      receive c s now u = (s, .unknownPeriod) ∨ receive c s now u = (s, .tooOld) ∨
      receive c s now u = (s, .badSignature) ∨
      ∃ com live, Passed c s now u com live ∧ receive c s now u = afterBls c s now u live := by
  unfold receive
  split
  · rename_i hh; exact .inl ⟨rfl, hh⟩
  · rename_i hh
    split
    · exact .inr (.inl rfl)
    · rename_i hf
      split
      · exact .inr (.inr (.inl rfl))
      · rename_i com live hcom
        split
        · exact .inr (.inr (.inr (.inl rfl)))
        · rename_i hfr
          split
          · exact .inr (.inr (.inr (.inr (.inl rfl))))
          · rename_i hsig
            refine .inr (.inr (.inr (.inr (.inr ⟨com, live, ⟨?_, ?_, hcom, ?_, ?_⟩, rfl⟩))))
            · simpa using hh
            · simpa using hf
            · simpa using hfr
            · simpa using hsig

/-! ## What `formOk` says -/

theorem formOk_parts {c : Chain} {u : Update} (h : formOk c u = true) :
    supermajority c.preset (u.signers c.preset) = true ∧ u.slot < u.signatureSlot ∧
      u.finalized.beacon.slot ≤ u.slot ∧ isValidHeader c u.attested = true ∧
      finalityOk c u = true ∧ nextOk c u = true := by
  simp only [formOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Two thirds of the committee: `3·signers ≥ 2·SYNC_COMMITTEE_SIZE`. -/
theorem formOk_supermajority {c : Chain} {u : Update} (h : formOk c u = true) :
    2 * c.preset.committeeSize ≤ 3 * u.signers c.preset := by
  have := (formOk_parts h).1
  simpa [supermajority] using this

theorem isEmpty_slot {h : Header} (he : h.isEmpty = true) : h.beacon.slot = 0 := by
  simp only [Header.isEmpty, Bool.and_eq_true, beq_iff_eq] at he
  exact he.1.1.1.1.1.1

/-- A finalized header other than genesis is valid at its own slot's fork, and the finality
branch proves its root at the gindex of the attested slot's fork under the attested state root. -/
theorem finalityOk_pos {c : Chain} {u : Update} (h : finalityOk c u = true)
    (hp : 0 < u.finalized.beacon.slot) :
    u.isFinalityUpdate = true ∧ isValidHeader c u.finalized = true ∧
      isValidNormalizedBranch u.finalized.root u.finalityBranch (finalizedGindex c u.slot)
        u.attested.beacon.stateRoot = true := by
  unfold finalityOk at h
  split at h
  · rename_i hn
    have := isEmpty_slot h
    omega
  · rename_i hn
    have hn' : u.isFinalityUpdate = true := by simpa using hn
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hne : u.finalized.beacon.slot ≠ 0 := by omega
    simp only [hne, ite_false] at h1
    have hl : u.finalizedLeaf = u.finalized.root := by simp [Update.finalizedLeaf, hne]
    rw [hl] at h2
    exact ⟨hn', h1, h2⟩

/-- An all-zero next-committee branch carries the empty committee; any other proves the
committee's root at the gindex of the attested slot's fork under the attested state root. -/
theorem nextOk_empty {c : Chain} {u : Update} (h : nextOk c u = true) :
    (u.isSyncCommitteeUpdate = false → committeeEmpty u.next = true) ∧
      (u.isSyncCommitteeUpdate = true → isValidNormalizedBranch (committeeRoot c.preset u.next)
        u.nextBranch (nextGindex c u.slot) u.attested.beacon.stateRoot = true) := by
  unfold nextOk at h
  constructor
  · intro hs; simpa [hs] using h
  · intro hs; simpa [hs] using h

/-- Every verdict past the checks before BLS rests on two thirds of the committee. -/
theorem passed_supermajority {c : Chain} {s : Store} {now : Nat} {u : Update} {com : Committee}
    {live : Bool} (h : Passed c s now u com live) :
    2 * c.preset.committeeSize ≤ 3 * u.signers c.preset :=
  formOk_supermajority h.form

/-! ## The committee for a signature period -/

/-- The store's current or next committee, never one for a period further on: no period is
skipped. -/
theorem committeeFor_live {c : Chain} {s : Store} {p : Nat} {com : Committee}
    (h : committeeFor c s p = some (com, true)) :
    (p = period c s ∧ com = s.current) ∨ (p = period c s + 1 ∧ s.next = some com) := by
  unfold committeeFor at h
  split at h
  · injection h with h; injection h with h1; exact .inl ⟨by assumption, h1.symm⟩
  · split at h
    · rename_i hp
      cases hn : s.next with
      | none => simp [hn] at h
      | some n =>
        simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact .inr ⟨hp, by rw [h.1]⟩
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, h⟩ := h
      cases h

/-! ## What `afterBls` changes -/

/-- The store once the update's attested slot is counted. -/
abbrev counted (s : Store) (u : Update) : Store :=
  { s with newestSlot := some (max u.slot (s.newestSlot.getD 0)) }

theorem moveAnchor_frame (c : Chain) (s : Store) (u : Update) :
    (moveAnchor c s u).finalized = s.finalized ∧ (moveAnchor c s u).current = s.current ∧
      (moveAnchor c s u).next = s.next ∧ (moveAnchor c s u).newestSlot = s.newestSlot ∧
      (moveAnchor c s u).halted = s.halted ∧ (moveAnchor c s u).checkpoints = s.checkpoints ∧
      (moveAnchor c s u).roots = s.roots := by
  unfold moveAnchor
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `apply` moves the finalized header only forward, to the update's. -/
theorem apply_finalized (c : Chain) (s : Store) (u : Update) :
    (apply c s u).1.finalized = s.finalized ∨
      ((apply c s u).1.finalized = u.finalized ∧
        s.finalized.beacon.slot < u.finalized.beacon.slot) := by
  unfold apply
  cases hn : s.next <;> cases hl : learn c u <;>
    by_cases h1 : c.periodAt u.finalized.beacon.slot = period c s <;>
    by_cases h2 : c.periodAt u.finalized.beacon.slot = period c s + 1 <;>
    by_cases hlt : s.finalized.beacon.slot < u.finalized.beacon.slot <;>
    simp [hl, h1, h2, hlt]

theorem apply_frame (c : Chain) (s : Store) (u : Update) :
    (apply c s u).1.newestSlot = s.newestSlot ∧ (apply c s u).1.halted = s.halted ∧
      (apply c s u).1.checkpoints = s.checkpoints ∧ (apply c s u).1.roots = s.roots ∧
      (apply c s u).1.anchor = s.anchor := by
  unfold apply
  cases hn : s.next <;> cases hl : learn c u <;>
    by_cases h1 : c.periodAt u.finalized.beacon.slot = period c s <;>
    by_cases h2 : c.periodAt u.finalized.beacon.slot = period c s + 1 <;>
    by_cases hlt : s.finalized.beacon.slot < u.finalized.beacon.slot <;>
    simp [hl, h1, h2, hlt]

/-- The committee `learn` takes in: `Committee.ofSync` of the update's committee, never
an empty committee. -/
theorem learn_some {c : Chain} {u : Update} {n : Committee} (h : learn c u = some (some n)) :
    committeeEmpty u.next = false ∧ Committee.ofSync c.preset u.next = some n := by
  unfold learn at h
  split at h
  · simp at h
  · rename_i he
    simp only [Option.map_eq_some_iff, Option.some.injEq] at h
    obtain ⟨n', hn', rfl⟩ := h
    exact ⟨by simpa using he, hn'⟩

/-- `apply`'s committees: unchanged; or the update's committee (or none) as next, the current
unchanged, the store holding no next committee before; or the old next as current and the
update's committee (or none) as next. The update's committee is one `learn` took in. -/
theorem apply_committees (c : Chain) (s : Store) (u : Update) :
    ((apply c s u).1.current = s.current ∧ (apply c s u).1.next = s.next) ∨
      (∃ nc, learn c u = some nc ∧ (apply c s u).1.next = nc ∧
        ((s.next = none ∧ (apply c s u).1.current = s.current) ∨
          (∃ n, s.next = some n ∧ (apply c s u).1.current = n))) := by
  unfold apply
  cases hn : s.next <;> cases hl : learn c u <;>
    by_cases h1 : c.periodAt u.finalized.beacon.slot = period c s <;>
    by_cases h2 : c.periodAt u.finalized.beacon.slot = period c s + 1 <;>
    by_cases hlt : s.finalized.beacon.slot < u.finalized.beacon.slot <;>
    simp [hn, hl, h1, h2, hlt]

theorem moveAnchor_anchor (c : Chain) (s : Store) (u : Update) :
    (moveAnchor c s u).anchor = s.anchor ∨
      ((moveAnchor c s u).anchor = some ⟨u.attested, u.signers c.preset, u.signatureSlot⟩ ∧
        ∀ a ∈ s.anchor, a.header.beacon.slot < u.slot) := by
  unfold moveAnchor
  split
  · rename_i h; exact .inr ⟨rfl, by simp [h]⟩
  · rename_i a h
    split
    · rename_i hlt; exact .inr ⟨rfl, by simp [h, hlt]⟩
    · split <;> exact .inl rfl

/-- The store after `process` at the update's anchor step: `best` set, the anchor moved. -/
abbrev bested (c : Chain) (s : Store) (u : Update) : Store := moveAnchor c (keepBest c s u) u

theorem process_cases (c : Chain) (s : Store) (u : Update) :
    process c s u = apply c (bested c s u) u ∨ process c s u = (bested c s u, .accepted false false) := by
  unfold process
  dsimp only
  split
  · exact .inl rfl
  · exact .inr rfl

theorem process_frame (c : Chain) (s : Store) (u : Update) :
    (process c s u).1.newestSlot = s.newestSlot ∧ (process c s u).1.halted = s.halted ∧
      (process c s u).1.checkpoints = s.checkpoints ∧ (process c s u).1.roots = s.roots := by
  have hm := moveAnchor_frame c (keepBest c s u) u
  rcases process_cases c s u with h | h <;> rw [h]
  · have ha := apply_frame c (bested c s u) u
    exact ⟨ha.1.trans hm.2.2.2.1, ha.2.1.trans hm.2.2.2.2.1, ha.2.2.1.trans hm.2.2.2.2.2.1,
      ha.2.2.2.1.trans hm.2.2.2.2.2.2⟩
  · exact ⟨hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩

theorem process_not_conflict (c : Chain) (s : Store) (u : Update) : (process c s u).2 ≠ .conflict := by
  rcases process_cases c s u with h | h <;> rw [h]
  · unfold apply
    cases hn : (bested c s u).next <;> cases hl : learn c u <;>
      by_cases h1 : c.periodAt u.finalized.beacon.slot = period c (bested c s u) <;>
      by_cases h2 : c.periodAt u.finalized.beacon.slot = period c (bested c s u) + 1 <;>
      simp [hl, h1, h2]
  · simp

theorem process_finalized (c : Chain) (s : Store) (u : Update) :
    (process c s u).1.finalized = s.finalized ∨
      ((process c s u).1.finalized = u.finalized ∧
        s.finalized.beacon.slot < u.finalized.beacon.slot) := by
  have hm := (moveAnchor_frame c (keepBest c s u) u).1
  rcases process_cases c s u with h | h <;> rw [h]
  · rcases apply_finalized c (bested c s u) u with h' | h'
    · exact .inl (h'.trans hm)
    · have hb : (bested c s u).finalized = s.finalized := hm
      exact .inr ⟨h'.1, by rw [← hb]; exact h'.2⟩
  · exact .inl hm

theorem process_committees (c : Chain) (s : Store) (u : Update) :
    ((process c s u).1.current = s.current ∧ (process c s u).1.next = s.next) ∨
      (∃ nc, learn c u = some nc ∧ (process c s u).1.next = nc ∧
        ((s.next = none ∧ (process c s u).1.current = s.current) ∨
          (∃ n, s.next = some n ∧ (process c s u).1.current = n))) := by
  have hm := moveAnchor_frame c (keepBest c s u) u
  rcases process_cases c s u with h | h <;> rw [h]
  · rcases apply_committees c (bested c s u) u with h' | ⟨nc, hl, hn, h'⟩
    · exact .inl ⟨h'.1.trans hm.2.1, h'.2.trans hm.2.2.1⟩
    · refine .inr ⟨nc, hl, hn, ?_⟩
      rw [hm.2.2.1, hm.2.1] at h'
      exact h'
  · exact .inl ⟨hm.2.1, hm.2.2.1⟩

theorem process_anchor (c : Chain) (s : Store) (u : Update) :
    (process c s u).1.anchor = s.anchor ∨
      ((process c s u).1.anchor = some ⟨u.attested, u.signers c.preset, u.signatureSlot⟩ ∧
        ∀ a ∈ s.anchor, a.header.beacon.slot < u.slot) := by
  have hm := moveAnchor_anchor c (keepBest c s u) u
  rcases process_cases c s u with h | h <;> rw [h]
  · rw [(apply_frame c (bested c s u) u).2.2.2.2]; exact hm
  · exact hm

/-! ## `afterBls` -/

theorem retain_frame (c : Chain) (s : Store) (now : Nat) (u : Update) :
    (retain c s now u).finalized = s.finalized ∧ (retain c s now u).current = s.current ∧
      (retain c s now u).next = s.next ∧ (retain c s now u).anchor = s.anchor ∧
      (retain c s now u).newestSlot = s.newestSlot ∧ (retain c s now u).halted = s.halted ∧
      (retain c s now u).past = s.past ∧ (retain c s now u).best = s.best :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fresh_retain (c : Chain) (s : Store) (now now' : Nat) (u : Update) :
    fresh c (retain c s now' u) now = fresh c s now := rfl

theorem relevant_retain (c : Chain) (s : Store) (now : Nat) (u u' : Update) :
    relevant c (retain c s now u) u' = relevant c s u' := rfl

/-- What `afterBls` does: a conflict halts the store; else, the update kept, it stops (compared,
too old, not relevant), or, live, fresh with its slot counted and relevant, it is processed. -/
theorem afterBls_cases (c : Chain) (s : Store) (now : Nat) (u : Update) (live : Bool) :
    (∃ k, conflictOf c (counted s u) u = some k ∧
        afterBls c s now u live = ({ counted s u with halted := some k }, .conflict)) ∨
      (conflictOf c (counted s u) u = none ∧
        afterBls c s now u live = (retain c (counted s u) now u, (afterBls c s now u live).2) ∧
        ((afterBls c s now u live).2 = .compared ∨ (afterBls c s now u live).2 = .tooOld ∨
          (afterBls c s now u live).2 = .irrelevant)) ∨
      (conflictOf c (counted s u) u = none ∧ live = true ∧ fresh c (counted s u) now = true ∧
        relevant c (counted s u) u = true ∧
        afterBls c s now u live = process c (retain c (counted s u) now u) u) := by
  cases hk : conflictOf c (counted s u) u with
  | some k =>
    refine .inl ⟨k, rfl, ?_⟩
    simp only [counted] at hk
    simp [afterBls, hk]
  | none =>
    simp only [counted] at hk
    cases live
    · exact .inr (.inl ⟨rfl, by simp [afterBls, hk], by simp [afterBls, hk]⟩)
    · cases hf : fresh c (counted s u) now
      · simp only [counted] at hf
        exact .inr (.inl ⟨rfl, by simp [afterBls, hk, fresh_retain, hf],
          by simp [afterBls, hk, fresh_retain, hf]⟩)
      · cases hv : relevant c (counted s u) u
        · simp only [counted] at hf hv
          exact .inr (.inl ⟨rfl, by simp [afterBls, hk, fresh_retain, hf, relevant_retain, hv],
            by simp [afterBls, hk, fresh_retain, hf, relevant_retain, hv]⟩)
        · simp only [counted] at hf hv
          exact .inr (.inr ⟨rfl, rfl, rfl, rfl,
            by simp [afterBls, hk, fresh_retain, hf, relevant_retain, hv]⟩)

/-! ## What `receive` can change (25f) -/

/-- **The finalized header (25f)** moves only forward, to the update's finalized header, when the
update passed every check under the store's current or next committee (`live`): two thirds
signed, BLS; and that header is valid at its own slot's fork and proved by the finality branch at
the gindex of the attested slot's fork, under the state root of the attested header the
committee signed. -/
theorem receive_finalized (c : Chain) (s : Store) (now : Nat) (u : Update) :
    (receive c s now u).1.finalized = s.finalized ∨
      ∃ com, Passed c s now u com true ∧ (receive c s now u).1.finalized = u.finalized ∧
        s.finalized.beacon.slot < u.finalized.beacon.slot ∧ u.isFinalityUpdate = true ∧
        isValidHeader c u.finalized = true ∧
        isValidNormalizedBranch u.finalized.root u.finalityBranch (finalizedGindex c u.slot)
          u.attested.beacon.stateRoot = true := by
  rcases receive_cases c s now u with h | ⟨com, live, hp, h⟩
  · exact .inl (by rw [h])
  · rw [h]
    rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, hl, -, -, ha⟩
    · rw [ha]; exact .inl rfl
    · rw [ha]; exact .inl rfl
    · rw [ha]
      subst hl
      rcases process_finalized c (retain c (counted s u) now u) u with h' | ⟨h', hlt⟩
      · exact .inl h'
      · have hlt' : s.finalized.beacon.slot < u.finalized.beacon.slot := hlt
        obtain ⟨h1, h2, h3⟩ := finalityOk_pos (formOk_parts hp.form).2.2.2.2.1 (by omega)
        exact .inr ⟨com, hp, h', hlt', h1, h2, h3⟩

/-- The finalized header never moves back. -/
theorem receive_finalized_mono (c : Chain) (s : Store) (now : Nat) (u : Update) :
    s.finalized.beacon.slot ≤ (receive c s now u).1.finalized.beacon.slot := by
  rcases receive_finalized c s now u with h | ⟨_, _, h, hlt, _⟩ <;> rw [h]; omega

/-- A committee `Committee.ofSync` takes in: as many keys as the preset's committee, held as
the committee's encodings, its aggregate key's, and the committee's root. No key is validated,
as in the specification: that they are points of G1 and the aggregate their sum is the
hypothesis `Committee.Consistent` (`LeanLightProofs.Signers`). -/
theorem ofSync_keys {p : Preset} {sc : LeanLight.Lc.Ssz.SyncCommittee} {com : Committee}
    (h : Committee.ofSync p sc = some com) :
    sc.pubkeys.size = p.committeeSize ∧ com.pubkeys = sc.pubkeys ∧
      com.aggregate = sc.aggregatePubkey ∧ com.root = committeeRoot p sc := by
  unfold Committee.ofSync at h
  split at h
  · rename_i hs
    obtain rfl := Option.some.inj h
    exact ⟨hs, rfl, rfl, rfl⟩
  · cases h

/-- **Committees (25f).** The current committee changes only to the store's next one, and the
next only to none or to a committee the update brings: an update that passed every check under
the current or next committee, whose next-committee branch proves that committee's root at the
gindex of the attested slot's fork under the attested state root, as many keys as the preset's
committee (`ofSync_keys`).
An all-zero branch carries the empty committee, which never enters (`nextOk_empty`,
`learn_some`). -/
theorem receive_committees (c : Chain) (s : Store) (now : Nat) (u : Update) :
    ((receive c s now u).1.current = s.current ∧ (receive c s now u).1.next = s.next) ∨
      ∃ com, Passed c s now u com true ∧
        ((s.next = none ∧ (receive c s now u).1.current = s.current) ∨
          (∃ n, s.next = some n ∧ (receive c s now u).1.current = n)) ∧
        ((receive c s now u).1.next = none ∨
          ∃ n, (receive c s now u).1.next = some n ∧ Committee.ofSync c.preset u.next = some n ∧
            isValidNormalizedBranch n.root u.nextBranch (nextGindex c u.slot)
              u.attested.beacon.stateRoot = true) := by
  rcases receive_cases c s now u with h | ⟨com, live, hp, h⟩
  · exact .inl (by rw [h]; exact ⟨rfl, rfl⟩)
  · rw [h]
    rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, hl, -, -, ha⟩
    · rw [ha]; exact .inl ⟨rfl, rfl⟩
    · rw [ha]; exact .inl ⟨rfl, rfl⟩
    · rw [ha]
      subst hl
      rcases process_committees c (retain c (counted s u) now u) u with h' | ⟨nc, hl, hn, hc⟩
      · exact .inl h'
      · refine .inr ⟨com, hp, hc, ?_⟩
        cases nc with
        | none => exact .inl hn
        | some n =>
          obtain ⟨he, hs⟩ := learn_some hl
          have hsc : u.isSyncCommitteeUpdate = true := by
            cases hsu : u.isSyncCommitteeUpdate
            · have := (nextOk_empty (formOk_parts hp.form).2.2.2.2.2).1 hsu
              rw [this] at he; cases he
            · rfl
          have hb := (nextOk_empty (formOk_parts hp.form).2.2.2.2.2).2 hsc
          rw [← (ofSync_keys hs).2.2.2] at hb
          exact .inr ⟨n, hn, hs, hb⟩

theorem periodAt_mono (c : Chain) {a b : Nat} (h : a ≤ b) : c.periodAt a ≤ c.periodAt b := by
  unfold Chain.periodAt Chain.epochAt
  exact Nat.div_le_div_right (Nat.div_le_div_right h)

/-- **No skipped period (25f).** An update that changes the finalized header was signed in the
store's period or the next, by the current committee or the next one the store holds; the store
moves at most one period. -/
theorem receive_period (c : Chain) (s : Store) (now : Nat) (u : Update) :
    period c s ≤ period c (receive c s now u).1 ∧ period c (receive c s now u).1 ≤ period c s + 1 := by
  rcases receive_finalized c s now u with h | ⟨com, hp, h, hlt, -⟩
  · unfold period; rw [h]; omega
  · unfold period; rw [h]
    obtain ⟨-, hsig, hfa, -⟩ := formOk_parts hp.form
    have h1 := periodAt_mono c (show u.finalized.beacon.slot ≤ u.signatureSlot by omega)
    have h2 := periodAt_mono c (show s.finalized.beacon.slot ≤ u.finalized.beacon.slot by omega)
    rcases committeeFor_live hp.committee with ⟨hq, -⟩ | ⟨hq, -⟩ <;>
      · unfold period at hq; omega

/-- **The anchor (25f)** moves only to the attested header of an update that passed every check
under the current or next committee (two thirds signed, BLS, the header valid at its slot's
fork), and only to a newer slot: at the anchor's slot another header never replaces it. -/
theorem receive_anchor (c : Chain) (s : Store) (now : Nat) (u : Update) :
    (receive c s now u).1.anchor = s.anchor ∨
      ∃ com, Passed c s now u com true ∧
        (receive c s now u).1.anchor = some ⟨u.attested, u.signers c.preset, u.signatureSlot⟩ ∧
        isValidHeader c u.attested = true ∧ ∀ a ∈ s.anchor, a.header.beacon.slot < u.slot := by
  rcases receive_cases c s now u with h | ⟨com, live, hp, h⟩
  · exact .inl (by rw [h])
  · rw [h]
    rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, hl, -, -, ha⟩
    · rw [ha]; exact .inl rfl
    · rw [ha]; exact .inl rfl
    · rw [ha]
      subst hl
      rcases process_anchor c (retain c (counted s u) now u) u with h' | ⟨h', hn⟩
      · exact .inl h'
      · exact .inr ⟨com, hp, h', (formOk_parts hp.form).2.2.2.1, hn⟩

/-! ## Conflicts (25g) -/

/-- A halted store accepts nothing and changes nothing. -/
theorem receive_halted {c : Chain} {s : Store} (h : s.halted.isSome) (now : Nat) (u : Update) :
    receive c s now u = (s, .halted) := by
  simp [receive, h]

/-- A halted store anchors nothing. -/
theorem anchored_halted {c : Chain} {s : Store} (h : s.halted.isSome) (now : Nat) :
    anchored c s now = none := by
  simp [anchored, Option.isSome_iff_ne_none.mp h]

/-- **Comparison before relevance, and after BLS (25g).** An update that passed every check,
BLS included, under any committee the store holds for its signature period (current, next or
past), and conflicts with what the store keeps, halts the store, whether or not it is relevant. -/
theorem receive_halts_on_conflict {c : Chain} {s : Store} {now : Nat} {u : Update} {com : Committee}
    {live : Bool} (hp : Passed c s now u com live) {k : Conflict}
    (hk : conflictOf c (counted s u) u = some k) :
    receive c s now u = ({ counted s u with halted := some k }, .conflict) := by
  have hh : s.halted.isSome = false := by simp [hp.notHalted]
  simp only [receive, hh, hp.form, hp.committee, hp.fresh, hp.signature, Bool.false_eq_true,
    ite_false, Bool.not_true]
  unfold afterBls
  simp only [counted] at hk
  simp [hk]

/-- **A conflict (25g)** halts the store, after BLS: the update passed every check under a
committee the store holds for its signature period, and conflicts with what the store kept. -/
theorem receive_conflict {c : Chain} {s : Store} {now : Nat} {u : Update}
    (h : (receive c s now u).2 = .conflict) :
    ∃ com live k, Passed c s now u com live ∧ conflictOf c (counted s u) u = some k ∧
      (receive c s now u).1.halted = some k := by
  rcases receive_cases_verdict c s now u with ⟨he, -⟩ | he | he | he | he | ⟨com, live, hp, he⟩
  all_goals try (rw [he] at h; cases h)
  rw [he] at h ⊢
  rcases afterBls_cases c s now u live with ⟨k, hk, ha⟩ | ⟨-, ha, hv⟩ | ⟨-, -, -, -, ha⟩
  · exact ⟨com, live, k, hp, hk, by rw [ha]⟩
  · rcases hv with hv | hv | hv <;> rw [hv] at h <;> cases h
  · rw [ha] at h; exact absurd h (process_not_conflict c _ u)

/-- What a conflict holds: for finality, a checkpoint the store kept for the update's finalized
epoch with another root (its witness the held side), the update's finalized checkpoint (not
genesis) the new side; for committees, a root the store kept for the period of the update's
next committee, another than its committee's, and the update's next committee the new side. -/
theorem conflictOf_spec {c : Chain} {s : Store} {u : Update} {k : Conflict}
    (h : conflictOf c s u = some k) :
    (k.kind = .finality ∧ u.isFinalityUpdate = true ∧ u.finalized.beacon.slot ≠ 0 ∧
        k.new = Witness.ofFinality u ∧
        ∃ cp ∈ s.checkpoints, cp.epoch = finalityEpoch c u ∧ cp.root ≠ u.finalized.root ∧
          k.held = some cp.witness) ∨
      (k.kind = .committee ∧ u.isSyncCommitteeUpdate = true ∧ k.new = Witness.ofNext c u ∧
        ∃ r ∈ s.roots, r.period = nextPeriod c u ∧ r.root ≠ committeeRoot c.preset u.next ∧
          k.held = r.witness) := by
  unfold conflictOf at h
  simp only at h
  split at h
  · rename_i k' hk
    injection h with h; subst h
    split at hk
    · rename_i hf
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
      split at hk
      · rename_i cp hcp
        split at hk
        · cases hk
        · rename_i hne
          injection hk with hk; subst hk
          have hm := List.mem_of_find?_eq_some hcp
          have he : cp.epoch = finalityEpoch c u := by simpa using List.find?_some hcp
          exact .inl ⟨rfl, hf.1, hf.2, rfl, cp, hm, he, hne, rfl⟩
      · cases hk
    · cases hk
  · rename_i hn
    split at h
    · rename_i hs
      split at h
      · rename_i r hr
        split at h
        · cases h
        · rename_i hne
          injection h with h; subst h
          have hm := List.mem_of_find?_eq_some hr
          have hp : r.period = nextPeriod c u := by simpa using List.find?_some hr
          exact .inr ⟨rfl, hs, rfl, r, hm, hp, hne, rfl⟩
      · cases h
    · cases h

/-- What the store keeps to compare comes from updates that passed every check, BLS included:
each finalized checkpoint the store holds after an update is one it held before, or that
update's. -/
theorem receive_checkpoints (c : Chain) (s : Store) (now : Nat) (u : Update) :
    ∀ cp ∈ (receive c s now u).1.checkpoints, cp ∈ s.checkpoints ∨
      ∃ com live, Passed c s now u com live ∧
        cp = ⟨finalityEpoch c u, u.finalized.root, u.finalized.beacon.slot, Witness.ofFinality u⟩ := by
  intro cp hcp
  rcases receive_cases c s now u with h | ⟨com, live, hp, h⟩
  · rw [h] at hcp; exact .inl hcp
  · have key : ∀ x ∈ (retain c (counted s u) now u).checkpoints, x ∈ s.checkpoints ∨
        x = ⟨finalityEpoch c u, u.finalized.root, u.finalized.beacon.slot, Witness.ofFinality u⟩ := by
      intro x hx
      unfold retain at hx
      simp only at hx
      have hx := (List.mem_filter.mp (List.mem_of_mem_take hx)).1
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inr rfl
        · exact .inl hx
      · exact .inl hx
    rw [h] at hcp
    rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, -, -, -, ha⟩
    · rw [ha] at hcp; exact .inl hcp
    · rw [ha] at hcp
      rcases key cp hcp with h' | h'
      · exact .inl h'
      · exact .inr ⟨com, live, hp, h'⟩
    · rw [ha, (process_frame c _ u).2.2.1] at hcp
      rcases key cp hcp with h' | h'
      · exact .inl h'
      · exact .inr ⟨com, live, hp, h'⟩

/-- Likewise each committee root the store holds after an update. -/
theorem receive_roots (c : Chain) (s : Store) (now : Nat) (u : Update) :
    ∀ r ∈ (receive c s now u).1.roots, r ∈ s.roots ∨
      ∃ com live, Passed c s now u com live ∧
        r = ⟨nextPeriod c u, committeeRoot c.preset u.next, some (Witness.ofNext c u)⟩ := by
  intro r hr
  rcases receive_cases c s now u with h | ⟨com, live, hp, h⟩
  · rw [h] at hr; exact .inl hr
  · have key : ∀ x ∈ (retain c (counted s u) now u).roots, x ∈ s.roots ∨
        x = ⟨nextPeriod c u, committeeRoot c.preset u.next, some (Witness.ofNext c u)⟩ := by
      intro x hx
      unfold retain at hx
      simp only at hx
      have hx := List.mem_of_mem_take hx
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inr rfl
        · exact .inl hx
      · exact .inl hx
    rw [h] at hr
    rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, -, -, -, ha⟩
    · rw [ha] at hr; exact .inl hr
    · rw [ha] at hr
      rcases key r hr with h' | h'
      · exact .inl h'
      · exact .inr ⟨com, live, hp, h'⟩
    · rw [ha, (process_frame c _ u).2.2.2] at hr
      rcases key r hr with h' | h'
      · exact .inl h'
      · exact .inr ⟨com, live, hp, h'⟩

/-! ## The age bound (25h) and the clock (25i) -/

/-- **The age bound (25h).** An accepted update was judged within `MAX_AGE` against `effNow`
before it, and again with its attested slot counted. -/
theorem receive_accepted_fresh {c : Chain} {s : Store} {now : Nat} {u : Update} {a l : Bool}
    (h : (receive c s now u).2 = .accepted a l) :
    fresh c s now = true ∧ fresh c (counted s u) now = true := by
  rcases receive_cases_verdict c s now u with ⟨he, -⟩ | he | he | he | he | ⟨com, live, hp, he⟩
  all_goals try (rw [he] at h; cases h)
  rw [he] at h
  rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, hv⟩ | ⟨-, -, hf, -, ha⟩
  · rw [ha] at h; cases h
  · rcases hv with hv | hv | hv <;> rw [hv] at h <;> cases h
  · exact ⟨hp.fresh, hf⟩

/-- An anchor is answered only within `MAX_AGE`, and only from a store not halted. -/
theorem anchored_fresh {c : Chain} {s : Store} {now : Nat} {a : Anchor}
    (h : anchored c s now = some a) : fresh c s now = true ∧ s.halted = none ∧ s.anchor = some a := by
  unfold anchored at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    exact ⟨hc.2, hc.1, h⟩
  · cases h

/-- `effNow`: the clock, or the newest verified attested slot's time, whichever is later. -/
theorem effNow_eq (c : Chain) (s : Store) (now : Nat) :
    effNow c s now = match s.newestSlot with
      | some n => max now (c.slotTime n)
      | none => now := rfl

/-- **Only verified data moves `effNow` (25i).** The newest slot changes only by an update that
passed every check, BLS included, to its attested slot if that is newer. -/
theorem receive_newestSlot (c : Chain) (s : Store) (now : Nat) (u : Update) :
    (receive c s now u).1.newestSlot = s.newestSlot ∨
      ∃ com live, Passed c s now u com live ∧
        (receive c s now u).1.newestSlot = some (max u.slot (s.newestSlot.getD 0)) := by
  rcases receive_cases c s now u with h | ⟨com, live, hp, h⟩
  · exact .inl (by rw [h])
  · refine .inr ⟨com, live, hp, ?_⟩
    rw [h]
    rcases afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, -, -, -, ha⟩
    · rw [ha]
    · rw [ha]; rfl
    · rw [ha, (process_frame c _ u).1]; rfl

/-- A later clock never makes the age bound hold. -/
theorem fresh_antitone {c : Chain} {s : Store} {now now' : Nat} (h : now ≤ now')
    (hf : fresh c s now' = true) : fresh c s now = true := by
  unfold fresh effNow at *
  simp only [decide_eq_true_eq] at *
  split at hf <;> simp_all <;> omega

/-- "Clock behind": the clock's slot is before the newest verified attested slot. -/
theorem clockBehind_iff (c : Chain) (s : Store) (now : Nat) :
    clockBehind c s now = true ↔ ∃ n, s.newestSlot = some n ∧ c.slotOf now < n := by
  unfold clockBehind
  split <;> simp_all

/-! ## Two thirds and two thirds -/

/-- **Any two sets of at least two thirds of a committee overlap in at least a third (25g).** -/
theorem overlap {α : Type} [DecidableEq α] (U A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ U)
    (ha : 2 * U.card ≤ 3 * A.card) (hb : 2 * U.card ≤ 3 * B.card) :
    U.card ≤ 3 * (A ∩ B).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 : (A ∪ B).card ≤ U.card := Finset.card_le_card (Finset.union_subset hA hB)
  omega

/-- On the mainnet committee: two sets of at least 342 of 512 members share at least 172. -/
theorem overlap_512 {α : Type} [DecidableEq α] (U A B : Finset α) (hU : U.card = 512)
    (hA : A ⊆ U) (hB : B ⊆ U) (ha : 342 ≤ A.card) (hb : 342 ≤ B.card) : 172 ≤ (A ∩ B).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 : (A ∪ B).card ≤ U.card := Finset.card_le_card (Finset.union_subset hA hB)
  omega

/-! ## Bootstrap (25e) -/

/-- **Bootstrap binds the checkpoint (25e).** A store starts only from a bootstrap whose header is
valid at its slot's fork, whose header root is the configured checkpoint, whose current committee
is proved by its branch at the gindex of that slot's fork under the header's state root, whose
keys are as many as the preset's committee (`ofSync_keys`), with the checkpoint
younger than `MAX_AGE` at the clock. It starts with that header finalized, that committee current,
no next committee, nothing anchored, no verified slot, nothing kept but that committee's root,
and not halted. -/
theorem bootstrap_sound {c : Chain} {cp : ByteArray} {now : Nat} {b : Bootstrap} {s : Store}
    (h : bootstrap c cp now b = some s) :
    isValidHeader c b.header = true ∧ b.header.root = cp ∧
      isValidNormalizedBranch (committeeRoot c.preset b.committee) b.branch
        (currentGindex c b.header.beacon.slot) b.header.beacon.stateRoot = true ∧
      now - c.slotTime b.header.beacon.slot ≤ c.maxAge ∧
      Committee.ofSync c.preset b.committee = some s.current ∧ s.finalized = b.header ∧
      s.next = none ∧ s.anchor = none ∧ s.newestSlot = none ∧ s.halted = none ∧
      s.checkpoints = [] ∧ s.past = [] := by
  unfold bootstrap at h
  simp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨com, hcom, rfl⟩ := h
    exact ⟨h1, h2, h3, h4, hcom, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

/-! ## Domains and forks (25d) -/

/-- **The signature check (25d)**: FastAggregateVerify's check (`Bls.verifyAggregate`) of the
participants' aggregate key (`signersKey?`: the sum of the keys whose bit is set, on a committee
consistent with the chain, `Committee.Consistent`, `LeanLightProofs.Signers.signersKey?_eq`), of the signing
root of the attested header's root under
`compute_domain(DOMAIN_SYNC_COMMITTEE, version, genesis_validators_root)`, the version the fork
table gives at the epoch of `max(signature_slot, 1) − 1`. -/
theorem verifySignature_iff (c : Chain) (com : Committee) (u : Update) :
    verifySignature c com u = true ↔
      ∃ v, c.versionAt (c.epochAt (max u.signatureSlot 1 - 1)) = some v ∧
        Bls.verifyAggregate (signersKey? com u.aggregate.bits)
          (signingRoot u.attested.root (computeDomain domainSyncCommittee v c.genesisValidatorsRoot))
          u.aggregate.signature = true := by
  rw [← Forks.signatureVersion_eq]
  unfold verifySignature
  split <;> simp_all

/-- `compute_signing_root`: `hash_tree_root(SigningData(object_root, domain))`, two nodes
hashed; `compute_domain`: the domain type, then the fork data root's first 28 bytes. -/
theorem signingRoot_eq (r d : ByteArray) : signingRoot r d = Ssz.hash64 r d := rfl

theorem computeDomain_eq (t v g : ByteArray) :
    computeDomain t v g = t ++ Bytes.extract (Ssz.forkDataRoot v g) 0 28 := rfl

/-- **Strict forks (25d, G8).** An update is decoded only as the fork its tag names, kept only when
that is the fork `Forks` gives for its attested slot, and, tagged with a digest, when that is the
chain's digest at that slot's epoch. -/
theorem decodeUpdate_fork {codec : Codec.Codec} {c : Chain} {k : Codec.Kind} {tag : Codec.Tag}
    {bs : ByteArray} {u : Update} (h : Codec.decodeUpdate codec c k tag bs = some u) :
    ∃ f, Codec.tagFork c tag = some f ∧ c.forkOfSlot u.slot = some f ∧
      codec.update k f bs = some u ∧ Codec.tagFits c u.slot tag = true := by
  unfold Codec.decodeUpdate at h
  split at h
  · cases h
  · rename_i f hf
    split at h
    · cases h
    · rename_i u' hu
      split at h
      · rename_i hc
        injection h with h; subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨f, hf, hc.1, hu, hc.2⟩
      · cases h

/-- Likewise a bootstrap, at its header's slot. -/
theorem decodeBootstrap_fork {codec : Codec.Codec} {c : Chain} {tag : Codec.Tag} {bs : ByteArray}
    {b : Bootstrap} (h : Codec.decodeBootstrap codec c tag bs = some b) :
    ∃ f, Codec.tagFork c tag = some f ∧ c.forkOfSlot b.header.beacon.slot = some f ∧
      codec.bootstrap f bs = some b ∧ Codec.tagFits c b.header.beacon.slot tag = true := by
  unfold Codec.decodeBootstrap at h
  split at h
  · cases h
  · rename_i f hf
    split at h
    · cases h
    · rename_i b' hb
      split at h
      · rename_i hc
        injection h with h; subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨f, hf, hc.1, hb, hc.2⟩
      · cases h

/-- **`signature_slot` is not signed (25d).** Another signature slot after the attested slot
changes nothing `formOk` checks. -/
theorem formOk_signatureSlot (c : Chain) (u : Update) {s' : Nat} (h : u.slot < u.signatureSlot)
    (h' : u.slot < s') : formOk c { u with signatureSlot := s' } = formOk c u := by
  have hf : finalityOk c { u with signatureSlot := s' } = finalityOk c u := rfl
  have hn : nextOk c { u with signatureSlot := s' } = nextOk c u := rfl
  have hs : ({ u with signatureSlot := s' } : Update).signers c.preset = u.signers c.preset := rfl
  have hl : ({ u with signatureSlot := s' } : Update).slot = u.slot := rfl
  simp only [formOk, hf, hn, hs, hl]
  rw [decide_eq_true h', decide_eq_true h]

/-- Nor the signature check, under one fork version. -/
theorem verifySignature_signatureSlot (c : Chain) (com : Committee) (u : Update) {s' : Nat}
    (h : c.signatureVersion s' = c.signatureVersion u.signatureSlot) :
    verifySignature c com { u with signatureSlot := s' } = verifySignature c com u := by
  unfold verifySignature
  simp only [h]

/-- Nor the committee chosen, within one period. -/
theorem committeeFor_signatureSlot (c : Chain) (s : Store) (u : Update) {s' : Nat}
    (h : c.periodAt s' = c.periodAt u.signatureSlot) :
    committeeFor c s (c.periodAt ({ u with signatureSlot := s' } : Update).signatureSlot) =
      committeeFor c s (c.periodAt u.signatureSlot) := by
  simp only [h]

/-! ## `isBetter` (25f) -/

/-- Lexicographic order, larger first. -/
def lexGt : List Int → List Int → Prop
  | a :: as, b :: bs => b < a ∨ (a = b ∧ lexGt as bs)
  | _, _ => False

theorem lexGtB_iff : ∀ x y : List Int, lexGtB x y = true ↔ lexGt x y
  | a :: x, b :: y => by
    simp only [lexGtB, lexGt]
    by_cases h : a = b
    · subst h; simp [lexGtB_iff x y]
    · simp only [h, ite_false, decide_eq_true_eq, false_and, or_false]
  | [], _ => by simp [lexGtB, lexGt]
  | _ :: _, [] => by simp [lexGtB, lexGt]

theorem lexGt_irrefl : ∀ l : List Int, ¬ lexGt l l
  | [] => by simp [lexGt]
  | a :: l => by
    simp only [lexGt, lt_self_iff_false, true_and, false_or]
    exact lexGt_irrefl l

theorem lexGt_trans : ∀ x y z : List Int, lexGt x y → lexGt y z → lexGt x z
  | a :: x, b :: y, c :: z, h1, h2 => by
    simp only [lexGt] at *
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact .inl (by omega)
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, lexGt_trans x y z h1 h2⟩
  | [], _, _, h, _ => by simp [lexGt] at h
  | _ :: _, [], _, h, _ => by simp [lexGt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexGt] at h

/-- **`isBetter` is a lexicographic order on `rank` (25f)**: supermajority; below it, more
participants; a relevant next committee; finality; sync-committee finality; more participants;
the older attested slot; the earlier signature slot. -/
theorem isBetter_iff_rank (c : Chain) (a b : Update) :
    isBetter c a b = true ↔ lexGt (rank c a) (rank c b) := lexGtB_iff _ _

/-- **`isBetter` is a strict preference (25f)**: irreflexive, -/
theorem isBetter_irrefl (c : Chain) (u : Update) : isBetter c u u = false := by
  cases h : isBetter c u u
  · rfl
  · exact absurd ((isBetter_iff_rank c u u).mp h) (lexGt_irrefl _)

/-- and transitive. -/
theorem isBetter_trans (c : Chain) {a b d : Update} (h1 : isBetter c a b = true)
    (h2 : isBetter c b d = true) : isBetter c a d = true :=
  (isBetter_iff_rank c a d).mpr (lexGt_trans _ _ _ ((isBetter_iff_rank c a b).mp h1)
    ((isBetter_iff_rank c b d).mp h2))

/-- and total on keys: of two updates with different keys, one is better. -/
theorem isBetter_total (c : Chain) (a b : Update) (h : rank c a ≠ rank c b) :
    isBetter c a b = true ∨ isBetter c b a = true := by
  rw [isBetter_iff_rank, isBetter_iff_rank]
  have key : ∀ x y : List Int, x.length = y.length → x ≠ y → lexGt x y ∨ lexGt y x := by
    intro x
    induction x with
    | nil => intro y hl hne; cases y with
      | nil => exact absurd rfl hne
      | cons => simp at hl
    | cons a x ih =>
      intro y hl hne
      cases y with
      | nil => simp at hl
      | cons b y =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [lexGt]
        by_cases hab : a = b
        · subst hab
          have : x ≠ y := fun h => hne (by rw [h])
          rcases ih y hl this with h | h
          · exact .inl (.inr ⟨rfl, h⟩)
          · exact .inr (.inr ⟨rfl, h⟩)
        · rcases Int.lt_or_gt_of_ne hab with h | h
          · exact .inr (.inl h)
          · exact .inl (.inl h)
  exact key _ _ (by simp [rank]) h

/-- **`signature_slot` moves only the last tiebreak (25d).** Within one period, another signature
slot leaves every key of `rank` but the last. -/
theorem rank_signatureSlot (c : Chain) (u : Update) {s' : Nat}
    (h : c.periodAt s' = c.periodAt u.signatureSlot) :
    (rank c { u with signatureSlot := s' }).take 7 = (rank c u).take 7 := by
  simp only [rank, Update.slot, Update.signers, Update.isSyncCommitteeUpdate,
    Update.isFinalityUpdate, h]
  rfl

end LeanLight.Lc.Store
