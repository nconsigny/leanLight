import LeanLightProofs.Anchor
import LeanLightProofs.Store
import LeanLightProofs.Spec.MptTrie
import LeanLight.Driver

/-!
# A client's reads rest only on the checked steps

About `LeanLight.Driver`, what the command-line client calls with the bytes it fetched.

* `Reaches c root s`: the store `s` is one `Store.bootstrap` of checkpoint `root` starts and
  `Store.receive` steps carry, at any clocks and on any updates.
* `start_reaches`, `feed_reaches`: `start` gives only such stores and `feed` keeps a store such,
  whatever bytes the client hands them, in whatever order, as often as it likes.
* `AnchorProved`, `reaches_committees`, `reaches_finalized`, `reaches_anchor`,
  `reaches_anchored`, `reaches_bindAnchor_sound`, `reaches_read_sound`: at any
  reached store, `Store.anchored` yields an anchor carried by a chain of two-thirds-signed
  `CommitteeAuth` periods from the bootstrap checkpoint, alongside `FinalizedAuth` on `s.finalized`,
  freshness and age bounds, `Anchor.bind_spec` on the EL header, and MPT collision-binding
  soundness (`Spec.MptTrie`) on the account and every requested storage slot.
* `read_sound`: a value `read` returns is read under the EL header
  `Anchor.bind` keeps for the store's anchor (whose RLP hashes to the anchored beacon header's
  execution block hash, `Anchor.bind_spec`), the account the trie's specification reads from the
  proof's nodes under that header's state root, each word the specification's storage read under
  the account's storage root (`Facts.storage_spec`).
* `codeOk_spec`: code accepted hashes to the proved code hash.

So what the client prints rests on the store's rules (bootstrap binds the checkpoint, acceptance
only after every check: `LeanLightProofs.Store`), `Anchor.bind`, and the trie, never on which
objects the unproved fetch loop asked for or how it ordered them. That loop decides only whether
a read happens and how fresh the anchor is.
-/

namespace LeanLight.Lc.Driver

open LeanLight.Lc.Forks (Chain)

/-- The stores reached from checkpoint `root`: one `Store.bootstrap` of it starts, then any
number of `Store.receive` steps, at any clocks, on any updates. -/
inductive Reaches (c : Chain) (root : ByteArray) : Store.Store → Prop
  | start {now : Nat} {b : Store.Bootstrap} {s : Store.Store} :
      Store.bootstrap c root now b = some s → Reaches c root s
  | step {s : Store.Store} (now : Nat) (u : Store.Update) :
      Reaches c root s → Reaches c root (Store.receive c s now u).1

/-- `start` gives only a store `Store.bootstrap` of the checkpoint starts. -/
theorem start_reaches {c : Chain} {root : ByteArray} {now : Nat} {tag : Codec.Tag}
    {bs : ByteArray} {s : Store.Store} (h : start c root now tag bs = some s) :
    Reaches c root s := by
  unfold start at h
  split at h
  · cases h
  · exact .start h

/-- `feed` keeps a store reached from the checkpoint reached from it, whatever its bytes. -/
theorem feed_reaches {c : Chain} {root : ByteArray} {s : Store.Store} (hs : Reaches c root s)
    (now : Nat) (k : Codec.Kind) (tag : Codec.Tag) (bs : ByteArray) :
    Reaches c root (feed c s now k tag bs).1 := by
  unfold feed
  split
  · exact hs
  · exact .step now _ hs

/-- **What a read returns is the checked steps' (the client's reads).** At any store, a value
`read` returns at clock `now` is read at the store's anchor `a`
(`Store.anchored`): under the EL header `h` that `Anchor.bind` keeps for `a`'s beacon header from
the endpoint's `rlp`, the account is what `Spec.Mpt.account` reads from the proof's `nodes` under
`h`'s state root, and the words are what `Spec.Mpt.storage` reads for each slot under the
account's storage root. Short of a Keccak-256 collision, those are the chain's values at the
block the anchor names (`Spec.MptTrie`, `Anchor.bind_spec`). The client reads only at stores
`start` and `feed` gave, so at stores reached from its checkpoint (`start_reaches`,
`feed_reaches`). -/
theorem read_sound {c : Chain} {s : Store.Store} {now : Nat} {rlp : ByteArray} {addr : List UInt8} {nodes : ByteArray}
    {slots : List (List UInt8 × ByteArray)} {h : Spec.Header.Header} {acct : Spec.Mpt.Account}
    {vs : List Nat} (hr : read c s now rlp addr nodes slots = some (h, acct, vs)) :
    ∃ a, Store.anchored c s now = some a ∧ Anchor.bind c a.header rlp = some h ∧
      Spec.Mpt.account h.stateRoot addr nodes.data.toList = some acct ∧
      slots.map (fun x => Spec.Mpt.storage acct.storageRoot x.1 x.2.data.toList) = vs.map some := by
  unfold read at hr
  split at hr
  · cases hr
  · rename_i a ha
    exact ⟨a, ha, Facts.storage_spec hr⟩

/-- `bindAnchor` binds an EL header only to the store's anchor, as `Anchor.bind` does. -/
theorem bindAnchor_sound {c : Chain} {s : Store.Store} {now : Nat} {rlp : ByteArray}
    {b : Store.Header} {h : Spec.Header.Header} (hb : bindAnchor c s now rlp = some (b, h)) :
    ∃ a, Store.anchored c s now = some a ∧ a.header = b ∧ Anchor.bind c b rlp = some h := by
  unfold bindAnchor at hb
  split at hb
  · cases hb
  · rename_i a ha
    cases hbind : Anchor.bind c a.header rlp with
    | none => simp [hbind] at hb
    | some h' =>
      simp only [hbind, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨a, ha, rfl, hbind⟩

/-- Code `codeOk` accepts hashes to the account's proved code hash. -/
theorem codeOk_spec {acct : Spec.Mpt.Account} {code : ByteArray} (h : codeOk acct code = true) :
    Spec.Common.keccak code.data.toList = acct.codeHash := by
  simpa [codeOk] using h

/-- A committee for period `p` authenticated from `root`: either the bootstrap checkpoint's
committee (`start`), or proved at `nextGindex` under an attested header signed by at least two
thirds of period `p`'s committee (`next`). -/
inductive CommitteeAuth (c : Chain) (root : ByteArray) : Nat → Store.Committee → Prop
  | start {now : Nat} {b : Store.Bootstrap} {s : Store.Store} :
      Store.bootstrap c root now b = some s →
        CommitteeAuth c root (Store.period c s) s.current
  | next {p : Nat} {com n : Store.Committee} {u : Store.Update} :
      CommitteeAuth c root p com →
      c.periodAt u.signatureSlot = p →
      Store.formOk c u = true →
      2 * c.preset.committeeSize ≤ 3 * u.signers c.preset →
      Store.verifySignature c com u = true →
      u.isSyncCommitteeUpdate = true →
      Store.Committee.ofSync c.preset u.next = some n →
      Ssz.isValidNormalizedBranch n.root u.nextBranch (Store.nextGindex c u.slot)
        u.attested.beacon.stateRoot = true →
      CommitteeAuth c root (c.periodAt u.slot + 1) n

/-- A finalized header authenticated from `root`: valid at its slot's fork, and either having
`root` itself or proved at `finalizedGindex` under an attested header signed by at least two thirds
of an authenticated committee. -/
def FinalizedAuth (c : Chain) (root : ByteArray) (f : Store.Header) : Prop :=
  Store.isValidHeader c f = true ∧
    (f.root = root ∨
      ∃ p com u, CommitteeAuth c root p com ∧
        c.periodAt u.signatureSlot = p ∧
        Store.formOk c u = true ∧
        2 * c.preset.committeeSize ≤ 3 * u.signers c.preset ∧
        Store.verifySignature c com u = true ∧
        u.isFinalityUpdate = true ∧
        u.finalized = f ∧
        0 < f.beacon.slot ∧
        Ssz.isValidNormalizedBranch f.root u.finalityBranch (Store.finalizedGindex c u.slot)
          u.attested.beacon.stateRoot = true)

/-- An anchor authenticated from `root`: the attested header of a well-formed update signed by at
least two thirds of an authenticated committee, valid at its slot's fork. -/
def AnchorAuth (c : Chain) (root : ByteArray) (a : Store.Anchor) : Prop :=
  ∃ p com u, CommitteeAuth c root p com ∧
    c.periodAt u.signatureSlot = p ∧
    Store.formOk c u = true ∧
    2 * c.preset.committeeSize ≤ 3 * u.signers c.preset ∧
    Store.verifySignature c com u = true ∧
    Store.isValidHeader c u.attested = true ∧
    a = ⟨u.attested, u.signers c.preset, u.signatureSlot⟩

/-- All store invariants established when `Store.anchored c s now = some a` at a store reached
from `root`. -/
structure AnchorProved (c : Chain) (root : ByteArray) (s : Store.Store) (now : Nat)
    (a : Store.Anchor) : Prop where
  reaches : Reaches c root s
  anchored : Store.anchored c s now = some a
  notHalted : s.halted = none
  fresh : Store.fresh c s now = true
  age : Store.effNow c s now - c.slotTime s.finalized.beacon.slot ≤ c.maxAge
  currentAuth : CommitteeAuth c root (Store.period c s) s.current
  finalizedAuth : FinalizedAuth c root s.finalized
  anchorAuth : AnchorAuth c root a

theorem reaches_bootstrap {c : Chain} {root : ByteArray} {s : Store.Store}
    (hs : Reaches c root s) :
    ∃ now₀ b s₀, Store.bootstrap c root now₀ b = some s₀ ∧
      Store.isValidHeader c b.header = true ∧ b.header.root = root ∧
      Ssz.isValidNormalizedBranch (Store.committeeRoot c.preset b.committee) b.branch
        (Store.currentGindex c b.header.beacon.slot) b.header.beacon.stateRoot = true ∧
      now₀ - c.slotTime b.header.beacon.slot ≤ c.maxAge ∧
      Store.Committee.ofSync c.preset b.committee = some s₀.current ∧
      s₀.finalized = b.header ∧ b.header.beacon.slot ≤ s.finalized.beacon.slot := by
  induction hs with
  | start hb =>
    obtain ⟨hv, hr, hbr, ha, hc, hf, -⟩ := Store.bootstrap_sound hb
    exact ⟨_, _, _, hb, hv, hr, hbr, ha, hc, hf, by rw [hf]⟩
  | @step s' now u _ ih =>
    obtain ⟨now₀, b, s₀, hb, hv, hr, hbr, ha, hc, hf, hle⟩ := ih
    have hm := Store.receive_finalized_mono c s' now u
    exact ⟨now₀, b, s₀, hb, hv, hr, hbr, ha, hc, hf, Nat.le_trans hle hm⟩

theorem committeeFor_live_auth {c : Chain} {root : ByteArray} {s : Store.Store} {p : Nat}
    {com : Store.Committee}
    (hcur : CommitteeAuth c root (Store.period c s) s.current)
    (hnext : ∀ n, s.next = some n → CommitteeAuth c root (Store.period c s + 1) n)
    (hc : Store.committeeFor c s p = some (com, true)) :
    CommitteeAuth c root p com := by
  rcases Store.committeeFor_live hc with ⟨rfl, rfl⟩ | ⟨rfl, hn⟩
  · exact hcur
  · exact hnext com hn

theorem apply_committees_auth {c : Chain} {root : ByteArray} {b : Store.Store} {u : Store.Update}
    {com : Store.Committee}
    (hcur : CommitteeAuth c root (Store.period c b) b.current)
    (hnext : ∀ n, b.next = some n → CommitteeAuth c root (Store.period c b + 1) n)
    (hcom : CommitteeAuth c root (c.periodAt u.signatureSlot) com)
    (hform : Store.formOk c u = true)
    (hsm : 2 * c.preset.committeeSize ≤ 3 * u.signers c.preset)
    (hsig : Store.verifySignature c com u = true)
    (hlive : (c.periodAt u.signatureSlot = Store.period c b ∧ com = b.current) ∨
      (c.periodAt u.signatureSlot = Store.period c b + 1 ∧ b.next = some com)) :
    CommitteeAuth c root (Store.period c (Store.apply c b u).1) (Store.apply c b u).1.current ∧
      ∀ n, (Store.apply c b u).1.next = some n →
        CommitteeAuth c root (Store.period c (Store.apply c b u).1 + 1) n := by
  have hlearned : ∀ {nc n}, Store.learn c u = some nc → nc = some n →
      CommitteeAuth c root (c.periodAt u.slot + 1) n := by
    intro nc n hlearn hnc
    subst hnc
    obtain ⟨he, hsync⟩ := Store.learn_some hlearn
    have hsc : u.isSyncCommitteeUpdate = true := by
      cases hsu : u.isSyncCommitteeUpdate
      · have := (Store.nextOk_empty (Store.formOk_parts hform).2.2.2.2.2).1 hsu
        rw [this] at he; cases he
      · rfl
    have hbr := (Store.nextOk_empty (Store.formOk_parts hform).2.2.2.2.2).2 hsc
    rw [← (Store.ofSync_keys hsync).2.2.2] at hbr
    exact .next hcom rfl hform hsm hsig hsc hsync hbr
  unfold Store.apply
  cases hbnext : b.next with
  | none =>
    dsimp only
    by_cases hfp : c.periodAt u.finalized.beacon.slot = Store.period c b
    · rw [ite_eq_left hfp]
      cases hlearn : Store.learn c u with
      | none =>
        dsimp only
        exact ⟨hcur, fun n h => by rw [hbnext] at h; cases h⟩
      | some nc =>
        dsimp only
        have hu_per : c.periodAt u.slot = Store.period c b := by
          obtain ⟨-, hsig_lt, hfa, -⟩ := Store.formOk_parts hform
          have hp1 := Store.periodAt_mono c hfa
          have hp2 := Store.periodAt_mono c (Nat.le_of_lt hsig_lt)
          rcases hlive with ⟨hsigp, -⟩ | ⟨-, hsnext⟩
          · omega
          · rw [hbnext] at hsnext; cases hsnext
        split
        · dsimp only
          have hp' : Store.period c { b with next := nc, finalized := u.finalized, best := none } =
              Store.period c b := by
            unfold Store.period; exact hfp
          rw [hp']
          exact ⟨hcur, fun n hn => hu_per ▸ hlearned hlearn hn⟩
        · dsimp only
          have hp' : Store.period c { b with next := nc, best := none } = Store.period c b := rfl
          rw [hp']
          exact ⟨hcur, fun n hn => hu_per ▸ hlearned hlearn hn⟩
    · rw [ite_eq_right hfp]
      exact ⟨hcur, hnext⟩
  | some nx =>
    dsimp only
    by_cases hfp : c.periodAt u.finalized.beacon.slot = Store.period c b + 1
    · rw [ite_eq_left hfp]
      cases hlearn : Store.learn c u with
      | none =>
        dsimp only
        exact ⟨hcur, fun n hn => by rw [hbnext] at hn; injection hn with hn; subst hn; exact hnext nx hbnext⟩
      | some nc =>
        dsimp only
        have hlt : b.finalized.beacon.slot < u.finalized.beacon.slot := by
          by_contra hge
          have hle : u.finalized.beacon.slot ≤ b.finalized.beacon.slot := by omega
          have := Store.periodAt_mono c hle
          unfold Store.period at hfp
          omega
        rw [ite_eq_left hlt]
        dsimp only
        let b' : Store.Store :=
          { b with
            current := nx
            next := nc
            past := ((Store.period c b, b.current) :: b.past).take Store.maxPast
            finalized := u.finalized
            best := none }
        have hp' : Store.period c b' = Store.period c b + 1 := by
          unfold Store.period; exact hfp
        change CommitteeAuth c root (Store.period c b') b'.current ∧
          ∀ n, b'.next = some n → CommitteeAuth c root (Store.period c b' + 1) n
        rw [hp']
        have hu_per : c.periodAt u.slot = Store.period c b + 1 := by
          obtain ⟨-, hsig_lt, hfa, -⟩ := Store.formOk_parts hform
          have hp1 := Store.periodAt_mono c hfa
          have hp2 := Store.periodAt_mono c (Nat.le_of_lt hsig_lt)
          rcases hlive with ⟨hsigp, -⟩ | ⟨hsigp, -⟩ <;> omega
        exact ⟨hnext nx hbnext, fun n hn => hu_per ▸ hlearned hlearn hn⟩
    · rw [ite_eq_right hfp]
      dsimp only
      split
      · rename_i hlt
        dsimp only
        have hp' : Store.period c { b with finalized := u.finalized, best := none } =
            Store.period c b := by
          obtain ⟨-, hsig_lt, hfa, -⟩ := Store.formOk_parts hform
          have hp1 := Store.periodAt_mono c (Nat.le_of_lt hlt)
          have hp2 := Store.periodAt_mono c (Nat.le_trans hfa (Nat.le_of_lt hsig_lt))
          have hsig_le : c.periodAt u.signatureSlot ≤ Store.period c b + 1 := by
            rcases hlive with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega
          unfold Store.period at hp1 hsig_le hfp ⊢
          dsimp only
          omega
        rw [hp']
        exact ⟨hcur, fun n hn => by rw [hbnext] at hn; injection hn with hn; subst hn; exact hnext nx hbnext⟩
      · dsimp only
        have hp' : Store.period c { b with best := none } = Store.period c b := rfl
        rw [hp']
        exact ⟨hcur, fun n hn => by rw [hbnext] at hn; injection hn with hn; subst hn; exact hnext nx hbnext⟩

/-- Every reached store's current and next committees are authenticated from `root`. -/
theorem reaches_committees {c : Chain} {root : ByteArray} {s : Store.Store}
    (hs : Reaches c root s) :
    CommitteeAuth c root (Store.period c s) s.current ∧
      ∀ n, s.next = some n → CommitteeAuth c root (Store.period c s + 1) n := by
  induction hs with
  | start hb =>
    obtain ⟨-, -, -, -, -, -, hn, -⟩ := Store.bootstrap_sound hb
    exact ⟨.start hb, fun n h => by rw [hn] at h; cases h⟩
  | @step s now u _ ih =>
    obtain ⟨hcur, hnext⟩ := ih
    let r := (Store.receive c s now u).1
    rcases Store.receive_cases c s now u with h | ⟨com, live, hp, h⟩
    · change CommitteeAuth c root (Store.period c r) r.current ∧
        ∀ n, r.next = some n → CommitteeAuth c root (Store.period c r + 1) n
      have hr : r = s := h
      rw [hr]
      exact ⟨hcur, hnext⟩
    · have hr : r = (Store.afterBls c s now u live).1 := congrArg Prod.fst h
      rcases Store.afterBls_cases c s now u live with
          ⟨k, -, ha⟩ | ⟨-, ha, -⟩ | ⟨-, hlive, -, -, ha⟩
      · have hr' : r = { Store.counted s u with halted := some k } :=
          hr.trans (congrArg Prod.fst ha)
        change CommitteeAuth c root (Store.period c r) r.current ∧
          ∀ n, r.next = some n → CommitteeAuth c root (Store.period c r + 1) n
        rw [hr']
        exact ⟨hcur, hnext⟩
      · have hr' : r = Store.retain c (Store.counted s u) now u :=
          hr.trans (congrArg Prod.fst ha)
        change CommitteeAuth c root (Store.period c r) r.current ∧
          ∀ n, r.next = some n → CommitteeAuth c root (Store.period c r + 1) n
        rw [hr']
        exact ⟨hcur, hnext⟩
      · subst hlive
        have hcom : CommitteeAuth c root (c.periodAt u.signatureSlot) com :=
          committeeFor_live_auth hcur hnext hp.committee
        let s₁ := Store.retain c (Store.counted s u) now u
        have hr' : r = (Store.process c s₁ u).1 := hr.trans (congrArg Prod.fst ha)
        change CommitteeAuth c root (Store.period c r) r.current ∧
          ∀ n, r.next = some n → CommitteeAuth c root (Store.period c r + 1) n
        rw [hr']
        let b := Store.bested c s₁ u
        have hbf : b.finalized = s.finalized := (Store.moveAnchor_frame c (Store.keepBest c s₁ u) u).1
        have hbc : b.current = s.current := (Store.moveAnchor_frame c (Store.keepBest c s₁ u) u).2.1
        have hbn : b.next = s.next := (Store.moveAnchor_frame c (Store.keepBest c s₁ u) u).2.2.1
        have hbp : Store.period c b = Store.period c s := by unfold Store.period; rw [hbf]
        have hbcur : CommitteeAuth c root (Store.period c b) b.current := by
          rw [hbp, hbc]; exact hcur
        have hbnext : ∀ n, b.next = some n → CommitteeAuth c root (Store.period c b + 1) n := by
          rw [hbp, hbn]; exact hnext
        have hblive : (c.periodAt u.signatureSlot = Store.period c b ∧ com = b.current) ∨
            (c.periodAt u.signatureSlot = Store.period c b + 1 ∧ b.next = some com) := by
          rw [hbp, hbc, hbn]
          exact Store.committeeFor_live hp.committee
        rcases Store.process_cases c s₁ u with hp_cases | hp_cases
        · rw [congrArg Prod.fst hp_cases]
          exact apply_committees_auth hbcur hbnext hcom hp.form (Store.passed_supermajority hp)
            hp.signature hblive
        · rw [congrArg Prod.fst hp_cases]
          exact ⟨hbcur, hbnext⟩

/-- Every reached store's finalized header is either `root`'s bootstrap header or proved under a
two-thirds-signed update from an authenticated committee. -/
theorem reaches_finalized {c : Chain} {root : ByteArray} {s : Store.Store}
    (hs : Reaches c root s) : FinalizedAuth c root s.finalized := by
  induction hs with
  | start hb =>
    obtain ⟨hv, hr, -, -, -, hf, -⟩ := Store.bootstrap_sound hb
    rw [hf]
    exact ⟨hv, .inl hr⟩
  | @step s now u hprev ih =>
    rcases Store.receive_finalized c s now u with hf | ⟨com, hp, hf, hlt, hfin, hv, hbr⟩
    · rw [hf]; exact ih
    · rw [hf]
      obtain ⟨hcur, hnext⟩ := reaches_committees hprev
      have hcom := committeeFor_live_auth hcur hnext hp.committee
      exact ⟨hv, .inr ⟨c.periodAt u.signatureSlot, com, u, hcom, rfl, hp.form,
        Store.passed_supermajority hp, hp.signature, hfin, rfl, by omega, hbr⟩⟩

/-- Any anchor held by a reached store was signed by at least two thirds of an authenticated
committee. -/
theorem reaches_anchor {c : Chain} {root : ByteArray} {s : Store.Store}
    (hs : Reaches c root s) : ∀ a ∈ s.anchor, AnchorAuth c root a := by
  induction hs with
  | start hb =>
    obtain ⟨-, -, -, -, -, -, -, ha, -⟩ := Store.bootstrap_sound hb
    intro a hm
    rw [ha] at hm
    cases hm
  | @step s now u hprev ih =>
    rcases Store.receive_anchor c s now u with ha | ⟨com, hp, ha, hv, -⟩
    · rw [ha]; exact ih
    · rw [ha]
      intro a hm
      simp only [Option.mem_def, Option.some.injEq] at hm
      subst hm
      obtain ⟨hcur, hnext⟩ := reaches_committees hprev
      have hcom := committeeFor_live_auth hcur hnext hp.committee
      exact ⟨c.periodAt u.signatureSlot, com, u, hcom, rfl, hp.form,
        Store.passed_supermajority hp, hp.signature, hv, rfl⟩

/-- `Store.anchored` at a reached store yields `AnchorProved`. -/
theorem reaches_anchored {c : Chain} {root : ByteArray} {s : Store.Store} {now : Nat}
    {a : Store.Anchor} (hs : Reaches c root s) (ha : Store.anchored c s now = some a) :
    AnchorProved c root s now a := by
  obtain ⟨hfr, hnh, hanc⟩ := Store.anchored_fresh ha
  have hage : Store.effNow c s now - c.slotTime s.finalized.beacon.slot ≤ c.maxAge := by
    simpa [Store.fresh] using hfr
  exact ⟨hs, ha, hnh, hfr, hage, (reaches_committees hs).1, reaches_finalized hs,
    reaches_anchor hs a hanc⟩

/-- `bindAnchor` at a reached store binds an EL header to an authenticated anchor (`AnchorProved`,
`Anchor.bind_spec`). -/
theorem reaches_bindAnchor_sound {c : Chain} {root : ByteArray} {s : Store.Store} {now : Nat}
    {rlp : ByteArray} {b : Store.Header} {h : Spec.Header.Header}
    (hs : Reaches c root s) (hb : bindAnchor c s now rlp = some (b, h)) :
    ∃ a fs, AnchorProved c root s now a ∧ a.header = b ∧ Anchor.bind c b rlp = some h ∧
      Spec.Rlp.encodeTree (.branch (fs.map .leaf)) = some rlp.data.toList ∧
      Spec.Common.keccak rlp.data.toList = b.elHash.data.toList ∧
      Spec.Header.ofFields fs = some h := by
  obtain ⟨a, ha, rfl, hbind⟩ := bindAnchor_sound hb
  obtain ⟨fs, henc, hk, hof, -⟩ := Anchor.bind_spec hbind
  exact ⟨a, fs, reaches_anchored hs ha, rfl, hbind, henc, hk, hof⟩

/-- End-to-end soundness of `read` at a reached store: ties the returned EL header, account and
storage slots back to `root` through `AnchorProved`, `Anchor.bind_spec`, and `Spec.MptTrie`
(short of an explicit Keccak-256 collision witness). -/
theorem reaches_read_sound {c : Chain} {root : ByteArray} {s : Store.Store} {now : Nat}
    {rlp : ByteArray} {addr : List UInt8} {nodes : ByteArray}
    {slots : List (List UInt8 × ByteArray)} {h : Spec.Header.Header} {acct : Spec.Mpt.Account}
    {vs : List Nat} (hs : Reaches c root s)
    (hr : read c s now rlp addr nodes slots = some (h, acct, vs)) :
    ∃ a fs, AnchorProved c root s now a ∧
      Anchor.bind c a.header rlp = some h ∧
      Spec.Rlp.encodeTree (.branch (fs.map .leaf)) = some rlp.data.toList ∧
      Spec.Common.keccak rlp.data.toList = a.header.elHash.data.toList ∧
      Spec.Header.ofFields fs = some h ∧
      Spec.Mpt.account h.stateRoot addr nodes.data.toList = some acct ∧
      slots.map (fun x => Spec.Mpt.storage acct.storageRoot x.1 x.2.data.toList) = vs.map some ∧
      vs.length = slots.length ∧
      (∀ p acct', Spec.Mpt.account h.stateRoot addr p = some acct' →
        acct' = acct ∨
          Spec.Mpt.IsCollision
            (Spec.Mpt.collision h.stateRoot (Spec.Common.keccak addr) nodes.data.toList p)) ∧
      (∀ (S : Spec.Mpt.Trie.State), (∀ q ∈ S, Spec.Mpt.Trie.AccountValid q.2) →
        h.stateRoot = Spec.Mpt.Trie.stateRoot S →
        acct = Spec.Mpt.Trie.accountAt S addr ∨
          Spec.Mpt.IsCollision (Spec.Mpt.Trie.clash S addr) ∨
          Spec.Mpt.IsCollision
            (Spec.Mpt.collision (Spec.Mpt.Trie.stateRoot S) (Spec.Common.keccak addr)
              nodes.data.toList (Spec.Mpt.Trie.accountProof S addr))) ∧
      (∀ i (hi : i < slots.length) (hv : i < vs.length) p x,
        Spec.Mpt.storage acct.storageRoot slots[i].1 p = some x →
        x = vs[i] ∨
          Spec.Mpt.IsCollision
            (Spec.Mpt.collision acct.storageRoot (Spec.Common.keccak slots[i].1)
              slots[i].2.data.toList p)) ∧
      (∀ i (hi : i < slots.length) (hv : i < vs.length) (T : Spec.Mpt.Trie.Storage),
        Spec.Mpt.Trie.StorageOk T →
        acct.storageRoot = Spec.Mpt.Trie.storageRoot T →
        vs[i] = Spec.Mpt.Trie.slotAt T slots[i].1 ∨
          Spec.Mpt.IsCollision (Spec.Mpt.Trie.clash T slots[i].1) ∨
          Spec.Mpt.IsCollision
            (Spec.Mpt.collision (Spec.Mpt.Trie.storageRoot T) (Spec.Common.keccak slots[i].1)
              slots[i].2.data.toList (Spec.Mpt.Trie.storageProof T slots[i].1))) := by
  obtain ⟨a, ha, hbind, hacct, hslots⟩ := read_sound hr
  obtain ⟨fs, henc, hk, hof, -⟩ := Anchor.bind_spec hbind
  have hlen : vs.length = slots.length := by
    have hl := congrArg List.length hslots
    simp only [List.length_map] at hl
    exact hl.symm
  have hslot_at : ∀ i (hi : i < slots.length) (hv : i < vs.length),
      Spec.Mpt.storage acct.storageRoot slots[i].1 slots[i].2.data.toList = some vs[i] := by
    intro i hi hv
    have hmap := congrArg (fun l => l[i]?) hslots
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_map,
      List.getElem?_eq_getElem hv, Option.map_some, Option.map_some] at hmap
    injection hmap
  refine ⟨a, fs, reaches_anchored hs ha, hbind, henc, hk, hof, hacct, hslots, hlen, ?_, ?_, ?_, ?_⟩
  · intro p acct' hp
    by_cases he : acct' = acct
    · exact .inl he
    · exact .inr (Spec.Mpt.account_binding hacct hp (Ne.symm he))
  · intro S hS hsr
    have hacct' : Spec.Mpt.account (Spec.Mpt.Trie.stateRoot S) addr nodes.data.toList = some acct := by
      rwa [← hsr]
    exact Spec.Mpt.Trie.account_sound hS hacct'
  · intro i hi hv p x hp
    by_cases he : x = vs[i]
    · exact .inl he
    · exact .inr (Spec.Mpt.storage_binding (hslot_at i hi hv) hp (Ne.symm he))
  · intro i hi hv T hT hsr
    have hst' : Spec.Mpt.storage (Spec.Mpt.Trie.storageRoot T) slots[i].1 slots[i].2.data.toList =
        some vs[i] := by
      rw [← hsr]
      exact hslot_at i hi hv
    exact Spec.Mpt.Trie.storage_sound hT hst'

end LeanLight.Lc.Driver
