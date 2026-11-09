import LeanLightProofs.Spec.SyncProtocol
import LeanLightProofs.Driver
import LeanLightProofs.Signers

/-!
# The store refines consensus-specs' sync protocol

`LeanLight.Store` is proved to be consensus-specs' light client (`LeanLightProofs.Spec.SyncProtocol`,
the specification transcribed) restricted to fewer updates: every update the store accepts, the
specification's `process_light_client_update` accepts at the same clock, and the two stores agree
after it; every update the store does not accept leaves what the specification's store holds as
it was. So every store leanLight reaches is one the specification reaches from the same
checkpoint, through the updates leanLight accepted (`reaches_spec`).

**What "agree" means** (`Sim`): the finalized header, the current and next sync committees, the
best valid update, the optimistic header and both participation counters are the specification
store's, a next committee leanLight does not hold being one the specification does not know.

**What it rests on**, as hypotheses, never axioms:

* `Agrees c cfg`: the chain table leanLight follows (`Forks.Chain`) agrees with the
  specification's configuration on the preset, the fork versions and the forks' epochs, for the
  slots it accepts. Proved for mainnet and Sepolia (`agrees_mainnet`, `agrees_sepolia`), against
  their `config.yaml` with every fork from Altair on.
* `Committee.Valid` of each committee whose signature is checked: every key passes KeyValidate
  and the aggregate key decodes to their sum. The beacon state's committees are such (each key
  was validated at deposit; `aggregate_pubkey` is `eth_aggregate_pubkeys` of the keys); leanLight
  does not validate them (`Committee.ofSync`), which is why the signature check that runs (the
  aggregate key less the absent keys) equals the specification's (`FastAggregateVerify` over the
  participants' keys, each KeyValidated) only on such a committee (`verifySignature_spec`).
  `reaches_spec` takes it of every committee authenticated from the checkpoint
  (`Driver.CommitteeAuth`), the committees the store can hold.

**Where leanLight refuses more** (each a check the specification does not make, so each makes the
store follow a subsequence of the specification's updates; none changes the result of an update
both accept): two thirds of the committee, not `MIN_SYNC_COMMITTEE_PARTICIPANTS`; headers from
the chain table's first fork on (Electra), with an Electra or Fulu container only before Gloas;
`signature_slot` below 2⁶⁴; the age bound `MAX_AGE`; a store halted by a conflict; and
`process_light_client_store_force_update` never called by the client (`Store.forceUpdate`, which
the tests call, refines it too: `forceUpdate_refines`).
-/

namespace LeanLight.Spec.LightClient

open LeanLight.Lc
open LeanLight.Lc.Store (Header Update Bootstrap Committee Exec)
open LeanLight.Lc.Forks (Chain)

/-! ## leanLight's objects, as the specification's -/

/-- A normalized header as the specification's `LightClientHeader`. -/
def ofHeader (h : Header) : LightClientHeader :=
  match h.exec with
  | .payload e => .electra h.beacon e h.branch
  | .blockHash b => .gloas h.beacon b h.branch

/-- A normalized update as the specification's `LightClientUpdate`. -/
def ofUpdate (u : Update) : LightClientUpdate :=
  { attested_header := ofHeader u.attested, next_sync_committee := u.next,
    next_sync_committee_branch := u.nextBranch, finalized_header := ofHeader u.finalized,
    finality_branch := u.finalityBranch, sync_aggregate := u.aggregate,
    signature_slot := u.signatureSlot }

/-- A normalized bootstrap as the specification's `LightClientBootstrap`. -/
def ofBootstrap (b : Bootstrap) : LightClientBootstrap :=
  ⟨ofHeader b.header, b.committee, b.branch⟩

/-- A committee the store holds as the specification's `SyncCommittee`. -/
def ofCommittee (com : Committee) : Ssz.SyncCommittee := ⟨com.pubkeys, com.aggregate⟩

@[simp] theorem ofHeader_beacon (h : Header) : (ofHeader h).beacon = h.beacon := by
  unfold ofHeader; cases h.exec <;> rfl

@[simp] theorem ofUpdate_attested (u : Update) :
    (ofUpdate u).attested_header = ofHeader u.attested := rfl
@[simp] theorem ofUpdate_finalized (u : Update) :
    (ofUpdate u).finalized_header = ofHeader u.finalized := rfl
@[simp] theorem ofUpdate_next (u : Update) : (ofUpdate u).next_sync_committee = u.next := rfl
@[simp] theorem ofUpdate_signatureSlot (u : Update) : (ofUpdate u).signature_slot = u.signatureSlot :=
  rfl
@[simp] theorem ofUpdate_aggregate (u : Update) : (ofUpdate u).sync_aggregate = u.aggregate := rfl

/-! ## The chain table and the configuration -/

/-- **The chain table agrees with the configuration** on the slots leanLight accepts (`uint64`):
the preset, the slot arithmetic, every fork version the table gives, which slots are past the
Electra and Gloas forks, and that a slot the table knows a fork for is past Deneb (and Capella),
of the fork Gloas exactly when past the Gloas epoch. -/
structure Agrees (c : Chain) (cfg : Config) : Prop where
  slotsPerEpoch : c.preset.slotsPerEpoch = cfg.SLOTS_PER_EPOCH
  epochsPerPeriod : c.preset.epochsPerPeriod = cfg.EPOCHS_PER_SYNC_COMMITTEE_PERIOD
  committeeSize : c.preset.committeeSize = cfg.SYNC_COMMITTEE_SIZE
  committeeDepth : c.preset.committeeDepth = floorlog2 cfg.SYNC_COMMITTEE_SIZE
  sizePos : 0 < cfg.SYNC_COMMITTEE_SIZE
  minParticipants : cfg.MIN_SYNC_COMMITTEE_PARTICIPANTS ≤ 1
  version : ∀ slot v, slot < 2 ^ 64 → c.versionAt (c.epochAt slot) = some v →
    v = compute_fork_version cfg (compute_epoch_at_slot cfg slot)
  gloas : ∀ slot, slot < 2 ^ 64 →
    (c.gloasAt slot = true ↔ cfg.GLOAS_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot)
  electra : ∀ slot, slot < 2 ^ 64 →
    (Store.electraAt c slot = true ↔ cfg.ELECTRA_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot)
  fork : ∀ slot f, slot < 2 ^ 64 → c.forkOfSlot slot = some f →
    cfg.CAPELLA_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot ∧
      cfg.DENEB_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot ∧
      (f = .gloas ↔ cfg.GLOAS_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot)

section Agrees

variable {c : Chain} {cfg : Config} (hA : Agrees c cfg)
include hA

theorem Agrees.epochAt (slot : Nat) : c.epochAt slot = compute_epoch_at_slot cfg slot := by
  simp [Chain.epochAt, compute_epoch_at_slot, hA.slotsPerEpoch]

theorem Agrees.periodAt (slot : Nat) :
    c.periodAt slot = compute_sync_committee_period_at_slot cfg slot := by
  simp [Chain.periodAt, compute_sync_committee_period_at_slot, compute_sync_committee_period,
    hA.epochAt slot, hA.epochsPerPeriod]

theorem Agrees.finalizedGindex {slot : Nat} (hs : slot < 2 ^ 64) :
    Store.finalizedGindex c slot = finalized_root_gindex_at_slot cfg slot := by
  unfold Store.finalizedGindex finalized_root_gindex_at_slot
  have hg := hA.gloas slot hs
  have he := hA.electra slot hs
  by_cases h1 : cfg.GLOAS_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot
  · simp [hg.mpr h1, h1]; rfl
  · have : c.gloasAt slot = false := by simpa [h1] using hg
    by_cases h2 : cfg.ELECTRA_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot
    · simp [this, h1, he.mpr h2, h2]; rfl
    · have : Store.electraAt c slot = false := by simpa [h2] using he
      simp [*]; rfl

theorem Agrees.currentGindex {slot : Nat} (hs : slot < 2 ^ 64) :
    Store.currentGindex c slot = current_sync_committee_gindex_at_slot cfg slot := by
  unfold Store.currentGindex current_sync_committee_gindex_at_slot
  have hg := hA.gloas slot hs
  have he := hA.electra slot hs
  by_cases h1 : cfg.GLOAS_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot
  · simp [hg.mpr h1, h1]; rfl
  · have : c.gloasAt slot = false := by simpa [h1] using hg
    by_cases h2 : cfg.ELECTRA_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot
    · simp [this, h1, he.mpr h2, h2]; rfl
    · have : Store.electraAt c slot = false := by simpa [h2] using he
      simp [*]; rfl

theorem Agrees.nextGindex {slot : Nat} (hs : slot < 2 ^ 64) :
    Store.nextGindex c slot = next_sync_committee_gindex_at_slot cfg slot := by
  unfold Store.nextGindex next_sync_committee_gindex_at_slot
  have hg := hA.gloas slot hs
  have he := hA.electra slot hs
  by_cases h1 : cfg.GLOAS_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot
  · simp [hg.mpr h1, h1]; rfl
  · have : c.gloasAt slot = false := by simpa [h1] using hg
    by_cases h2 : cfg.ELECTRA_FORK_EPOCH ≤ compute_epoch_at_slot cfg slot
    · simp [this, h1, he.mpr h2, h2]; rfl
    · have : Store.electraAt c slot = false := by simpa [h2] using he
      simp [*]; rfl

theorem Agrees.committeeRoot (sc : Ssz.SyncCommittee) :
    Store.committeeRoot c.preset sc = hash_tree_root_sync_committee cfg sc := by
  simp [Store.committeeRoot, hash_tree_root_sync_committee, hA.committeeDepth]

theorem Agrees.signers (u : Update) :
    u.signers c.preset = get_set_bit_count cfg u.aggregate.bits := by
  simp [Update.signers, Store.popcount, get_set_bit_count, hA.committeeSize]; rfl

end Agrees

/-- **Mainnet's table agrees with its configuration.** -/
theorem agrees_mainnet : Agrees Forks.mainnet mainnet where
  slotsPerEpoch := rfl
  epochsPerPeriod := rfl
  committeeSize := rfl
  committeeDepth := by decide
  sizePos := by decide
  minParticipants := by decide
  version := by
    intro slot v hs h
    have h3 : ¬ 18446744073709551615 ≤ slot / 32 := by omega
    simp only [Chain.versionAt, Chain.forkAt, Chain.epochAt, Forks.mainnet, Forks.mainnetPreset,
      List.filter_cons, List.filter_nil] at h
    simp only [compute_fork_version, compute_epoch_at_slot, mainnet, FAR_FUTURE_EPOCH]
    by_cases h1 : 364032 ≤ slot / 32 <;> by_cases h2 : 411392 ≤ slot / 32 <;>
      simp [h1, h2, h3] at h ⊢ <;> first | omega | (subst h; rfl)
  gloas := by
    intro slot hs
    simp [Chain.gloasAt, Chain.gloasEpoch, Forks.mainnet, mainnet, FAR_FUTURE_EPOCH,
      compute_epoch_at_slot]
    omega
  electra := by
    intro slot hs
    simp [Store.electraAt, Chain.epochOf, Forks.mainnet, mainnet, compute_epoch_at_slot,
      Chain.epochAt, Forks.mainnetPreset]
  fork := by
    intro slot f hs h
    simp only [Chain.forkOfSlot, Chain.forkNameAt, Chain.forkAt, Chain.epochAt, Forks.mainnet,
      Forks.mainnetPreset, List.filter_cons, List.filter_nil] at h
    simp only [compute_epoch_at_slot, mainnet, FAR_FUTURE_EPOCH]
    by_cases h1 : 364032 ≤ slot / 32 <;> by_cases h2 : 411392 ≤ slot / 32 <;>
      simp [h1, h2] at h <;> (try subst h) <;> refine ⟨by omega, by omega, ?_⟩ <;> simp <;> omega

/-- **Sepolia's table agrees with its configuration.** -/
theorem agrees_sepolia : Agrees Forks.sepolia sepolia where
  slotsPerEpoch := rfl
  epochsPerPeriod := rfl
  committeeSize := rfl
  committeeDepth := by decide
  sizePos := by decide
  minParticipants := by decide
  version := by
    intro slot v hs h
    simp only [Chain.versionAt, Chain.forkAt, Chain.epochAt, Forks.sepolia, Forks.mainnetPreset,
      List.filter_cons, List.filter_nil] at h
    simp only [compute_fork_version, compute_epoch_at_slot, sepolia]
    by_cases h1 : 222464 ≤ slot / 32 <;> by_cases h2 : 272640 ≤ slot / 32 <;>
      by_cases h4 : 353024 ≤ slot / 32 <;>
      simp [h1, h2, h4] at h ⊢ <;> first | omega | (subst h; rfl)
  gloas := by
    intro slot hs
    simp only [Chain.gloasAt, Forks.gloas_epochs.1, sepolia, compute_epoch_at_slot]
    simp only [Chain.epochAt, Forks.sepolia, Forks.mainnetPreset]
    exact decide_eq_true_iff
  electra := by
    intro slot hs
    simp [Store.electraAt, Chain.epochOf, Forks.sepolia, sepolia, compute_epoch_at_slot,
      Chain.epochAt, Forks.mainnetPreset]
  fork := by
    intro slot f hs h
    simp only [Chain.forkOfSlot, Chain.forkNameAt, Chain.forkAt, Chain.epochAt, Forks.sepolia,
      Forks.mainnetPreset, List.filter_cons, List.filter_nil] at h
    simp only [compute_epoch_at_slot, sepolia]
    by_cases h1 : 222464 ≤ slot / 32 <;> by_cases h2 : 272640 ≤ slot / 32 <;>
      by_cases h4 : 353024 ≤ slot / 32 <;>
      simp [h1, h2, h4] at h <;> (try subst h) <;> refine ⟨by omega, by omega, ?_⟩ <;> simp <;> omega

/-! ## Merkle branches -/

theorem testBit_mod {g d i : Nat} (hi : i < d) :
    (g % 2 ^ d / 2 ^ i % 2 == 1) = g.testBit i := by
  have h1 : (g % 2 ^ d).testBit i = g.testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [Nat.testBit_eq_decide_div_mod_eq] at h1
  rw [← h1]
  cases h : g % 2 ^ d / 2 ^ i % 2 == 1 <;> simp_all

/-- One step of phase0's `is_valid_merkle_branch` loop. -/
def mstep (br : Array ByteArray) (index : Nat) (value : ByteArray) (i : Nat) : Option ByteArray :=
  br[i]?.bind fun b => some (if index / 2 ^ i % 2 == 1 then Ssz.hash64 b value else Ssz.hash64 value b)

/-- The runtime's climb is phase0's loop, on the branch past its leading extra roots. -/
theorem climb_foldlM (g : Nat) (branch : Array ByteArray) (start d : Nat) :
    ∀ n level node, start + level + n ≤ branch.size → level + n ≤ d →
      (List.range' level n).foldlM (mstep (branch.extract start branch.size) (g % 2 ^ d)) node =
        some (Ssz.climb g branch start n level node)
  | 0, _, _, _, _ => rfl
  | n + 1, level, node, hb, hd => by
    rw [List.range'_succ, List.foldlM_cons]
    have hget : (branch.extract start branch.size)[level]? = some branch[start + level] := by
      rw [Array.getElem?_extract, Nat.min_self]
      split
      · exact Array.getElem?_eq_getElem (by omega)
      · omega
    have hs : mstep (branch.extract start branch.size) (g % 2 ^ d) node level =
        some (if g.testBit level then Ssz.hash64 branch[start + level] node
          else Ssz.hash64 node branch[start + level]) := by
      simp only [mstep, hget, Option.bind_some, testBit_mod (by omega : level < d)]
    rw [hs, Option.bind_eq_bind, Option.bind_some,
      climb_foldlM g branch start d n (level + 1) _ (by omega) (by omega)]
    simp only [Ssz.climb, Array.getElem?_eq_getElem (by omega : start + level < branch.size),
      Option.getD_some]

theorem data_beq {a b : ByteArray} (h : (a.data == b.data) = true) : a = b := by
  cases a; cases b; simp_all

/-- **A branch leanLight accepts, `is_valid_normalized_merkle_branch` accepts.** -/
theorem normalized_of_runtime {leaf root : ByteArray} {branch : Array ByteArray} {g : Nat}
    (h : Ssz.isValidNormalizedBranch leaf branch g root = true) :
    is_valid_normalized_merkle_branch leaf branch g root = true := by
  simp only [Ssz.isValidNormalizedBranch, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hd⟩, -⟩, -⟩, hz⟩, hr⟩ := h
  simp only [is_valid_normalized_merkle_branch, floorlog2, get_subtree_index, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [Array.all_eq_true] at hz
    have hsz : i < (branch.extract 0 (branch.size - g.log2)).size := by simp; omega
    have := hz i hsz
    simp only [Array.getElem_extract, Nat.zero_add] at this
    simp only [isZero, Array.getElem?_eq_getElem (by omega : i < branch.size), Option.getD_some]
    exact this
  · have := climb_foldlM g branch (branch.size - g.log2) g.log2 g.log2 0 leaf (by omega) (by omega)
    show (match (List.range g.log2).foldlM (mstep _ _) leaf with
      | some value => decide (value = root) | none => false) = true
    rw [List.range_eq_range', this]
    simp [data_beq hr]

/-- On a branch exactly as deep as the gindex, `is_valid_normalized_merkle_branch` is
`is_valid_merkle_branch` at the gindex's depth and subtree index. -/
theorem normalized_exact {leaf root : ByteArray} {branch : Array ByteArray} {g : Nat}
    (hs : branch.size = floorlog2 g)
    (h : is_valid_normalized_merkle_branch leaf branch g root = true) :
    is_valid_merkle_branch leaf branch (floorlog2 g) (get_subtree_index g) root = true := by
  simp only [is_valid_normalized_merkle_branch, Bool.and_eq_true] at h
  rw [hs, Nat.sub_self] at h
  have he : branch.extract 0 (floorlog2 g) = branch := by
    rw [← hs]; exact Array.extract_size
  rw [he] at h
  exact h.2

/-! ## Empty values, flags and counts -/

theorem isZero_eq (b : ByteArray) : Store.isZero b = isZero b := rfl

theorem isEmpty_eq (h : Header) : h.isEmpty = (ofHeader h).isEmpty := by
  unfold Header.isEmpty ofHeader LightClientHeader.isEmpty Store.allZero
  cases h.exec <;> rfl

theorem committeeEmpty_eq (sc : Ssz.SyncCommittee) :
    Store.committeeEmpty sc = SyncCommittee.isEmpty sc := rfl

theorem isSync_eq (u : Update) : is_sync_committee_update (ofUpdate u) = u.isSyncCommitteeUpdate :=
  rfl

theorem isFinality_eq (u : Update) : is_finality_update (ofUpdate u) = u.isFinalityUpdate := rfl

theorem participants_eq {cfg : Config} (bits : ByteArray) (pubkeys : Array ByteArray)
    (hs : pubkeys.size = cfg.SYNC_COMMITTEE_SIZE) :
    participant_pubkeys cfg bits pubkeys = some (Store.participants pubkeys bits) := by
  simp only [participant_pubkeys, hs, Store.participants, bitAt, Store.bit, Bytes.byteAt]
  rfl


/-! ## `is_better_update` -/

/-- `Store.rank`'s keys, over the values they read. -/
def rankOf (sm : Bool) (n : Nat) (rel f scf : Bool) (x y : Nat) : List Int :=
  [if sm then 1 else 0, if sm then 0 else n, if rel then 1 else 0, if f then 1 else 0,
    if (f && scf) then 1 else 0, n, -x, -y]

/-- `is_better_update`'s comparisons, over the values they read. -/
def betterOf (sma smb : Bool) (n m : Nat) (rela relb fa fb scfa scfb : Bool) (xa ya xb yb : Nat) : Bool :=
  if sma ≠ smb then sma
  else if !sma ∧ n ≠ m then n > m
  else if rela ≠ relb then rela
  else if fa ≠ fb then fa
  else if fa ∧ scfa ≠ scfb then scfa
  else if n ≠ m then n > m
  else if xa ≠ xb then xa < xb
  else ya < yb

theorem lex_eq {a b : Int} {as bs : List Int} (h : a = b) :
    Store.lexGtB (a :: as) (b :: bs) = Store.lexGtB as bs := by simp [Store.lexGtB, h]

theorem lex_ne {a b : Int} {as bs : List Int} (h : a ≠ b) :
    Store.lexGtB (a :: as) (b :: bs) = decide (b < a) := by simp [Store.lexGtB, h]

theorem flag_eq {p q : Bool} : ((if p then (1 : Int) else 0) = if q then 1 else 0) ↔ p = q := by
  cases p <;> cases q <;> simp

theorem flag_lt {p q : Bool} (h : p ≠ q) :
    decide ((if q then (1 : Int) else 0) < if p then 1 else 0) = p := by
  cases p <;> cases q <;> simp_all

theorem tail (n m : Nat) (xa ya xb yb : Nat) :
    Store.lexGtB [(n : Int), -xa, -ya] [(m : Int), -xb, -yb] =
      (if n ≠ m then decide (n > m) else if xa ≠ xb then decide (xa < xb) else decide (ya < yb)) := by
  by_cases h1 : n = m
  · subst h1
    rw [lex_eq rfl]
    by_cases h2 : xa = xb
    · subst h2
      rw [lex_eq rfl]
      by_cases h3 : ya = yb
      · subst h3; simp [Store.lexGtB]
      · rw [lex_ne (by omega)]; simp
    · rw [lex_ne (by omega)]; simp [h2]
  · rw [lex_ne (by omega)]; simp [h1]

theorem key2 (sma : Bool) (n m : Nat) (rest rest' : List Int) :
    Store.lexGtB ((if sma then (0 : Int) else n) :: rest) ((if sma then (0 : Int) else m) :: rest') =
      if !sma ∧ n ≠ m then decide (n > m) else Store.lexGtB rest rest' := by
  cases sma
  · by_cases h : n = m
    · subst h; rw [lex_eq rfl]; simp
    · rw [lex_ne (by simp; omega)]; simp [h]
  · rw [lex_eq (by simp)]; simp

/-- The lexicographic order on `rankOf` is `betterOf`, key by key. -/
theorem core (sma smb : Bool) (n m : Nat) (rela relb fa fb scfa scfb : Bool) (xa ya xb yb : Nat) :
    Store.lexGtB (rankOf sma n rela fa scfa xa ya) (rankOf smb m relb fb scfb xb yb) =
      betterOf sma smb n m rela relb fa fb scfa scfb xa ya xb yb := by
  unfold rankOf betterOf
  by_cases h1 : sma = smb
  · subst h1
    rw [lex_eq rfl, key2]
    conv_rhs => rw [if_neg (by simp)]
    by_cases h2 : (!sma) = true ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : rela = relb
      · subst h3
        rw [lex_eq rfl]
        conv_rhs => rw [if_neg (by simp)]
        by_cases h4 : fa = fb
        · subst h4
          rw [lex_eq rfl]
          conv_rhs => rw [if_neg (by simp)]
          by_cases h5 : fa = true ∧ scfa ≠ scfb
          · obtain ⟨hf, h5⟩ := h5
            subst hf
            rw [lex_ne (by rw [Ne, flag_eq]; simpa using h5)]
            conv_rhs => rw [if_pos ⟨rfl, h5⟩]
            simpa using flag_lt (p := scfa) (q := scfb) h5
          · rw [lex_eq (by rw [flag_eq]; cases fa <;> simp_all), tail]
            conv_rhs => rw [if_neg h5]
        · rw [lex_ne (by rw [Ne, flag_eq]; exact h4), flag_lt h4]
          conv_rhs => rw [if_pos h4]
      · rw [lex_ne (by rw [Ne, flag_eq]; exact h3), flag_lt h3]
        conv_rhs => rw [if_pos h3]
  · rw [lex_ne (by rw [Ne, flag_eq]; exact h1), flag_lt h1]
    conv_rhs => rw [if_pos h1]


/-- **`isBetter` is `is_better_update`.** -/
theorem isBetter_spec {c : Chain} {cfg : Config} (hA : Agrees c cfg) (a b : Update) :
    Store.isBetter c a b = is_better_update cfg (ofUpdate a) (ofUpdate b) := by
  have hr : ∀ u : Update, Store.rank c u = rankOf (Store.supermajority c.preset (u.signers c.preset))
      (u.signers c.preset) (u.isSyncCommitteeUpdate && c.periodAt u.slot == c.periodAt u.signatureSlot)
      u.isFinalityUpdate (c.periodAt u.finalized.beacon.slot == c.periodAt u.slot) u.slot
      u.signatureSlot := fun u => rfl
  rw [Store.isBetter, hr, hr, core]
  unfold betterOf is_better_update
  simp only [hA.signers, hA.periodAt, Store.supermajority, hA.committeeSize, ofUpdate_aggregate,
    ofUpdate_attested, ofUpdate_finalized, ofUpdate_signatureSlot, ofHeader_beacon, isSync_eq,
    isFinality_eq, Update.slot]
  simp only [Bool.and_eq_true, Nat.mul_comm 3, Nat.mul_comm 2, ge_iff_le, Bool.decide_and,
    ← beq_eq_decide, beq_true]
  rfl

/-! ## Headers -/

/-- **A header leanLight accepts, `is_valid_light_client_header` accepts**, for a `uint64` slot. -/
theorem isValidHeader_spec {c : Chain} {cfg : Config} (hA : Agrees c cfg) {h : Header}
    (hs : h.beacon.slot < 2 ^ 64) (hv : Store.isValidHeader c h = true) :
    is_valid_light_client_header cfg (ofHeader h) = true := by
  unfold Store.isValidHeader at hv
  cases hf : c.forkOfSlot h.beacon.slot with
  | none => rw [hf] at hv; cases hv
  | some f =>
    rw [hf] at hv
    obtain ⟨hcap, hden, hgl⟩ := hA.fork _ f hs hf
    unfold ofHeader
    cases he : h.exec with
    | payload e =>
      rw [he] at hv
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hv
      obtain ⟨⟨-, hsz⟩, hb⟩ := hv
      simp only [is_valid_light_client_header, get_lc_execution_root_electra]
      rw [if_neg (fun h' => absurd (of_decide_eq_true (Bool.and_eq_true _ _ ▸ h').1) (by omega)),
        if_neg (by omega), if_pos hden]
      exact normalized_exact hsz (normalized_of_runtime hb)
    | blockHash b =>
      rw [he] at hv
      dsimp only at hv
      simp only [is_valid_light_client_header]
      by_cases hg : cfg.GLOAS_FORK_EPOCH ≤ compute_epoch_at_slot cfg h.beacon.slot
      · rw [if_pos hg]
        have : f = .gloas := hgl.mpr hg
        subst this
        exact normalized_of_runtime hv
      · rw [if_neg hg, if_pos hden]
        have : f ≠ .gloas := fun h' => hg (hgl.mp h')
        have hf' : (f == .gloas) = false := by simpa using this
        rw [hf'] at hv
        exact normalized_of_runtime hv

/-! ## The signature -/

/-- **A committee as the chain holds one**: every key passes KeyValidate (so is a point of G1
other than the identity), and the aggregate key decodes to their sum (`Committee.Consistent`). -/
def Valid (com : Committee) : Prop :=
  ∃ keys, com.pubkeys.mapM Bls.keyValidate? = some keys ∧ com.Consistent keys

theorem mapM_weaken {α β : Type} {f g : α → Option β} (hfg : ∀ a b, f a = some b → g a = some b) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.mapM g = some l'
  | [], l', h => by simpa using h
  | a :: l, l', h => by
    rw [List.mapM_cons] at h ⊢
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some t =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
        rw [hfg a b ha, mapM_weaken hfg hl]
        simpa using h

/-- Keys that pass KeyValidate are a consistent committee's when the aggregate is their sum: the
form the chain gives, stated from KeyValidate. -/
theorem Valid.of_keyValidate {com : Committee} {keys : Array Bls.G1A}
    (hk : com.pubkeys.mapM Bls.keyValidate? = some keys)
    (ha : ∃ a, Bls.g1Decompress? com.aggregate = some a ∧
      WeierstrassCurve.Jacobian.Point.toAffine Bls.E1 a.toJ =
        (keys.toList.map fun p => WeierstrassCurve.Jacobian.Point.toAffine Bls.E1 p.toJ).sum) :
    Valid com := by
  refine ⟨keys, hk, ?_, ?_, ha⟩
  · rw [Array.mapM_eq_mapM_toList] at hk ⊢
    cases hl : com.pubkeys.toList.mapM Bls.keyValidate? with
    | none => simp [hl] at hk
    | some l =>
      rw [mapM_weaken (fun a b h => (Bls.keyValidate?_some h).1) hl]
      simpa [hl] using hk
  · intro p hp
    have hl := Store.toList_of_mapM hk
    obtain ⟨-, hi⟩ := Store.getElem?_of_mapM hl
    obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
    rw [hi i] at hpi
    cases hb : com.pubkeys.toList[i]? with
    | none => rw [hb] at hpi; cases hpi
    | some b =>
      rw [hb, Option.bind_some] at hpi
      exact (Bls.keyValidate?_some hpi).2.2.2.2

/-- **The signature check that runs is the specification's**, on a committee as the chain holds
one: when leanLight's check (the aggregate key less the absent keys) passes, the participants'
keys (`zip(bits, pubkeys, strict=True)`) pass `FastAggregateVerify` (KeyValidate on each, then the
aggregate check) over the signing root of the attested header under the fork version of
`compute_fork_version(compute_epoch_at_slot(saturating_sub(signature_slot, 1)))`. -/
theorem verifySignature_spec {c : Chain} {cfg : Config} (hA : Agrees c cfg) {com : Committee}
    (hV : Valid com) (hsize : com.pubkeys.size = cfg.SYNC_COMMITTEE_SIZE) {u : Update}
    (hs : u.signatureSlot < 2 ^ 64) (h : Store.verifySignature c com u = true) :
    ∃ ps, participant_pubkeys cfg u.aggregate.bits com.pubkeys = some ps ∧
      Bls.fastAggregateVerifyBytes ps
        (Forks.signingRoot (ofHeader u.attested).beacon.root
          (Forks.computeDomain DOMAIN_SYNC_COMMITTEE
            (compute_fork_version cfg (compute_epoch_at_slot cfg (saturating_sub u.signatureSlot 1)))
            c.genesisValidatorsRoot))
        u.aggregate.signature = true := by
  obtain ⟨keys, hk, hc⟩ := hV
  refine ⟨_, participants_eq _ _ hsize, ?_⟩
  unfold Store.verifySignature at h
  cases hv : c.signatureVersion u.signatureSlot with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    have hv' : v = compute_fork_version cfg (compute_epoch_at_slot cfg (u.signatureSlot - 1)) :=
      hA.version _ v (by omega) hv
    rw [Store.signersKey?_eq hc] at h
    have hl := Store.toList_of_mapM hk
    obtain ⟨hlen, -⟩ := Store.getElem?_of_mapM hl
    have hm := Store.mapM_select hl (Store.bit u.aggregate.bits) (List.range com.pubkeys.toList.length)
    have hp : (Store.participants com.pubkeys u.aggregate.bits).mapM Bls.keyValidate? =
        some (Store.participants keys u.aggregate.bits) := by
      rw [Array.mapM_eq_mapM_toList, Store.participants_toList, hm]
      have : Store.participants keys u.aggregate.bits = ((List.range com.pubkeys.toList.length).filterMap
          fun i => if Store.bit u.aggregate.bits i then keys.toList[i]? else none).toArray := by
        apply Array.toList_inj.mp
        rw [Store.participants_toList, hlen, List.toList_toArray]
      rw [this]
      rfl
    unfold Bls.fastAggregateVerifyBytes
    rw [hp]
    simp only [Bls.fastAggregateVerify, ofHeader_beacon, saturating_sub, ← hv']
    exact h

/-! ## The stores -/

/-- **leanLight's store holds what the specification's store holds**: the finalized header, the
current committee (of the preset's size), the next committee (none held exactly when the
specification's is `SyncCommittee.empty()`), the best valid update, the optimistic header and the
participation counters. -/
structure Sim (cfg : Config) (s : Store.Store) (S : LightClientStore) : Prop where
  finalized : S.finalized_header = ofHeader s.finalized
  current : S.current_sync_committee = ofCommittee s.current
  currentSize : s.current.pubkeys.size = cfg.SYNC_COMMITTEE_SIZE
  nextNone : s.next = none → SyncCommittee.isEmpty S.next_sync_committee = true
  nextSome : ∀ n, s.next = some n → S.next_sync_committee = ofCommittee n ∧
    SyncCommittee.isEmpty (ofCommittee n) = false ∧ n.pubkeys.size = cfg.SYNC_COMMITTEE_SIZE
  best : S.best_valid_update = s.best.map ofUpdate
  optimistic : S.optimistic_header = ofHeader s.optimistic
  previous : S.previous_max_active_participants = s.previousMaxActive
  currentMax : S.current_max_active_participants = s.currentMaxActive

/-- Two stores of leanLight that hold the same as the specification's store. -/
structure SameSpec (s' s : Store.Store) : Prop where
  finalized : s'.finalized = s.finalized
  current : s'.current = s.current
  next : s'.next = s.next
  best : s'.best = s.best
  optimistic : s'.optimistic = s.optimistic
  previous : s'.previousMaxActive = s.previousMaxActive
  currentMax : s'.currentMaxActive = s.currentMaxActive

theorem SameSpec.trans {a b d : Store.Store} (h1 : SameSpec a b) (h2 : SameSpec b d) :
    SameSpec a d :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2, h1.3.trans h2.3, h1.4.trans h2.4, h1.5.trans h2.5,
    h1.6.trans h2.6, h1.7.trans h2.7⟩

theorem Sim.congr {cfg : Config} {s s' : Store.Store} {S : LightClientStore}
    (h : SameSpec s' s) (hs : Sim cfg s S) : Sim cfg s' S :=
  ⟨h.finalized ▸ hs.finalized, h.current ▸ hs.current, h.current ▸ hs.currentSize,
    h.next ▸ hs.nextNone, h.next ▸ hs.nextSome, h.best ▸ hs.best, h.optimistic ▸ hs.optimistic,
    h.previous ▸ hs.previous, h.currentMax ▸ hs.currentMax⟩

theorem Sim.known {cfg : Config} {s : Store.Store} {S : LightClientStore} (hs : Sim cfg s S) :
    is_next_sync_committee_known S = s.next.isSome := by
  unfold is_next_sync_committee_known
  cases hn : s.next with
  | none => simp [hs.nextNone hn]
  | some n => simp [(hs.nextSome n hn).1, (hs.nextSome n hn).2.1]

theorem Sim.period {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) :
    compute_sync_committee_period_at_slot cfg S.finalized_header.beacon.slot = Store.period c s := by
  rw [hs.finalized, ofHeader_beacon, Store.period, hA.periodAt]

theorem ofCommittee_ofSync {p : Forks.Preset} {sc : Ssz.SyncCommittee} {n : Committee}
    (h : Committee.ofSync p sc = some n) : ofCommittee n = sc := by
  obtain ⟨-, h1, h2, -⟩ := Store.ofSync_keys h
  cases sc; simp [ofCommittee, h1, h2]

/-- What `learn` takes in is what the specification sets as the next committee. -/
theorem learn_sim {c : Chain} {cfg : Config} (hA : Agrees c cfg) {u : Update}
    {nc : Option Committee} (h : Store.learn c u = some nc) :
    (nc = none → SyncCommittee.isEmpty u.next = true) ∧
      ∀ n, nc = some n → u.next = ofCommittee n ∧ SyncCommittee.isEmpty (ofCommittee n) = false ∧
        n.pubkeys.size = cfg.SYNC_COMMITTEE_SIZE := by
  unfold Store.learn at h
  split at h
  · rename_i he
    cases h
    exact ⟨fun _ => he, fun n hn => by cases hn⟩
  · rename_i he
    cases hn : Committee.ofSync c.preset u.next with
    | none => rw [hn] at h; cases h
    | some n =>
    rw [hn] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨fun h' => absurd h' (by simp), fun n' hn' => ?_⟩
    obtain rfl : n = n' := Option.some.inj hn'
    have := ofCommittee_ofSync hn
    refine ⟨this.symm, by rw [this, ← committeeEmpty_eq]; simpa using he, ?_⟩
    rw [(Store.ofSync_keys hn).2.1, (Store.ofSync_keys hn).1, hA.committeeSize]

/-- **`apply` is `apply_light_client_update`** (then `best_valid_update = None`), when it
accepts. -/
theorem apply_sim {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) {u : Update} {a l : Bool}
    (hacc : (Store.apply c s u).2 = .accepted a l) :
    ∃ S', apply_light_client_update cfg S (ofUpdate u) = some S' ∧
      Sim cfg (Store.apply c s u).1 { S' with best_valid_update := none } := by
  have hp := hs.period hA
  have hk := hs.known
  have hfp : compute_sync_committee_period_at_slot cfg u.finalized.beacon.slot =
      c.periodAt u.finalized.beacon.slot := (hA.periodAt _).symm
  have hF : S.finalized_header.beacon.slot = s.finalized.beacon.slot := by
    rw [hs.finalized, ofHeader_beacon]
  have hO : S.optimistic_header.beacon.slot = s.optimistic.beacon.slot := by
    rw [hs.optimistic, ofHeader_beacon]
  cases hn : s.next with
  | none =>
    by_cases h1 : c.periodAt u.finalized.beacon.slot = Store.period c s
    · cases hl : Store.learn c u with
      | none => simp [Store.apply, hn, h1, hl] at hacc
      | some nc =>
        obtain ⟨hl1, hl2⟩ := learn_sim hA hl
        have hp' : compute_sync_committee_period_at_slot cfg s.finalized.beacon.slot =
            Store.period c s := by rw [Store.period, hA.periodAt]
        by_cases hlt : s.finalized.beacon.slot < u.finalized.beacon.slot <;>
        by_cases hlo : s.optimistic.beacon.slot < u.finalized.beacon.slot <;>
        · simp only [Store.apply, apply_light_client_update, hn, h1, hl, hk, hp, hp', hfp, hF, hO, hlt,
            hlo, require, ofUpdate_finalized, ofHeader_beacon, Option.isSome_none, Bool.not_false,
            decide_true, ite_true, ite_false, gt_iff_lt, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, exists_eq_left', Bool.false_eq_true, Nat.lt_irrefl,
            not_false_eq_true, ite_true, ite_false]
          exact
            { finalized := by simp [hs.finalized]
              current := by simp [hs.current]
              currentSize := by simpa using hs.currentSize
              nextNone := fun h => by simpa [h] using hl1 h
              nextSome := fun n h => by simpa using hl2 n h
              best := rfl
              optimistic := by simp [hs.optimistic]
              previous := by simpa using hs.previous
              currentMax := by simpa using hs.currentMax }
    · simp [Store.apply, hn, h1] at hacc
  | some n =>
    obtain ⟨hn1, hn2, hn3⟩ := hs.nextSome n hn
    have hp' : compute_sync_committee_period_at_slot cfg s.finalized.beacon.slot =
        Store.period c s := by rw [Store.period, hA.periodAt]
    by_cases h1 : c.periodAt u.finalized.beacon.slot = Store.period c s + 1
    · cases hl : Store.learn c u with
      | none => simp [Store.apply, hn, h1, hl] at hacc
      | some nc =>
        obtain ⟨hl1, hl2⟩ := learn_sim hA hl
        by_cases hlt : s.finalized.beacon.slot < u.finalized.beacon.slot <;>
        by_cases hlo : s.optimistic.beacon.slot < u.finalized.beacon.slot <;>
        · simp only [Store.apply, apply_light_client_update, hn, h1, hl, hk, hp, hp', hfp, hF, hO,
            hlt, hlo, require, ofUpdate_finalized, ofHeader_beacon, Option.isSome_some, Bool.not_true,
            ite_true, ite_false, gt_iff_lt, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq, exists_eq_left', Bool.false_eq_true, Nat.lt_irrefl,
            not_false_eq_true, ite_true, ite_false]
          exact
            { finalized := by simp [hs.finalized]
              current := by simp [hn1]
              currentSize := by simpa using hn3
              nextNone := fun h => by simpa [h] using hl1 h
              nextSome := fun n h => by simpa using hl2 n h
              best := rfl
              optimistic := by simp [hs.optimistic]
              previous := by simpa using hs.currentMax
              currentMax := rfl }
    · by_cases hlt : s.finalized.beacon.slot < u.finalized.beacon.slot <;>
      by_cases hlo : s.optimistic.beacon.slot < u.finalized.beacon.slot <;>
      · simp only [Store.apply, apply_light_client_update, hn, h1, hk, hp, hp', hfp, hF, hO,
          hlt, hlo, require, ofUpdate_finalized, ofHeader_beacon, Option.isSome_some, Bool.not_true,
          ite_true, ite_false, gt_iff_lt, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, exists_eq_left', Bool.false_eq_true, Nat.lt_irrefl,
          not_false_eq_true, ite_true, ite_false]
        exact
          { finalized := by simp [hs.finalized]
            current := by simp [hs.current]
            currentSize := by simpa using hs.currentSize
            nextNone := fun h => by simp [hn] at h
            nextSome := fun n' h => by simp [hn] at h; subst h; simpa using hs.nextSome n hn
            best := rfl
            optimistic := by simp [hs.optimistic]
            previous := by simpa using hs.previous
            currentMax := by simpa using hs.currentMax }

/-! ## `process_light_client_update` -/

/-- What `process_light_client_update` does to the store before deciding whether to apply: the
best update, the participation counter, the optimistic header. -/
def trackS (cfg : Config) (store : LightClientStore) (update : LightClientUpdate) :
    LightClientStore :=
  let store := match store.best_valid_update with
    | none => { store with best_valid_update := some update }
    | some best => if is_better_update cfg update best then
        { store with best_valid_update := some update } else store
  let store := { store with
    current_max_active_participants :=
      max store.current_max_active_participants (get_set_bit_count cfg update.sync_aggregate.bits) }
  if get_set_bit_count cfg update.sync_aggregate.bits > get_safety_threshold store ∧
      update.attested_header.beacon.slot > store.optimistic_header.beacon.slot then
    { store with optimistic_header := update.attested_header }
  else store

/-- `process_light_client_update` once `validate_light_client_update` passed. -/
theorem process_eq {cfg : Config} {S : LightClientStore} {U : LightClientUpdate} {slot : Nat}
    {gvr : ByteArray} (h : validate_light_client_update cfg S U slot gvr = some ()) :
    process_light_client_update cfg S U slot gvr =
      let S1 := trackS cfg S U
      if get_set_bit_count cfg U.sync_aggregate.bits * 3 ≥ cfg.SYNC_COMMITTEE_SIZE * 2 ∧
          (U.finalized_header.beacon.slot > S1.finalized_header.beacon.slot ∨
            (!is_next_sync_committee_known S1 && is_sync_committee_update U &&
              is_finality_update U &&
              compute_sync_committee_period_at_slot cfg U.finalized_header.beacon.slot ==
                compute_sync_committee_period_at_slot cfg U.attested_header.beacon.slot) = true) then
        (apply_light_client_update cfg S1 U).bind fun st => some { st with best_valid_update := none }
      else some S1 := by
  unfold process_light_client_update
  rw [h]
  rfl

theorem moveAnchor_same (c : Chain) (s : Store.Store) (u : Update) :
    SameSpec (Store.moveAnchor c s u) s := by
  unfold Store.moveAnchor
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `process_light_client_update`'s choice of the best update. -/
def bestS (cfg : Config) (store : LightClientStore) (update : LightClientUpdate) :
    LightClientStore :=
  match store.best_valid_update with
  | none => { store with best_valid_update := some update }
  | some best => if is_better_update cfg update best then
      { store with best_valid_update := some update } else store

/-- The specification's store with the current participation counter raised to `n`. -/
def bumpS (store : LightClientStore) (n : Nat) : LightClientStore :=
  { store with current_max_active_participants := max store.current_max_active_participants n }

/-- leanLight's store with the current participation counter raised to `n`. -/
def bumpR (s : Store.Store) (n : Nat) : Store.Store :=
  { s with currentMaxActive := max s.currentMaxActive n }

theorem trackS_eq (cfg : Config) (S : LightClientStore) (U : LightClientUpdate) :
    trackS cfg S U =
      let S2 := bumpS (bestS cfg S U) (get_set_bit_count cfg U.sync_aggregate.bits)
      if get_set_bit_count cfg U.sync_aggregate.bits > get_safety_threshold S2 ∧
          U.attested_header.beacon.slot > S2.optimistic_header.beacon.slot then
        { S2 with optimistic_header := U.attested_header }
      else S2 := rfl

theorem track_eq (c : Chain) (s : Store.Store) (u : Update) :
    Store.track c s u =
      let s2 := bumpR (Store.keepBest c s u) (u.signers c.preset)
      if decide (Store.safetyThreshold s2 < u.signers c.preset) &&
          decide (s2.optimistic.beacon.slot < u.slot) then
        { s2 with optimistic := u.attested }
      else s2 := rfl

/-- `track` is the specification's first steps of `process_light_client_update`. -/
theorem track_sim {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) (u : Update) :
    Sim cfg (Store.track c s u) (trackS cfg S (ofUpdate u)) := by
  have hb : ∀ b, is_better_update cfg (ofUpdate u) (ofUpdate b) = Store.isBetter c u b :=
    fun b => (isBetter_spec hA u b).symm
  have h1 : Sim cfg (Store.keepBest c s u) (bestS cfg S (ofUpdate u)) := by
    unfold bestS Store.keepBest
    rw [hs.best]
    cases hbs : s.best with
    | none => exact { hs with best := by simp }
    | some b =>
      simp only [Option.map_some, hb]
      by_cases hbt : Store.isBetter c u b = true
      · simp only [hbt, ite_true, Option.getD_some]
        exact { hs with best := by simp }
      · simp only [hbt, Bool.false_eq_true, ite_false, Option.getD_some]
        exact { hs with best := by simp [hs.best, hbs] }
  have hn : get_set_bit_count cfg (ofUpdate u).sync_aggregate.bits = u.signers c.preset := by
    rw [ofUpdate_aggregate, hA.signers]
  have h2 : Sim cfg (bumpR (Store.keepBest c s u) (u.signers c.preset))
      (bumpS (bestS cfg S (ofUpdate u)) (u.signers c.preset)) :=
    { h1 with currentMax := by simp [bumpR, bumpS, h1.currentMax] }
  have hth : get_safety_threshold (bumpS (bestS cfg S (ofUpdate u)) (u.signers c.preset)) =
      Store.safetyThreshold (bumpR (Store.keepBest c s u) (u.signers c.preset)) := by
    simp [get_safety_threshold, Store.safetyThreshold, bumpR, bumpS, h1.previous, h1.currentMax]
  have hos : (bumpS (bestS cfg S (ofUpdate u)) (u.signers c.preset)).optimistic_header.beacon.slot =
      (bumpR (Store.keepBest c s u) (u.signers c.preset)).optimistic.beacon.slot := by
    rw [h2.optimistic, ofHeader_beacon]
  rw [trackS_eq, track_eq, hn]
  dsimp only
  by_cases hc : Store.safetyThreshold (bumpR (Store.keepBest c s u) (u.signers c.preset)) <
      u.signers c.preset ∧ (bumpR (Store.keepBest c s u) (u.signers c.preset)).optimistic.beacon.slot <
        u.attested.beacon.slot
  · rw [if_pos (by simp only [Bool.and_eq_true, Update.slot]; exact ⟨decide_eq_true hc.1,
        decide_eq_true hc.2⟩),
      if_pos (by simpa [hth, hos, ofUpdate_attested, ofHeader_beacon] using hc)]
    exact { h2 with optimistic := rfl }
  · rw [if_neg (by
        simp only [Bool.and_eq_true, Update.slot]
        exact fun h => hc ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩),
      if_neg (by simpa [hth, hos, ofUpdate_attested, ofHeader_beacon] using hc)]
    exact h2

/-- `apply` accepts, or `learn` refused the committee, or the store held no next committee and
the finalized header was not in its period. -/
theorem apply_verdict (c : Chain) (s : Store.Store) (u : Update) :
    (∃ a l, (Store.apply c s u).2 = .accepted a l) ∨ Store.learn c u = none ∨
      (s.next = none ∧ c.periodAt u.finalized.beacon.slot ≠ Store.period c s) := by
  unfold Store.apply
  cases hn : s.next with
  | none =>
    by_cases h1 : c.periodAt u.finalized.beacon.slot = Store.period c s
    · cases hl : Store.learn c u <;> simp [h1, hl]
    · exact .inr (.inr ⟨rfl, h1⟩)
  | some n =>
    by_cases h1 : c.periodAt u.finalized.beacon.slot = Store.period c s + 1
    · cases hl : Store.learn c u <;> simp [h1, hl]
    · simp [h1]

/-- `learn` takes in the committee of an update `formOk` passed. -/
theorem learn_isSome {c : Chain} {u : Update} (h : Store.formOk c u = true) :
    Store.learn c u ≠ none := by
  have hn := (Store.formOk_parts h).2.2.2.2.2
  unfold Store.learn
  split
  · simp
  · rename_i he
    have hs : u.isSyncCommitteeUpdate = true := by
      cases hsu : u.isSyncCommitteeUpdate
      · have := (Store.nextOk_empty hn).1 hsu
        simp [this] at he
      · rfl
    have hsz := ((Store.nextOk_empty hn).2 hs).1
    simp [Store.Committee.ofSync, hsz]

/-- **`process` is `process_light_client_update`** on an update `validate_light_client_update`
passes and leanLight's checks passed: the two stores agree after it, and leanLight accepts. -/
theorem process_sim {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) {u : Update} {slot : Nat} {gvr : ByteArray}
    (hval : validate_light_client_update cfg S (ofUpdate u) slot gvr = some ())
    (hform : Store.formOk c u = true)
    (hlive : c.periodAt u.signatureSlot = Store.period c s ∨
      (c.periodAt u.signatureSlot = Store.period c s + 1 ∧ s.next.isSome = true))
    (hrel : Store.relevant c s u = true) :
    ∃ S', process_light_client_update cfg S (ofUpdate u) slot gvr = some S' ∧
      Sim cfg (Store.process c s u).1 S' ∧ ∃ a l, (Store.process c s u).2 = .accepted a l := by
  rw [process_eq hval]
  have h1 : Sim cfg (Store.moveAnchor c (Store.track c s u) u) (trackS cfg S (ofUpdate u)) :=
    (track_sim hA hs u).congr (moveAnchor_same c _ u)
  have hf1 : (Store.moveAnchor c (Store.track c s u) u).finalized = s.finalized :=
    (Store.bested_frame c s u).1
  have hn1 : (Store.moveAnchor c (Store.track c s u) u).next = s.next :=
    (Store.bested_frame c s u).2.2.1
  have hcond : (Store.supermajority c.preset (u.signers c.preset) &&
      Store.applies c (Store.moveAnchor c (Store.track c s u) u) u) = true ↔
      (get_set_bit_count cfg (ofUpdate u).sync_aggregate.bits * 3 ≥ cfg.SYNC_COMMITTEE_SIZE * 2 ∧
        ((ofUpdate u).finalized_header.beacon.slot >
            (trackS cfg S (ofUpdate u)).finalized_header.beacon.slot ∨
          (!is_next_sync_committee_known (trackS cfg S (ofUpdate u)) &&
            is_sync_committee_update (ofUpdate u) && is_finality_update (ofUpdate u) &&
            compute_sync_committee_period_at_slot cfg (ofUpdate u).finalized_header.beacon.slot ==
              compute_sync_committee_period_at_slot cfg
                (ofUpdate u).attested_header.beacon.slot) = true)) := by
    rw [h1.known, h1.finalized]
    simp only [Store.supermajority, Store.applies, hf1, hn1, ofUpdate_aggregate, ofUpdate_finalized,
      ofUpdate_attested, ofHeader_beacon, ← hA.signers, ← hA.committeeSize, ← hA.periodAt,
      isSync_eq, isFinality_eq, Update.slot, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      ge_iff_le, gt_iff_lt]
    simp only [Option.isNone_iff_eq_none, Bool.not_eq_true', Option.isSome_eq_false_iff]
    constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by omega, hb⟩
  unfold Store.process
  dsimp only
  by_cases hc : (Store.supermajority c.preset (u.signers c.preset) &&
      Store.applies c (Store.moveAnchor c (Store.track c s u) u) u) = true
  · rw [if_pos hc, if_pos (hcond.mp hc)]
    have hacc : ∃ a l, (Store.apply c (Store.moveAnchor c (Store.track c s u) u) u).2 =
        .accepted a l := by
      rcases apply_verdict c (Store.moveAnchor c (Store.track c s u) u) u with h | h | ⟨hn, hne⟩
      · exact h
      · exact absurd h (learn_isSome hform)
      · exfalso
        rw [hn1] at hn
        have hper : Store.period c (Store.moveAnchor c (Store.track c s u) u) = Store.period c s := by
          simp [Store.period, hf1]
        rw [hper] at hne
        obtain ⟨-, hsig, hfa, -⟩ := Store.formOk_parts hform
        have hsp : c.periodAt u.signatureSlot = Store.period c s := by
          rcases hlive with h | ⟨-, h⟩
          · exact h
          · simp [hn] at h
        have m1 := Store.periodAt_mono c hfa
        have m2 := Store.periodAt_mono c (Nat.le_of_lt hsig)
        simp only [Bool.and_eq_true, Store.applies, hf1, hn1, hn, Option.isNone_none,
          Bool.true_and, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        have hrel' : s.finalized.beacon.slot < u.attested.beacon.slot ∨
            c.periodAt u.attested.beacon.slot = Store.period c s := by
          unfold Store.relevant at hrel
          rw [hn] at hrel
          simp only [Option.isNone_none, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, Update.slot] at hrel
          rcases hrel with h | ⟨-, h⟩
          · exact .inl (of_decide_eq_true h)
          · exact .inr h
        unfold Store.period at hsp hne hrel'
        rcases hc.2 with h | ⟨⟨-, -⟩, h⟩
        · have := Store.periodAt_mono c (Nat.le_of_lt h)
          omega
        · rcases hrel' with h' | h'
          · have := Store.periodAt_mono c (Nat.le_of_lt h')
            simp only [Update.slot] at h
            omega
          · simp only [Update.slot] at h
            omega
    obtain ⟨a, l, hacc⟩ := hacc
    obtain ⟨S', hS', hsim⟩ := apply_sim hA h1 hacc
    exact ⟨_, by rw [hS']; rfl, hsim, a, l, hacc⟩
  · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
    exact ⟨_, rfl, h1, false, false, rfl⟩


/-! ## `validate_light_client_update` -/

/-- **Every update leanLight lets reach `process`, `validate_light_client_update` passes** at the
clock's slot: leanLight's checks (`formOk`, the clock, a live committee for the signature period,
the signature, relevance, the next committee) are the specification's or stronger, on a committee
as the chain holds one. -/
theorem validate_sim {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) {u : Update} {now : Nat} {com : Committee}
    (hform : Store.formOk c u = true) (hclock : u.signatureSlot ≤ c.slotOf now)
    (hcom : Store.committeeFor c s (c.periodAt u.signatureSlot) = some (com, true))
    (hsig : Store.verifySignature c com u = true) (hV : Valid com)
    (hrel : Store.relevant c s u = true) (hnm : Store.nextMatches c s u = true) :
    validate_light_client_update cfg S (ofUpdate u) (c.slotOf now) c.genesisValidatorsRoot =
      some () := by
  obtain ⟨hsm, hsl, hfa, hva, hfin, hnext⟩ := Store.formOk_parts hform
  have h64 := Store.formOk_uint64 hform
  have hp := hs.period hA
  have hk := hs.known
  have hlive := Store.committeeFor_live hcom
  have hsize : com.pubkeys.size = cfg.SYNC_COMMITTEE_SIZE := by
    rcases hlive with ⟨-, rfl⟩ | ⟨-, hn⟩
    · exact hs.currentSize
    · exact (hs.nextSome com hn).2.2
  have hcomS : (if compute_sync_committee_period_at_slot cfg u.signatureSlot =
      compute_sync_committee_period_at_slot cfg S.finalized_header.beacon.slot
      then S.current_sync_committee else S.next_sync_committee) = ofCommittee com := by
    rw [hp, ← hA.periodAt]
    rcases hlive with ⟨h1, rfl⟩ | ⟨h1, hn⟩
    · simp [h1, hs.current]
    · simp [h1, (hs.nextSome com hn).1]
  obtain ⟨ps, hps, hfav⟩ := verifySignature_spec hA hV hsize h64 hsig
  have F1 : cfg.MIN_SYNC_COMMITTEE_PARTICIPANTS ≤ get_set_bit_count cfg u.aggregate.bits := by
    have := hA.minParticipants
    have := hA.sizePos
    simp only [Store.supermajority, decide_eq_true_eq, hA.signers, hA.committeeSize] at hsm
    omega
  have F2 := isValidHeader_spec hA (by simp only [Update.slot] at hsl; omega) hva
  have F3 : (c.slotOf now ≥ u.signatureSlot ∧ u.signatureSlot > u.attested.beacon.slot ∧
      u.attested.beacon.slot ≥ u.finalized.beacon.slot) := ⟨hclock, hsl, hfa⟩
  have hF : S.finalized_header.beacon.slot = s.finalized.beacon.slot := by
    rw [hs.finalized, ofHeader_beacon]
  have hper : ∀ x, compute_sync_committee_period_at_slot cfg x = c.periodAt x :=
    fun x => (hA.periodAt x).symm
  have hgi : finalized_root_gindex_at_slot cfg u.attested.beacon.slot =
      Store.finalizedGindex c u.slot := (hA.finalizedGindex (by simp only [Update.slot] at hsl; omega)).symm
  have hgn : next_sync_committee_gindex_at_slot cfg u.attested.beacon.slot =
      Store.nextGindex c u.slot := (hA.nextGindex (by simp only [Update.slot] at hsl; omega)).symm
  have hcomS' : (if c.periodAt u.signatureSlot = c.periodAt s.finalized.beacon.slot
      then S.current_sync_committee else S.next_sync_committee) = ofCommittee com := by
    simpa only [hper, hF] using hcomS
  simp only [ofHeader_beacon] at hfav
  have hpk : (ofCommittee com).pubkeys = com.pubkeys := rfl
  have R : (decide (u.attested.beacon.slot > s.finalized.beacon.slot) || !s.next.isSome &&
      (u.isSyncCommitteeUpdate && c.periodAt u.attested.beacon.slot ==
        c.periodAt s.finalized.beacon.slot)) = true := by
    simp only [Store.relevant, Store.period, Update.slot, Option.isNone_iff_eq_none,
      Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hrel
    simp only [Bool.or_eq_true, decide_eq_true_eq, gt_iff_lt, Bool.and_eq_true, Bool.not_eq_true',
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, beq_iff_eq]
    rcases hrel with h | ⟨⟨h1, h2⟩, h3⟩
    · exact .inl (of_decide_eq_true h)
    · exact .inr ⟨h1, h2, h3⟩
  have SP : (s.next.isSome = true → (c.periodAt u.signatureSlot = c.periodAt s.finalized.beacon.slot ∨
      c.periodAt u.signatureSlot = c.periodAt s.finalized.beacon.slot + 1)) ∧
      (s.next.isSome = false → c.periodAt u.signatureSlot = c.periodAt s.finalized.beacon.slot) := by
    unfold Store.period at hlive
    rcases hlive with ⟨h, -⟩ | ⟨h, hn⟩
    · exact ⟨fun _ => .inl h, fun _ => h⟩
    · exact ⟨fun _ => .inr h, fun h' => by simp [hn] at h'⟩
  have FIN : (u.isFinalityUpdate = false → u.finalized.isEmpty = true) ∧
      (u.isFinalityUpdate = true → u.finalized.beacon.slot = GENESIS_SLOT →
        u.finalized.isEmpty = true ∧ is_valid_normalized_merkle_branch Ssz.zeroChunk
          u.finalityBranch (Store.finalizedGindex c u.slot) u.attested.beacon.stateRoot = true) ∧
      (u.isFinalityUpdate = true → ¬ u.finalized.beacon.slot = GENESIS_SLOT →
        is_valid_light_client_header cfg (ofHeader u.finalized) = true ∧
        is_valid_normalized_merkle_branch u.finalized.beacon.root u.finalityBranch
          (Store.finalizedGindex c u.slot) u.attested.beacon.stateRoot = true) := by
    unfold Store.finalityOk at hfin
    refine ⟨fun h => by simpa [h] using hfin, fun h h0 => ?_, fun h h0 => ?_⟩
    · simp only [h, Bool.not_true, Bool.false_eq_true, ite_false, GENESIS_SLOT] at hfin h0
      simp only [h0, ite_true, Bool.and_eq_true, Store.Update.finalizedLeaf] at hfin
      exact ⟨hfin.1, normalized_of_runtime hfin.2⟩
    · simp only [h, Bool.not_true, Bool.false_eq_true, ite_false, GENESIS_SLOT] at hfin h0
      simp only [h0, ite_false, Bool.and_eq_true, Store.Update.finalizedLeaf] at hfin
      exact ⟨isValidHeader_spec hA (by simp only [Update.slot] at hsl hfa; omega) hfin.1,
        normalized_of_runtime hfin.2⟩
  have NX : (u.isSyncCommitteeUpdate = false → Store.committeeEmpty u.next = true) ∧
      (u.isSyncCommitteeUpdate = true → is_valid_normalized_merkle_branch
        (Store.committeeRoot c.preset u.next) u.nextBranch (Store.nextGindex c u.slot)
        u.attested.beacon.stateRoot = true) ∧
      (u.isSyncCommitteeUpdate = true → c.periodAt u.attested.beacon.slot =
        c.periodAt s.finalized.beacon.slot ∧ s.next.isSome = true →
        SyncCommittee.eq u.next S.next_sync_committee = true) := by
    refine ⟨fun h => (Store.nextOk_empty hnext).1 h,
      fun h => normalized_of_runtime ((Store.nextOk_empty hnext).2 h).2, fun h ⟨hp1, hp2⟩ => ?_⟩
    cases hn : s.next with
    | none => simp [hn] at hp2
    | some n =>
      simp only [Store.nextMatches, hn, h, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at hnm
      rcases hnm with h' | ⟨h1, h2⟩
      · exact absurd (by simpa [Store.period, Update.slot] using hp1) h'
      · simp [SyncCommittee.eq, (hs.nextSome n hn).1, ofCommittee, h1, h2]
  have hbr1 : (ofUpdate u).finality_branch = u.finalityBranch := rfl
  have hbr2 : (ofUpdate u).next_sync_committee_branch = u.nextBranch := rfl
  unfold validate_light_client_update
  simp only [ofUpdate_aggregate, ofUpdate_attested, ofUpdate_finalized, ofHeader_beacon,
    ofUpdate_signatureSlot, F1, F2, F3, require, decide_true, ite_true, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, hper, hF, hk, hcomS', hps, hfav, hgi, hgn, isSync_eq,
    isFinality_eq, ← isEmpty_eq, ← committeeEmpty_eq, ← hA.committeeRoot, and_self, hpk, R,
    ofUpdate_next, hbr1, hbr2]
  cases hn : s.next.isSome <;> cases hfu : u.isFinalityUpdate <;> cases hsu : u.isSyncCommitteeUpdate <;>
    by_cases h0 : u.finalized.beacon.slot = GENESIS_SLOT <;>
    simp [hn, hfu, hsu, h0, SP.1, SP.2, FIN.1, FIN.2.1, FIN.2.2, NX.1, NX.2.1]
  all_goals
    intro hap
    simp [NX.2.2 hsu ⟨hap, hn⟩, NX.2.1 hsu]

/-! ## One update -/

theorem counted_same (s : Store.Store) (u : Update) : SameSpec (Store.counted s u) s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem retain_same (c : Chain) (s : Store.Store) (now : Nat) (u : Update) :
    SameSpec (Store.retain c s now u) s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem halted_same (s : Store.Store) (k : Option Store.Conflict) :
    SameSpec { s with halted := k } s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **One update through leanLight's store is zero or one step of the specification's.** On a
store that agrees with the specification's, signed (when it is checked) by a committee as the
chain holds one: an update leanLight does not accept leaves the specification's store as it was
(`Sim` still holds); an update it accepts, `process_light_client_update` accepts at the clock's
slot, and the stores agree after it. -/
theorem receive_refines {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) (now : Nat) (u : Update)
    (hV : ∀ com, Store.committeeFor c s (c.periodAt u.signatureSlot) = some (com, true) →
      Valid com) :
    ((∀ a l, (Store.receive c s now u).2 ≠ .accepted a l) → Sim cfg (Store.receive c s now u).1 S) ∧
      (∀ a l, (Store.receive c s now u).2 = .accepted a l →
        ∃ S', process_light_client_update cfg S (ofUpdate u) (c.slotOf now)
            c.genesisValidatorsRoot = some S' ∧ Sim cfg (Store.receive c s now u).1 S') := by
  rcases Store.receive_cases_verdict c s now u with ⟨he, -⟩ | he | he | he | he | he |
      ⟨com, live, hp, he⟩
  all_goals try (rw [he]; exact ⟨fun _ => hs, fun _ _ h => by cases h⟩)
  rw [he]
  rcases Store.afterBls_cases c s now u live with ⟨k, -, ha⟩ | ⟨-, ha, hv⟩ | ⟨-, hl, -, hrm, ha⟩
  · rw [ha]
    exact ⟨fun _ => hs.congr ((halted_same _ _).trans (counted_same s u)),
      fun _ _ h => by cases h⟩
  · refine ⟨fun _ => ?_, fun a l h => ?_⟩
    · rw [ha]; exact hs.congr ((retain_same c _ now u).trans (counted_same s u))
    · rcases hv with hv | hv | hv | hv <;> rw [hv] at h <;> cases h
  · subst hl
    rw [ha]
    let s₂ := Store.retain c (Store.counted s u) now u
    have h2 : Sim cfg s₂ S := hs.congr ((retain_same c _ now u).trans (counted_same s u))
    have hcom₂ : Store.committeeFor c s₂ (c.periodAt u.signatureSlot) = some (com, true) :=
      hp.committee
    simp only [Bool.and_eq_true] at hrm
    have hval := validate_sim hA h2 hp.form hp.clock hcom₂ hp.signature (hV com hp.committee)
      hrm.1 hrm.2
    have hlive : c.periodAt u.signatureSlot = Store.period c s₂ ∨
        (c.periodAt u.signatureSlot = Store.period c s₂ + 1 ∧ s₂.next.isSome = true) := by
      rcases Store.committeeFor_live hcom₂ with ⟨h, -⟩ | ⟨h, hn⟩
      · exact .inl h
      · exact .inr ⟨h, by simp [hn]⟩
    obtain ⟨S', hS', hsim, a, l, hacc⟩ := process_sim hA h2 hval hp.form hlive hrm.1
    exact ⟨fun h => absurd hacc (h a l), fun _ _ _ => ⟨S', hS', hsim⟩⟩

/-- **An update leanLight accepts, the specification accepts**, and the two stores agree after
it. -/
theorem receive_accepted_spec {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) {now : Nat} {u : Update}
    (hV : ∀ com, Store.committeeFor c s (c.periodAt u.signatureSlot) = some (com, true) →
      Valid com) {a l : Bool} (h : (Store.receive c s now u).2 = .accepted a l) :
    ∃ S', process_light_client_update cfg S (ofUpdate u) (c.slotOf now)
        c.genesisValidatorsRoot = some S' ∧ Sim cfg (Store.receive c s now u).1 S' :=
  (receive_refines hA hs now u hV).2 a l h

/-! ## Bootstrap, the forced update, and every store reached -/

theorem empty_isEmpty (cfg : Config) : SyncCommittee.isEmpty (SyncCommittee.empty cfg) = true := by
  unfold SyncCommittee.isEmpty SyncCommittee.empty
  rw [Bool.and_eq_true, Array.all_eq_true]
  have hz : isZero Ssz.zeroChunk = true := by decide +kernel
  have ha : isZero ⟨Array.replicate 48 0⟩ = true := by decide +kernel
  exact ⟨fun i hi => by rw [Array.getElem_replicate]; exact hz, ha⟩

/-- The store `initialize_light_client_store` builds from a bootstrap. -/
def initOf (cfg : Config) (b : Bootstrap) : LightClientStore :=
  { finalized_header := ofHeader b.header, current_sync_committee := b.committee,
    next_sync_committee := SyncCommittee.empty cfg, best_valid_update := none,
    optimistic_header := ofHeader b.header, previous_max_active_participants := 0,
    current_max_active_participants := 0 }

/-- **A store leanLight starts, `initialize_light_client_store` starts**, from the same
checkpoint and bootstrap, and the two agree. -/
theorem bootstrap_sim {c : Chain} {cfg : Config} (hA : Agrees c cfg) {root : ByteArray}
    {now : Nat} {b : Bootstrap} {s : Store.Store} (h : Store.bootstrap c root now b = some s) :
    ∃ S, initialize_light_client_store cfg root (ofBootstrap b) = some S ∧ Sim cfg s S := by
  unfold Store.bootstrap at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hv, hr⟩, h64⟩, hbr⟩, -⟩ := hc
    cases hcom : Committee.ofSync c.preset b.committee with
    | none => rw [hcom] at h; cases h
    | some com =>
      rw [hcom] at h
      cases h
      refine ⟨initOf cfg b, ?_, ?_⟩
      · unfold initialize_light_client_store
        simp only [ofBootstrap, isValidHeader_spec hA h64 hv, ofHeader_beacon, ← hA.currentGindex h64,
          ← hA.committeeRoot, normalized_of_runtime hbr, require, ite_true, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, decide_eq_true (show b.header.beacon.root = root from hr)]
        rfl
      · exact
          { finalized := rfl
            current := (ofCommittee_ofSync hcom).symm
            currentSize := by
              rw [(Store.ofSync_keys hcom).2.1, (Store.ofSync_keys hcom).1, hA.committeeSize]
            nextNone := fun _ => empty_isEmpty cfg
            nextSome := fun n h => by cases h
            best := rfl
            optimistic := rfl
            previous := rfl
            currentMax := rfl }
  · cases h

/-- **The forced update leanLight's tests call is the specification's
`process_light_client_store_force_update`**: it leaves the specification's store as it was, or the
specification's forced update gives the store leanLight's agrees with. -/
theorem forceUpdate_refines {c : Chain} {cfg : Config} (hA : Agrees c cfg) {s : Store.Store}
    {S : LightClientStore} (hs : Sim cfg s S) (now : Nat) :
    Sim cfg (Store.forceUpdate c s now) S ∨
      ∃ S', process_light_client_store_force_update cfg S (c.slotOf now) = some S' ∧
        Sim cfg (Store.forceUpdate c s now) S' := by
  unfold Store.forceUpdate
  cases hb : s.best with
  | none => exact .inl hs
  | some b =>
    dsimp only
    by_cases hg : (s.halted.isNone && decide (s.finalized.beacon.slot + Store.updateTimeout c.preset <
        c.slotOf now)) = true
    · rw [if_pos hg]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      generalize hb' : (if b.finalized.beacon.slot ≤ s.finalized.beacon.slot then
        { b with finalized := b.attested } else b) = b'
      cases ha : Store.apply c s b' with
      | mk s' v =>
        cases v with
        | accepted a l =>
          dsimp only
          have hacc : (Store.apply c s b').2 = .accepted a l := by rw [ha]
          obtain ⟨S', hS', hsim⟩ := apply_sim hA hs hacc
          rw [ha] at hsim
          dsimp only at hsim
          refine .inr ⟨{ S' with best_valid_update := none }, ?_, ?_⟩
          · have hF : S.finalized_header.beacon.slot = s.finalized.beacon.slot := by
              rw [hs.finalized, ofHeader_beacon]
            have hT : UPDATE_TIMEOUT cfg = Store.updateTimeout c.preset := by
              simp [UPDATE_TIMEOUT, Store.updateTimeout, hA.slotsPerEpoch, hA.epochsPerPeriod]
            have hbest : S.best_valid_update = some (ofUpdate b) := by rw [hs.best, hb]; rfl
            have hU : (if (ofUpdate b).finalized_header.beacon.slot ≤ s.finalized.beacon.slot
                then { ofUpdate b with finalized_header := (ofUpdate b).attested_header }
                else ofUpdate b) = ofUpdate b' := by
              rw [← hb']
              simp only [ofUpdate_finalized, ofHeader_beacon]
              split_ifs <;> rfl
            unfold process_light_client_store_force_update
            rw [hbest]
            simp only [hF, hT, gt_iff_lt, hg.2, ite_true, hU, hS', Option.bind_eq_bind,
              Option.bind_some, Option.pure_def]
          · have hbn : s'.best = none := by
              have := hsim.best
              simp only at this
              cases h : s'.best
              · rfl
              · rw [h] at this; cases this
            exact Sim.congr (s := s') ⟨rfl, rfl, rfl, by simp [hbn], rfl, rfl, rfl⟩ hsim
        | _ => exact .inl hs
    · rw [if_neg hg]
      exact .inl hs

/-- **Every store leanLight reaches is one the specification reaches** from the same checkpoint:
`Driver.Reaches` (bootstrap, then any updates at any clocks) gives a store of
`Spec.LightClient.Reaches` (`initialize_light_client_store`, then `process_light_client_update`
steps, each validated) that holds the same finalized header, committees, best update, optimistic
header and counters. It rests on `Agrees` and on every committee authenticated from the
checkpoint being as the chain holds one (`Valid`), the trust the specification's light client
places in the committees it follows. -/
theorem reaches_spec {c : Chain} {cfg : Config} (hA : Agrees c cfg) {root : ByteArray}
    (hV : ∀ p com, Driver.CommitteeAuth c root p com → Valid com) {s : Store.Store}
    (hr : Driver.Reaches c root s) :
    ∃ S, Reaches cfg c.genesisValidatorsRoot root S ∧ Sim cfg s S := by
  induction hr with
  | start hb =>
    obtain ⟨S, hS, hsim⟩ := bootstrap_sim hA hb
    exact ⟨S, .init hS, hsim⟩
  | @step s now u hr ih =>
    obtain ⟨S, hS, hsim⟩ := ih
    obtain ⟨hcur, hnext⟩ := Driver.reaches_committees hr
    have hVc : ∀ com, Store.committeeFor c s (c.periodAt u.signatureSlot) = some (com, true) →
        Valid com := fun com h => hV _ com (Driver.committeeFor_live_auth hcur hnext h)
    obtain ⟨hno, hyes⟩ := receive_refines hA hsim now u hVc
    by_cases hacc : ∃ a l, (Store.receive c s now u).2 = .accepted a l
    · obtain ⟨a, l, h⟩ := hacc
      obtain ⟨S', hS', hsim'⟩ := hyes a l h
      exact ⟨S', .update _ _ hS hS', hsim'⟩
    · exact ⟨S, hS, hno fun a l h => hacc ⟨a, l, h⟩⟩

/-- **What the client reads from rests on the specification's store**: at every store leanLight
reaches, its finalized header and its current and next sync committees are those of a store the
specification reaches from the same checkpoint, and so is its optimistic header. -/
theorem reaches_spec_finalized {c : Chain} {cfg : Config} (hA : Agrees c cfg) {root : ByteArray}
    (hV : ∀ p com, Driver.CommitteeAuth c root p com → Valid com) {s : Store.Store}
    (hr : Driver.Reaches c root s) :
    ∃ S, Reaches cfg c.genesisValidatorsRoot root S ∧
      S.finalized_header = ofHeader s.finalized ∧
      S.current_sync_committee = ofCommittee s.current ∧
      S.optimistic_header = ofHeader s.optimistic ∧
      (∀ n, s.next = some n → S.next_sync_committee = ofCommittee n) ∧
      (s.next = none → is_next_sync_committee_known S = false) := by
  obtain ⟨S, hS, hsim⟩ := reaches_spec hA hV hr
  refine ⟨S, hS, hsim.finalized, hsim.current, hsim.optimistic, fun n h => (hsim.nextSome n h).1,
    fun h => ?_⟩
  rw [hsim.known, h]; rfl

end LeanLight.Spec.LightClient
