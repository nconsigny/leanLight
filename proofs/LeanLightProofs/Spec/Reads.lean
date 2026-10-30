-- Moved to LeanLight/El/Reads.lean (docs/spec-16-light-client.md, LC1), namespace kept;
-- this module stays so that its importers build unchanged. G11's nonce rules, which only the UI
-- runs, are specified here.
import LeanLight.El.Reads

/-!
# Settled, replaceable and foreign nonces (G11, invariant 25m)

What `lkd_verified::reads::{settled, may_replace, alarm}` decide, over the nonce `p` proved at a
head (`docs/spec-16-light-client.md`, "Stuck, settled and foreign nonces (G11)"):

- `settled p n`: nonce `n` was consumed (`settled_iff`: `n < p`);
- `mayReplace p n receiptSeen fresh`: a speed-up or a cancel is offered only while `p ≤ n`, no
  receipt was seen and the head is fresh (`mayReplace_iff`), never for a settled nonce
  (`mayReplace_not_settled`);
- `alarm last p`: `keyd`'s last signed nonce is `m` and `p > m + 1` (`alarm_iff`).

**What they mean, under H_nonce** (`Consumed`): an account's nonce at a block is how many nonce
values its included transactions and EIP-7702 authorizations consumed up to that block, each
consuming the account's nonce at the time and raising it by one, so the values consumed, in the
order the chain consumed them, are exactly `0, 1, …, p - 1`. Then:

- `settled_consumed`, `unsettled_absent`: `n` is settled exactly when it was consumed; while it
  is not, no transaction or authorization at `n` is included up to that block;
- `settled_final`: on a later block of the same chain the values consumed extend these, and a
  settled `n` is never consumed again, so no transaction at `n` can be included after;
- `mayReplace_absent`: a nonce a speed-up or a cancel is offered for was not consumed;
- `alarm_foreign`: when every nonce `keyd` released is at most its last `m` (invariants 7a and
  7b: what `keyd` releases is at most its ledger's last at any later read; 7c: a refusal gives
  back only nonces not released), the alarm means `m + 1` to `p - 1` were consumed by
  transactions or authorizations `keyd` did not sign; `no_alarm` is the converse: without it,
  every value consumed is at most `m`.

H_nonce is the chain's execution (EIP-2681's nonce, EIP-7702's authorizations), not proved here.
-/

namespace LeanLight.Spec.Reads

/-- Nonce `n` is settled at a head where the account's nonce is `p`. -/
def settled (p n : Nat) : Bool := decide (n < p)

/-- A speed-up or a cancel of nonce `n` may be offered at a head where the account's nonce is
`p`: not settled, no receipt seen, the head fresh. -/
def mayReplace (p n : Nat) (receiptSeen fresh : Bool) : Bool :=
  decide (p ≤ n) && !receiptSeen && fresh

/-- The foreign-nonce alarm: `keyd` last signed `m`, and the account's nonce is past `m + 1`. -/
def alarm : Option Nat → Nat → Bool
  | none, _ => false
  | some m, p => decide (m + 1 < p)

theorem settled_iff {p n : Nat} : settled p n = true ↔ n < p := by
  simp [settled]

theorem mayReplace_iff {p n : Nat} {r f : Bool} :
    mayReplace p n r f = true ↔ p ≤ n ∧ r = false ∧ f = true := by
  cases r <;> cases f <;> simp [mayReplace]

theorem mayReplace_not_settled {p n : Nat} {r f : Bool} (h : mayReplace p n r f = true) :
    settled p n = false := by
  obtain ⟨hp, -, -⟩ := mayReplace_iff.mp h
  simp [settled]
  omega

theorem alarm_iff {last : Option Nat} {p : Nat} :
    alarm last p = true ↔ ∃ m, last = some m ∧ m + 1 < p := by
  cases last <;> simp [alarm]

/-- H_nonce: the values an account consumed up to a block, in order, are `0, …, p - 1`, where
`p` is its nonce at that block. -/
def Consumed (c : List Nat) (p : Nat) : Prop := c = List.range p

theorem settled_consumed {c : List Nat} {p n : Nat} (h : Consumed c p) :
    settled p n = true ↔ n ∈ c := by
  subst h
  simp [settled_iff, List.mem_range]

theorem unsettled_absent {c : List Nat} {p n : Nat} (h : Consumed c p) :
    settled p n = false ↔ n ∉ c := by
  subst h
  simp [settled, List.mem_range]

/-- Settled for good: on a later block, with nonce `p₂ ≥ p₁`, the values consumed extend those of
the earlier one, and a nonce settled at the earlier one is not among those consumed after it. -/
theorem settled_final {c₁ c₂ : List Nat} {p₁ p₂ n : Nat} (h₁ : Consumed c₁ p₁)
    (h₂ : Consumed c₂ p₂) (hle : p₁ ≤ p₂) (hs : settled p₁ n = true) :
    c₁ <+: c₂ ∧ n ∉ c₂.drop c₁.length := by
  subst h₁ h₂
  rw [settled_iff] at hs
  refine ⟨?_, ?_⟩
  · rw [List.prefix_iff_eq_take, List.length_range, List.take_range, Nat.min_eq_left hle]
  · intro hmem
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hmem
    rw [List.getElem_drop, List.getElem_range, List.length_range] at hx
    omega

theorem mayReplace_absent {c : List Nat} {p n : Nat} {r f : Bool} (h : Consumed c p)
    (hm : mayReplace p n r f = true) : n ∉ c :=
  (unsettled_absent h).mp (mayReplace_not_settled hm)

/-- The alarm, under H_nonce and `keyd`'s ledger (every nonce it released, `signed`, at most its
last `m`): `m + 1` to `p - 1` were consumed, and `keyd` signed none of them. -/
theorem alarm_foreign {c signed : List Nat} {p m : Nat} (h : Consumed c p)
    (hk : ∀ s ∈ signed, s ≤ m) (ha : alarm (some m) p = true) :
    m + 1 ∈ c ∧ m + 1 ∉ signed ∧ ∀ v, m < v → v < p → v ∈ c ∧ v ∉ signed := by
  subst h
  have hp : m + 1 < p := by simpa [alarm] using ha
  have hv : ∀ v, m < v → v < p → v ∈ List.range p ∧ v ∉ signed := fun v hmv hvp =>
    ⟨List.mem_range.mpr hvp, fun hs => absurd (hk v hs) (by omega)⟩
  exact ⟨(hv (m + 1) (by omega) hp).1, (hv (m + 1) (by omega) hp).2, hv⟩

/-- Without the alarm, every value the account consumed is at most `keyd`'s last. -/
theorem no_alarm {c : List Nat} {p m : Nat} (h : Consumed c p) (ha : alarm (some m) p = false) :
    ∀ v ∈ c, v ≤ m := by
  subst h
  intro v hv
  have hp : ¬ m + 1 < p := by simpa [alarm] using ha
  have := List.mem_range.mp hv
  omega

end LeanLight.Spec.Reads
