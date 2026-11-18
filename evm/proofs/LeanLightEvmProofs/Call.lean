import LeanLightEvmProofs.Prepare

/-!
# What an answer or a refusal of `call` tells

The facts `call` decided on when it answered or refused, read back from its definition.
-/

namespace LeanLightEvmProofs

open LeanLightEvm
open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.Transactions (CallOutput)

/-- What `call` checked before it answered. -/
structure Answered (b : Budgets) (i : Input) (a : Answer) where
  rules : LeanLightEvm.Activation
  p : Prepared
  o : CallOutput
  notes : Notes
  input : checkInput b i = .ok rules
  sender : i.facts.accounts.contains i.request.sender = true
  recipient : ∀ x, i.request.to = some x → i.facts.accounts.contains x = true
  prepared : prepare rules i.chainId i.header i.ancestors b.executionGas i.request
    i.facts.toState = .ok p
  ran : p.runObserved i.facts i.header.number = .ok (o, notes)
  complete : (checkRun i.facts i.header i.ancestors i.request o notes).complete = true
  nonEmpty : (checkRun i.facts i.header i.ancestors i.request o notes).nonEmpty = []
  result : a.result = p.result o

private theorem fixed_known {f : Facts} {r : Request}
    (h : ((r.sender :: r.to.toList).filter fun a => !f.accounts.contains a).isEmpty = true) :
    f.accounts.contains r.sender = true ∧ ∀ x, r.to = some x → f.accounts.contains x = true := by
  rw [List.isEmpty_iff, List.filter_eq_nil_iff] at h
  refine ⟨?_, fun x hx => ?_⟩
  · have := h r.sender (List.mem_cons_self ..)
    simpa using this
  · have := h x (List.mem_cons_of_mem _ (by simp [hx]))
    simpa using this

theorem answered {b : Budgets} {i : Input} {a : Answer} (h : call b i = .answer a) :
    Nonempty (Answered b i a) := by
  unfold call at h
  split at h
  · cases h
  rename_i rules hin
  dsimp only at h
  split at h
  · cases h
  rename_i hmissing
  have hfixed := fixed_known (by simpa using hmissing)
  split at h <;> try cases h
  rename_i p hp
  split at h
  · cases h
  split at h <;> try cases h
  rename_i o notes hrun
  split at h
  · repeat' split at h
    all_goals cases h
  rename_i hc
  split at h
  · cases h
  rename_i hn
  split at h
  · cases h
  cases h
  exact ⟨⟨rules, p, o, notes, hin, hfixed.1, hfixed.2, hp, hrun, by simpa using hc, hn, rfl⟩⟩

end LeanLightEvmProofs
