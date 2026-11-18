/-!
# `for` loops over lists, as `LeanLightEvm` writes them

`LeanLightEvm`'s checks are `for` loops: in `Id`, over a mutable record of findings
(`checkRun`), and in `Except`, throwing at the first bad element (`Facts.check`). These lemmas
read such a loop element by element.
-/

namespace LeanLightEvmProofs.Loops

universe u v

section Id

variable {α : Type u} {β : Type v}

/-- A loop in `Id` whose body always continues keeps a property every step keeps. -/
theorem forIn_id_keep (flag : β → Prop) (body : α → β → Id (ForInStep β))
    (hkeep : ∀ a b b', body a b = .yield b' → flag b → flag b')
    (hyield : ∀ a b, ∃ b', body a b = .yield b') :
    ∀ (L : List α) (init : β), flag init → flag (forIn L init body).run
  | [], _, h => h
  | a :: t, init, h => by
    obtain ⟨b', hb⟩ := hyield a init
    rw [List.forIn_cons, hb]
    exact forIn_id_keep flag body hkeep hyield t b' (hkeep a init b' hb h)

/-- A loop in `Id` whose body always continues ends with a property every step keeps, once one
element of the list makes it hold. -/
theorem forIn_id_flag (flag : β → Prop) (body : α → β → Id (ForInStep β))
    (hkeep : ∀ a b b', body a b = .yield b' → flag b → flag b')
    (hyield : ∀ a b, ∃ b', body a b = .yield b') {a₀ : α}
    (htrigger : ∀ b b', body a₀ b = .yield b' → flag b') :
    ∀ (L : List α) (init : β), a₀ ∈ L → flag (forIn L init body).run
  | [], _, h => absurd h List.not_mem_nil
  | a :: t, init, h => by
    obtain ⟨b', hb⟩ := hyield a init
    rw [List.forIn_cons, hb]
    rcases List.mem_cons.mp h with e | e
    · subst e
      exact forIn_id_keep flag body hkeep hyield t b' (htrigger init b' hb)
    · exact forIn_id_flag flag body hkeep hyield htrigger t b' e

end Id

section Except

variable {ε : Type u} {α : Type v}

/-- A loop in `Except` that ends without error, whose body continues or throws, ran its body
without error on every element. -/
theorem forIn_except_ok (body : α → PUnit → Except ε (ForInStep PUnit))
    (hbody : ∀ a, body a ⟨⟩ = .ok (.yield ⟨⟩) ∨ ∃ e, body a ⟨⟩ = .error e) :
    ∀ (L : List α), forIn L ⟨⟩ body = .ok ⟨⟩ → ∀ a ∈ L, body a ⟨⟩ = .ok (.yield ⟨⟩)
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: t, hrun, a, ha => by
    rw [List.forIn_cons] at hrun
    rcases hbody x with hx | ⟨e, hx⟩
    · rw [hx] at hrun
      rcases List.mem_cons.mp ha with e | e
      · subst e
        exact hx
      · exact forIn_except_ok body hbody t hrun a e
    · rw [hx] at hrun
      cases hrun

end Except

end LeanLightEvmProofs.Loops
