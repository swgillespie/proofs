namespace logic

open classical

variables {p q : Prop}

theorem not_or : ¬p ∧ ¬q → ¬(p ∨ q)
| ⟨hnp, _⟩ (or.inl hp) := hnp hp
| ⟨_, hnq⟩ (or.inr hq) := hnq hq

theorem not_and : ¬p ∨ ¬q → ¬(p ∧ q)
| (or.inl hnp) ⟨hp, _⟩ := hnp hp
| (or.inr hnq) ⟨_, hq⟩ := hnq hq

theorem or_not : ¬(p ∧ q) → ¬p ∨ ¬q :=
λ h_not_p_and_q,
  match classical.em p, classical.em q with
  | or.inr hnp, _ := or.inl hnp
  | _,          or.inr hnq := or.inr hnq
  | or.inl hp, or.inl hq := absurd (and.intro hp hq) h_not_p_and_q
  end

theorem and_not : ¬(p ∨ q) → ¬p ∧ ¬q :=
λ h, ⟨let t := h ∘ or.inl in t, h ∘ or.inr⟩

end logic