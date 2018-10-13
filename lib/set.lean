import .logic

universe u

local attribute [instance] classical.prop_decidable

namespace set

variable {U: Type u}

/-
 - Unions
 -/

theorem union.intro_left {A : set U} (B : set U) : ∀ x, x ∈ A → x ∈ A ∪ B :=
begin
  intro x,
  intro ha,
  apply or.intro_left,
  assumption
end

theorem union.intro_right {A : set U} (B : set U) : ∀ x, x ∈ A → x ∈ B ∪ A :=
begin
  intro x,
  intro ha,
  apply or.intro_right,
  assumption
end

theorem union.intro {A B : set U} : ∀ x, x ∈ A ∨ x ∈ B → x ∈ A ∪ B :=
begin
  intros x h,
  cases h with ha hb,
  {
    apply union.intro_left,
    assumption
  },
  {
    apply union.intro_right,
    assumption
  }
end

/-
 - Set Complement
 -/
theorem mem.complement {A : set U} {x : U} (h₁ : x ∉ A) : x ∈ -A := h₁
theorem mem.complement_reverse {A: set U} {x: U} (h₁ : x ∈ -A) : x ∉ A := h₁

theorem intersect.intro {A B : set U} : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B :=
begin
  assume x,
  intro ha,
  intro hb,
  apply and.intro,
  assumption,
  assumption,
end

/-
 - Generally useful theorems
 -/

theorem subset.refl (A : set U) : A ⊆ A :=
  by {assume h, intro, assumption}

theorem subset.trans (A B C : set U) : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intros h1 h2,
  assume x,
  intro ha,
  exact h2 (h1 ha)
end

theorem subset.ext (A B: set U) : (∀ x, x ∈ A ↔ x ∈ B) → A = B :=
begin
  assume hforall,
  apply funext,
  assume x,
  apply propext (hforall x),
end

theorem subset.antisymm (A B : set U) (h₁ : A ⊆ B) (h₂ : B ⊆ A) : A = B :=
begin
  apply subset.ext,
  assume x,
  apply iff.intro,
  { intro ha, exact (h₁ ha) },
  { intro hb, exact (h₂ hb) }
end

-- Still working on this theorem...
theorem demorgan_union {A B : set U} : -(A ∩ B) = -A ∪ -B :=
begin
  apply subset.antisymm,
  {
    intros x h,
    have hnot := mem.complement_reverse h,
    suffices ha : x ∉ A ∨ x ∉ B,
    cases ha with hleft hright,
    {
      apply union.intro,
      apply or.intro_left,
      assumption,
    },
    {
      apply union.intro,
      apply or.intro_right,
      assumption,
    },
    {
      -- proof of suffices condition: x ∉ A ∨ x ∉ b
      -- pretty huge gap in this proof...
      sorry
    }
  },
  {
    -- pretty sure you can't do this with non-classical logic
    sorry
  }
end

end set