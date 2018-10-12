/-
Some proofs of simple theorems around even and odd numbers.

Mostly practice for using proof tactics.
-/
open tactic

@[simp] def is_even (n : ℕ) := ∃ x, n = 2 * x
@[simp] def is_odd  (n : ℕ) := ∃ x, n = 2 * x + 1

theorem even_plus_even_is_even {a b : ℕ} (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
begin
    simp,
    cases h₁ with w₁ hw₁,
    cases h₂ with w₂ hw₂,
    existsi w₁ + w₂,
    rw hw₁,
    rw hw₂,
    rw mul_add,
end

theorem even_plus_even_is_odd {a b : ℕ} (h₁ : is_even a) (h₂ : is_odd b) : is_odd (a + b) :=
begin
    simp,
    cases h₁ with w₁ hw₁,
    cases h₂ with w₂ hw₂,
    existsi w₁ + w₂,
    rw hw₁,
    rw hw₂,
    simp,
    rw mul_add
end

theorem odd_plus_odd_is_even {a b : ℕ} (h₁ : is_odd a) (h₂ : is_odd b) : is_even (a + b) :=
begin
    simp,
    cases h₁ with w₁ hw₁,
    cases h₂ with w₂ hw₂,
    existsi w₁ + w₂ + 1,
    rw hw₁,
    rw hw₂,
    rw mul_add,
    rw mul_add,
    simp,
    rw ←add_assoc,
end

theorem even_plus_two_is_even {a : ℕ} (h₁ : is_even a) : is_even (a + 2) :=
begin
    simp,                         -- is_even a + 2 → ∃ x : a + 2 = 2 * x
    apply even_plus_even_is_even, -- two subgoals: is_even a + is_even 2
    assumption,                   -- is_even a is an assumption h₁
    simp,                         -- is_even 2 → ∃ x : 2 = 2 * x
    existsi 1,                    -- true for x == 1
    trivial                       -- QED
end

-- Some additional proofs, useful for practicing tactics
section
    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    include a
    example : (∃ x : α, r) → r :=
    begin
        intro h,              
        cases h with a₁ ha₁, -- There exists some α such that r, call it a₁
        show r, exact ha₁    -- Therefore, r for all a
    end

    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
    begin
        apply iff.intro, -- two subgoals - forward and backwards directions of iff
        {
            -- Forward direction
            intro h,
            cases h with a ha,  -- There exists an x such that h, call it a
            cases ha, split,    -- Both sides of the and must be true, split into 2 subgoals
            existsi a,          -- Intro the exists by proving that a is a witness
            assumption,         -- ... and that p a is true (a hypothesis)
            assumption,         -- Finally, r is true by the split hypothesis, so we are done
        },
        {
            -- Backward direction
            intro h,
            cases h with left right,
            cases left with a ha,
            existsi a,
            exact ⟨ha, right⟩
        }
    end

    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    begin
        apply iff.intro,
        {
            intro h,
            cases h with a₁ ha₁,
            apply or.elim,
            assumption,
            {
                intro q,
                apply or.intro_left,
                existsi a₁,
                assumption
            },
            {
                intro q,
                apply or.intro_right,
                existsi a₁,
                assumption
            }
        },
        {
            intro h,
            apply or.elim,
            assumption,
            {
                intro q,
                cases q with a₁ ha₁,
                existsi a₁,
                apply or.intro_left,
                assumption
            },
            {
                intro q,
                cases q with a₁ ha₁,
                existsi a₁,
                apply or.intro_right,
                assumption,
            }
        }
    end
    

    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    begin
        apply iff.intro,
        {
            intro h,
            cases h with witness hwitness,
            apply or.elim hwitness,
            {
                intro hp,
                apply or.intro_left,
                existsi witness,
                assumption
            },
            {
                intro hq,
                apply or.intro_right,
                existsi witness,
                assumption
            }
        },
        {
            intro h,
            apply or.elim h,
            {
                intro hp,
                cases hp with witness hwitness,
                existsi witness,
                apply or.intro_left,
                assumption,
            },
            {
                intro hq,
                cases hq with witness hwitness,
                existsi witness,
                apply or.intro_right,
                assumption,
            }
        }
    end
end