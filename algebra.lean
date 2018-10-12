universe u

variables (α β : Type u)

-- Equality is useful in proofs. If two things are equal, they can be substituted
-- for one another in proofs using eq.subst. Such as this proof:
example (a b : α) (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b :=
    eq.subst h₁ h₂


-- ▸ is shorthand for eq.subst:
example (a b : α) (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b := h₁ ▸ h₂

-- We can start using algebraic theorems to prove useful theorems:
theorem foil (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
        from mul_add (x + y) x y,
    have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
        from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
    h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- We can do "calculative proofs" by chaining together basic principles:
section
    variables (a b c d e : ℕ)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    theorem T : a = e :=
        calc
          a     = b     : h1 -- a == b by hypothesis 1
          ...   = c + 1 : h2 -- b == c + 1 by hypothesis 2
          ...   = d + 1 : congr_arg _ h3 -- c + 1 == d + 1 by the congruence of c and d, hypothesis 3
          ...   = 1 + d : add_comm d (1 : ℕ) -- d + 1 == 1 + d by the communitivity of addition
          ...   = e : eq.symm h4 -- 1 + d == e by hypothesis 4, qed
          
    -- We can do the same proof above using rewrite tactics:
    include h1 h2 h3 h4
    theorem T': a = e :=
        calc
            a    = b     : by rw h1
            ...  = c + 1 : by rw h2
            ...  = d + 1 : by rw h3
            ...  = 1 + d : by rw add_comm
            ...  = e     : by rw h4

    -- Not explained, but here's a super simple proof of foil using tactics
    theorem foil_fast (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
        by simp [mul_add, add_mul]
end

-- Existential quantifiers

-- Like universal quantifiers, existential quantifiers have an introduction rule
-- and an elimination rule. Like in regular math, it sufficies to prove an existential
-- to prove that a prop p holds for one element of some type:
section 
    open nat

    example : ∃ x : ℕ, x > 0 :=
        -- Obvious proof that there exists a natural number greater than zero:
        -- one exists, is a natural number, and is greater than zero
        have h : 1 > 0, from zero_lt_succ 0,
        exists.intro 1 h

    -- Equivalent syntax
    example : ∃ x : ℕ, x > 0 :=
        have h : 1 > 0, from zero_lt_succ 0,
        ⟨1, h⟩

    variables (p q : α → Prop)

    -- The existential elimination rule allows us to prove some prop q through an existential
    -- by showing that q holds for all x
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        exists.elim h
            (
                assume w, -- There exists some x such that p x ∧ q x, call it w
                assume hw : p w ∧ q w,
                show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩
            )

    -- Equivalent proof, using 'match' to deconstruct the existential into cases
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        -- Not sure what the semantics of this are yet... I guess you can always
        -- destructure existentials into a witness and a hypothesis that the property
        -- holds for the witness
        match h with ⟨(w : α), (hw : p w ∧ q w)⟩ :=
            ⟨w, hw.right, hw.left⟩
        end

    def is_even (p : ℕ) := ∃ x, p = 2 * x

    theorem even_plus_even_is_even { a b : ℕ } (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
        match h₁, h₂ with
            -- This is extremely concise, but the core reasoning in the rewrite tactic is:
            --  0) start with is_even w₁ + w₂
            --  1) w₁ = 2 * q for some q (2 * q + w₂), since w₁ is even (h1)
            --  2) w₂ = 2 * p for some p (2 * q + 2 * p), since w₂ is even (h2)
            --  3) (2 * q) + 2 * (p + q) (mul_add)
            -- QED
            ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ := ⟨w₁ + w₂, by rw [hw₁, hw₂, mul_add]⟩
        end

    -- A similar proof, done on my own...
    def is_odd (p : ℕ) := ∃ x, p = 2 * x + 1

    theorem even_plus_odd_is_odd { a b : ℕ } (h1 : is_even a) (h2 : is_odd b) : is_odd (a + b) :=
        match h1, h2 with
            ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, begin rw hw1, rw hw2, simp, rw mul_add end⟩
        end
end