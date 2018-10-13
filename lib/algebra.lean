universe u

namespace algebra

variable {α: Type u}

/-
 - Semigroup Proofs
 -/
section semigroup

  theorem mul_left_inj [left_cancel_semigroup α] (a : α) {b c : α} : a * b = a * c ↔ b = c :=
    ⟨mul_left_cancel, congr_arg _⟩

  #check @mul_left_inj
  
end semigroup

/-
 - Group Proofs
 -/
section group
  variables [group α] {a b : α}

  theorem same_inverse_implies_equality : a⁻¹ = b⁻¹ ↔ a = b :=
  begin
    apply iff.intro,
    {
      intro h,
      rw ←inv_inv a,
      rw h,
      rw inv_inv,
    },
    {
      intro h,
      apply congr_arg,
      exact h,
    }
  end

  theorem mul_self_iff_one : a * a = a ↔ a = 1 :=
  begin
    have q := @mul_left_inj _ _ a a 1,
    rw mul_one at q,
    exact q
  end

  theorem inv_one_iff_one : a⁻¹ = 1 ↔ a = 1 :=
  begin
    rw ←@same_inverse_implies_equality _ _ a 1,
    rw one_inv,
  end
end group
end algebra