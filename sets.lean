import .lib.set
open set

section
  variable U : Type
  variables A B C : set U

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
  begin
    assume x,
    intro h,
    cases h,
    apply union.intro_left,
    assumption,
  end

  example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
  sorry
end