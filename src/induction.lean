/-
 - Exercises and theorems using induction.
 -/

open function

section example_6
  inductive aexpr : Type
  | const : ℕ → aexpr
  | var : ℕ → aexpr
  | plus : aexpr → aexpr → aexpr
  | times : aexpr → aexpr → aexpr

  open aexpr

  def sample_aexpr : aexpr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

  def aeval (v : ℕ → ℕ) : aexpr → ℕ
  | (const n)     := n
  | (var n)       := v n
  | (plus e₁ e₂)  := (aeval e₁) + (aeval e₂)
  | (times e₁ e₂) := (aeval e₁) * (aeval e₂)

  def sample_val : ℕ → ℕ
  | 0 := 5
  | 1 := 6
  | _ := 0

  -- Try it out. You should get 47 here.
  #eval aeval sample_val sample_aexpr

  def simp_const : aexpr → aexpr
  | (plus (const n₁) (const n₂))  := const (n₁ + n₂)
  | (times (const n₁) (const n₂)) := const (n₁ * n₂)
  | e                             := e

  def fuse : aexpr → aexpr 
  | (plus e₁ e₂)  := simp_const (plus  (fuse e₁) (fuse e₂))
  | (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))
  | e             := e

  theorem simp_const_eq (v : ℕ → ℕ) :
    ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
    begin
      intro h,
      induction h,
      all_goals {
        try { rw simp_const },
        all_goals {
          cases h_a,
          cases h_a_1,
          all_goals {
            rw simp_const,
            repeat { rw aeval }
          }
        }
      }
    end

  theorem fuse_eq (v : ℕ → ℕ) :
    ∀ e : aexpr, aeval v (fuse e) = aeval v e := sorry

end example_6