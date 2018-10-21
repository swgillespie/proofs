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

  def simp_const : aexpr → aexpr
  | (plus (const n₁) (const n₂))  := const (n₁ + n₂)
  | (times (const n₁) (const n₂)) := const (n₁ * n₂)
  | e                             := e

  def fuse : aexpr → aexpr 
  | (plus e₁ e₂)  := simp_const (plus  (fuse e₁) (fuse e₂))
  | (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))
  | e             := e

  theorem simp_const_eq (v : ℕ → ℕ) : ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
  begin
    intro e,     -- Suppose there exists an aexpr, call it e,
    induction e, -- Begin a proof by induction on variants of e
    case aexpr.const { rw simp_const }, -- e is a const? Trivial, since simp_const does not touch them
    case aexpr.var { rw simp_const },   -- e is a var? same, simp_const does not touch them.
    case aexpr.plus : e₁ e₂ {
      -- e is a plus? Induct on both operands of the plus and repeatedly rewrite using aeval and
      -- simp_cont to ultimately prove that simp_const and the + operator on ℕ do the same thing.
      cases e₁,
      cases e₂,
      iterate { simp [simp_const, aeval] },
    },
    case aexpr.times : e₁ e₂ {
      -- e is a times? Same as above, but we're proving that * and simp_const do the same thing.
      cases e₁,
      cases e₂,
      iterate { simp [simp_const, aeval] },
    }
  end

  theorem fuse_eq (v : ℕ → ℕ) : ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
  begin
    intro e,
    induction e,
    case aexpr.const { rw fuse },
    case aexpr.var { rw fuse },
    case aexpr.plus : e₁ e₂ he₁ he₂ { simp [fuse, simp_const_eq, aeval, he₁, he₂] },
    case aexpr.times : e₁ e₂ he₁ he₂ { simp [fuse, simp_const_eq, aeval, he₁, he₂] },
  end

end example_6