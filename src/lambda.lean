import data.finset

namespace lambda

inductive term : Type
| var : ℕ → term
| abs : ℕ → term → term
| app : term → term → term

def free_variables : term → finset ℕ
| (term.var v)     := {v}
| (term.abs v e)   := (free_variables e) \ {v}
| (term.app e₁ e₂) := (free_variables e₁) ∪ (free_variables e₂)

definition closed (t : term) : Prop := (free_variables t) = ∅

end lambda