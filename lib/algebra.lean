universe u

namespace algebra

class semigroup (α : Type u) extends has_mul α :=
(mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))

class abelian_semigroup (α : Type u) extends semigroup α :=
(mul_comm : ∀ a b : α, a * b = b * a)

class monoid (α : Type u) extends semigroup α, has_one α :=
(mul_one : ∀ a : α, 1 * a = a)
(one_mul : ∀ a : α, a * 1 = a)

class group (α : Type u) extends monoid α, has_inv α :=
(mul_left_inv  : ∀ a : α, a⁻¹ * a = 1)
(mul_right_inv : ∀ a : α, a * a⁻¹ = 1)


end algebra