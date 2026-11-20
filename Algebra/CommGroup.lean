import Algebra.Commute

/-! # Commutative groups

A `Group` whose multiplication commutes. In such a group every pair of elements
`Commute`s, and inverses cancel from either side. -/

universe u

namespace My

class CommGroup (G : Type u) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

-- every two elements of a commutative group commute (Mathlib states this for any `CommMagma`)
theorem Commute.all {G : Type u} [CommGroup G] (a b : G) : Commute a b :=
  sorry

namespace CommGroup

open Group

variable {G : Type u} [CommGroup G]

theorem inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b :=
  sorry

theorem mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b :=
  sorry

theorem inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b :=
  sorry

theorem mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b :=
  sorry

end CommGroup
end My
