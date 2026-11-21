/-! # Groups

Mathlib: `Mathlib/Algebra/Group/Defs.lean`.

Mathlib builds `Group` in layers (`Semigroup`, `Monoid`, `DivInvMonoid`, …). Here it is one
flat class with three axioms: associativity, a *left* identity and a *left* inverse.
`mul_one` and `mul_inv_cancel` are theorems, not axioms (see `Algebra/Group/Basic.lean`).

`1`, `*` and `⁻¹` come from core's `One`, `Mul` and `Inv` classes, as in Mathlib. -/

universe u

namespace My

class Group (G : Type u) extends Mul G, One G, Inv G where
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  protected one_mul : ∀ a : G, 1 * a = a
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

class CommGroup (G : Type u) extends Group G where
  protected mul_comm : ∀ a b : G, a * b = b * a

section

variable {G : Type u} [Group G]

-- the axioms, as theorems outside the `Group` namespace (as in Mathlib)
theorem mul_assoc (a b c : G) : a * b * c = a * (b * c) :=
  Group.mul_assoc a b c

theorem one_mul (a : G) : 1 * a = a :=
  Group.one_mul a

theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

end

theorem mul_comm {G : Type u} [CommGroup G] (a b : G) : a * b = b * a :=
  CommGroup.mul_comm a b

end My
