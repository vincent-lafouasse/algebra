/-! # Groups

Mathlib: `Mathlib/Algebra/Group/Defs.lean`.

Mathlib builds `Group` in layers (`Semigroup`, `Monoid`, `DivInvMonoid`, …). Here it is one
flat class with Mathlib's fields minus the power and division ones (those come later):
associativity, `1` on both sides, and a *left* inverse. `mul_inv_cancel` is a theorem
(see `Algebra/Group/Basic.lean`).

`mul_one` is a field although it follows from the others: an instance has to prove it.
`Group.ofLeftAxioms` (in `Algebra/Group/MinimalAxioms.lean`) builds a group without it.

`1`, `*` and `⁻¹` come from core's `One`, `Mul` and `Inv` classes, as in Mathlib. -/

universe u

namespace My

class Group (G : Type u) extends Mul G, One G, Inv G where
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  protected one_mul : ∀ a : G, 1 * a = a
  protected mul_one : ∀ a : G, a * 1 = a
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  protected mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

class CommGroup (G : Type u) extends Group G where
  protected mul_comm : ∀ a b : G, a * b = b * a

section

variable {G : Type u} [Group G]

-- the axioms, as theorems outside the `Group` namespace (as in Mathlib)
theorem mul_assoc (a b c : G) : a * b * c = a * (b * c) :=
  Group.mul_assoc a b c

theorem one_mul (a : G) : 1 * a = a :=
  Group.one_mul a

theorem mul_one (a : G) : a * 1 = a :=
  Group.mul_one a

theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 :=
  Group.mul_inv_cancel a

instance Group.to_isAssociative : Std.Associative (λ (a b : G) => a * b) :=
  ⟨mul_assoc⟩

end

theorem mul_comm {G : Type u} [CommGroup G] (a b : G) : a * b = b * a :=
  CommGroup.mul_comm a b

instance CommGroup.to_isCommutative {G : Type u} [CommGroup G] :
    Std.Commutative (λ (a b : G) => a * b) :=
  ⟨CommGroup.mul_comm⟩

end My
