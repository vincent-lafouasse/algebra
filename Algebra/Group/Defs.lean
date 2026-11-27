/-! # Groups

Mathlib: `Mathlib/Algebra/Group/Defs.lean`.

Mathlib builds `Group` in layers (`Semigroup`, `MulOneClass`, `Monoid`, `DivInvMonoid`, …).
Here there are two: a `Monoid` (associativity, `1` on both sides) and a `Group` on top of it
(`⁻¹` on both sides). Mathlib's power and division fields are left out (`npow`, `zpow`, `div`):
`^` is a plain definition, `npowRec`, in `Pow.lean`. Mathlib has no `mul_inv_cancel` field
(there it is a theorem): that field is not in Mathlib.

Rings will need the split: a ring's multiplication is a monoid, not a group. So every lemma
that holds in any monoid is stated for `[Monoid M]`, and groups get it through
`Group.toMonoid`. "No `⁻¹` in the statement" is not enough: cancellation
(`mul_left_cancel`), `a * b = a ↔ b = 1`, and the uniqueness of inverses all fail in monoids.
In the monoid `ℕ → ℕ` under composition, a surjection has many right inverses.

`mul_one` and `mul_inv_cancel` follow from the other three, so an instance should not prove
them by hand: `Group.ofLeftAxioms` and `Group.ofRightAxioms` (in
`Algebra/Group/MinimalAxioms.lean`) build a group from three of the five.

`1`, `*` and `⁻¹` come from core's `One`, `Mul` and `Inv` classes, as in Mathlib. -/

universe u

namespace My

class Monoid (M : Type u) extends Mul M, One M where
  protected mul_assoc : ∀ a b c : M, a * b * c = a * (b * c)
  protected one_mul : ∀ a : M, 1 * a = a
  protected mul_one : ∀ a : M, a * 1 = a

class CommMonoid (M : Type u) extends Monoid M where
  protected mul_comm : ∀ a b : M, a * b = b * a

class Group (G : Type u) extends Monoid G, Inv G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  protected mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

-- (Mathlib: the same two parents)
class CommGroup (G : Type u) extends Group G, CommMonoid G

section Monoid

variable {M : Type u} [Monoid M]

-- the axioms, as theorems outside the class namespaces (as in Mathlib)
theorem mul_assoc (a b c : M) : a * b * c = a * (b * c) :=
  Monoid.mul_assoc a b c

theorem one_mul (a : M) : 1 * a = a :=
  Monoid.one_mul a

theorem mul_one (a : M) : a * 1 = a :=
  Monoid.mul_one a

instance Monoid.to_isAssociative : Std.Associative (λ (a b : M) => a * b) :=
  ⟨mul_assoc⟩

end Monoid

section Group

variable {G : Type u} [Group G]

theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 :=
  Group.mul_inv_cancel a

end Group

theorem mul_comm {M : Type u} [CommMonoid M] (a b : M) : a * b = b * a :=
  CommMonoid.mul_comm a b

instance CommMonoid.to_isCommutative {M : Type u} [CommMonoid M] :
    Std.Commutative (λ (a b : M) => a * b) :=
  ⟨CommMonoid.mul_comm⟩

end My
