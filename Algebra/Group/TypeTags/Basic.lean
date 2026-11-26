import Algebra.Group.MinimalAxioms
import Base.Logic.Equiv

/-! # `Multiplicative α`: an additive structure, written multiplicatively

Mathlib: `Mathlib/Algebra/Group/TypeTags/Basic.lean`.

`Group` here is multiplicative, so `(ℤ, +)` is not a `Group` as is. `Multiplicative ℤ` is a
copy of `ℤ` whose `*` is `+`, `1` is `0` and `⁻¹` is `-`. `ofAdd` and `toAdd` translate, and
are the identity underneath: `ofAdd (x + y) = ofAdd x * ofAdd y`.

Mathlib makes `Multiplicative α` a group for any additive group `α`; there is no additive
group class here yet, so only `Multiplicative ℤ` is a group (not in Mathlib: the instance is
for `ℤ` only). This is the manual version of what the additive codegen will automate. -/

universe u

namespace My

def Multiplicative (α : Type u) : Type u :=
  α

namespace Multiplicative

variable {α : Type u}

/-- `x : α`, seen in `Multiplicative α`. -/
def ofAdd : α ≃ Multiplicative α where
  toFun x := x
  invFun x := x
  left_inv := sorry
  right_inv := sorry

/-- The way back. -/
def toAdd : Multiplicative α ≃ α :=
  ofAdd.symm

theorem toAdd_ofAdd (x : α) : toAdd (ofAdd x) = x :=
  sorry

theorem ofAdd_toAdd (x : Multiplicative α) : ofAdd (toAdd x) = x :=
  sorry

instance [Add α] : Mul (Multiplicative α) :=
  ⟨λ x y => ofAdd (toAdd x + toAdd y)⟩

instance [Zero α] : One (Multiplicative α) :=
  ⟨ofAdd 0⟩

instance [Neg α] : Inv (Multiplicative α) :=
  ⟨λ x => ofAdd (-toAdd x)⟩

theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y :=
  sorry

theorem toAdd_mul [Add α] (x y : Multiplicative α) : toAdd (x * y) = toAdd x + toAdd y :=
  sorry

theorem ofAdd_zero [Zero α] : ofAdd (0 : α) = 1 :=
  sorry

theorem toAdd_one [Zero α] : toAdd (1 : Multiplicative α) = 0 :=
  sorry

theorem ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹ :=
  sorry

theorem toAdd_inv [Neg α] (x : Multiplicative α) : toAdd x⁻¹ = -toAdd x :=
  sorry

-- `(ℤ, +, 0, -)` written as `(*, 1, ⁻¹)`: the group axioms are `Int.add_assoc`, …
instance : CommGroup (Multiplicative Int) :=
  { Group.ofLeftAxioms sorry sorry sorry with mul_comm := sorry }

end Multiplicative

end My
