/-! # Preorders and partial orders

Mathlib: `Mathlib/Order/Defs/PartialOrder.lean`.

A preorder is a reflexive, transitive `≤`; a partial order is also antisymmetric. These are
what `Monotone`, `GaloisConnection` and order isomorphisms are stated for; `Subgroup G` and
(later) `Set α` are partial orders.

Mathlib's `Preorder` also has a `<` field, with default `a < b := a ≤ b ∧ ¬b ≤ a`; here there
is no `<` yet (not in Mathlib): add it when something needs strict inequalities. -/

universe u

namespace My

class Preorder (α : Type u) extends LE α where
  protected le_refl : ∀ a : α, a ≤ a
  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

class PartialOrder (α : Type u) extends Preorder α where
  protected le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

section Preorder

variable {α : Type u} [Preorder α] {a b c : α}

theorem le_refl (a : α) : a ≤ a :=
  sorry

-- `le_refl` with `a` implicit, for when Lean can find it
theorem le_rfl : a ≤ a :=
  sorry

theorem le_trans : a ≤ b → b ≤ c → a ≤ c :=
  sorry

theorem le_of_eq (hab : a = b) : a ≤ b :=
  sorry

theorem ge_of_eq (hab : a = b) : b ≤ a :=
  sorry

-- lets `calc` chain `≤` steps
instance : @Trans α α α LE.le LE.le LE.le :=
  sorry

end Preorder

section PartialOrder

variable {α : Type u} [PartialOrder α] {a b : α}

theorem le_antisymm : a ≤ b → b ≤ a → a = b :=
  sorry

theorem le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  sorry

-- two elements with the same lower bounds are equal
theorem eq_of_forall_le_iff (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  sorry

end PartialOrder

end My
