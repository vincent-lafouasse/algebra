/-! # Nontrivial types

Mathlib: `Mathlib/Basic/Nontrivial/Defs.lean`.

A type is nontrivial when it has two distinct elements. A simple group is required to be
nontrivial (the trivial group has only one normal subgroup, not two), so `IsSimpleGroup`
extends this class. -/

universe u

namespace My

class Nontrivial (α : Type u) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y

theorem exists_pair_ne (α : Type u) [Nontrivial α] : ∃ x y : α, x ≠ y :=
  sorry

-- every element has something different from it
theorem exists_ne {α : Type u} [Nontrivial α] (x : α) : ∃ y, y ≠ x :=
  sorry

end My
