import Algebra.GroupTheory.Center
import Algebra.Group.Commute

/-! # Centralizers

Mathlib: `Mathlib/GroupTheory/Subgroup/Centralizer.lean`.

`centralizer s` is the set of elements that commute with every element of the set `s`.
The centralizer of one element `g` is `centralizer {g}`. -/

universe u

namespace My

namespace Subgroup

variable {G : Type u} [Group G]

def centralizer (s : Set G) : Subgroup G where
  carrier := {g | ∀ h, h ∈ s → h * g = g * h}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

theorem mem_centralizer_iff {g : G} {s : Set G} : g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h :=
  sorry

theorem mem_centralizer_singleton_iff {g k : G} : k ∈ centralizer {g} ↔ Commute k g :=
  sorry

theorem center_le_centralizer (s : Set G) : center G ≤ centralizer s :=
  sorry

theorem centralizer_univ : centralizer (Set.univ : Set G) = center G :=
  sorry

end Subgroup

end My
