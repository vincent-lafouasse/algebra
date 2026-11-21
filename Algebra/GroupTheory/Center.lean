import Algebra.Group.Subgroup.Normal

/-! # The center

Mathlib: `Mathlib/GroupTheory/Subgroup/Center.lean`.

`center G` is the set of elements that commute with everything. -/

universe u

namespace My

namespace Subgroup

variable (G : Type u) [Group G]

def center : Subgroup G where
  carrier := {z | ∀ g : G, g * z = z * g}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

variable {G}

theorem mem_center_iff {z : G} : z ∈ center G ↔ ∀ g : G, g * z = z * g :=
  sorry

instance : (center G).Normal :=
  sorry

end Subgroup

theorem CommGroup.center_eq_top {G : Type u} [CommGroup G] : Subgroup.center G = ⊤ :=
  sorry

-- (not in Mathlib) conjugation by g is the identity exactly when g is central
theorem MulAut.ker_conj {G : Type u} [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G :=
  sorry

end My
