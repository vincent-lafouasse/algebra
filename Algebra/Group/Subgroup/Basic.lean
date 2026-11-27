import Algebra.Group.Subgroup.Normal
import Algebra.Group.Subgroup.Closure

/-! # The normal closure of a set

Mathlib: `Mathlib/Algebra/Group/Subgroup/Basic.lean` (`Subgroup.normalClosure`).

`normalClosure s` is the smallest normal subgroup containing `s`. Mathlib builds it as the
`closure` of all conjugates of elements of `s` (`conjugatesOfSet s`); whatever the construction,
the interface is `subset_normalClosure`, `normalClosure_normal` and `normalClosure_le_normal`,
the same "smallest" shape as `closure`.

Presented groups are quotients of free groups by a normal closure: `⟨a, b | a² = b³ = 1⟩` is
`FreeGroup {a, b} ⧸ normalClosure {a², b³}`. -/

universe u

namespace My

namespace Subgroup

variable {G : Type u} [Group G] {s t : Set G}

def normalClosure (s : Set G) : Subgroup G :=
  sorry

theorem subset_normalClosure : s ⊆ (normalClosure s : Set G) :=
  sorry

instance normalClosure_normal : (normalClosure s).Normal :=
  sorry

-- the smallest one
theorem normalClosure_le_normal {N : Subgroup G} [N.Normal] (h : s ⊆ (N : Set G)) :
    normalClosure s ≤ N :=
  sorry

theorem normalClosure_mono (h : s ⊆ t) : normalClosure s ≤ normalClosure t :=
  sorry

theorem normalClosure_eq_self (H : Subgroup G) [H.Normal] : normalClosure (H : Set G) = H :=
  sorry

-- it contains the plain closure (Mathlib: `le_normalClosure`)
theorem le_normalClosure {H : Subgroup G} : H ≤ normalClosure (H : Set G) :=
  sorry

end Subgroup

end My
