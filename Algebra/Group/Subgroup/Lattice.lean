import Algebra.Group.Subgroup.Defs
import Algebra.Order.Notation

/-! # `⊥`, `⊤` and `⊓` for subgroups

Mathlib: `Mathlib/Algebra/Group/Subgroup/Lattice.lean`.

`⊥` is the trivial subgroup `{1}`, `⊤` is all of `G`, `H ⊓ K` is the intersection.
Mathlib makes `Subgroup G` a complete lattice and gets `bot_le`, `le_top`, `inf_le_left`, …
for free; here they are proved by hand. -/

universe u

namespace My
namespace Subgroup

variable {G : Type u} [Group G]

instance : Bot (Subgroup G) := ⟨{
  carrier := {x | x = 1}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry }⟩

instance : Top (Subgroup G) := ⟨{
  carrier := Set.univ
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry }⟩

instance : Min (Subgroup G) := ⟨fun H K => {
  carrier := {x | x ∈ H ∧ x ∈ K}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry }⟩

theorem mem_bot {x : G} : x ∈ (⊥ : Subgroup G) ↔ x = 1 :=
  sorry

theorem mem_top (x : G) : x ∈ (⊤ : Subgroup G) :=
  sorry

theorem mem_inf {p p' : Subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  sorry

theorem eq_bot_iff_forall (H : Subgroup G) : H = ⊥ ↔ ∀ x, x ∈ H → x = 1 :=
  sorry

theorem eq_top_iff' (H : Subgroup G) : H = ⊤ ↔ ∀ x : G, x ∈ H :=
  sorry

-- (Mathlib: the general order lemmas `bot_le`, `le_top`, `inf_le_left`, `inf_le_right`, `le_inf`)

protected theorem bot_le (H : Subgroup G) : ⊥ ≤ H :=
  sorry

protected theorem le_top (H : Subgroup G) : H ≤ ⊤ :=
  sorry

protected theorem inf_le_left (H K : Subgroup G) : H ⊓ K ≤ H :=
  sorry

protected theorem inf_le_right (H K : Subgroup G) : H ⊓ K ≤ K :=
  sorry

protected theorem le_inf {H K L : Subgroup G} (hK : L ≤ H) (hL : L ≤ K) : L ≤ H ⊓ K :=
  sorry

end Subgroup
end My
