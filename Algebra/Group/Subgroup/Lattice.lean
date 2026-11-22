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
  mul_mem' := by
    intro a b (ha : a = 1) (hb : b = 1)
    show a * b = 1
    rw [ha, hb]
    exact mul_one 1
  one_mem' := rfl
  inv_mem' := by
    intro x (hx : x = 1)
    rw [← inv_eq_one] at hx
    exact hx
  }⟩

instance : Top (Subgroup G) := ⟨{
  carrier := Set.univ
  mul_mem' := by
    intro _ _ _ _
    trivial
  one_mem' := trivial
  inv_mem' := by
    intro _ _
    trivial
  }⟩

instance : Min (Subgroup G) := ⟨fun H K => {
  carrier := {x | x ∈ H ∧ x ∈ K}
  mul_mem' := by
    rintro a b
    rintro ⟨hah, hak⟩ ⟨hbh, hbk⟩
    show (a * b) ∈ H ∧ (a * b) ∈ K
    exact ⟨H.mul_mem hah hbh, K.mul_mem hak hbk⟩
  one_mem' := ⟨H.one_mem, K.one_mem⟩
  inv_mem' := by
    rintro _ ⟨hh, hk⟩
    exact ⟨H.inv_mem hh, K.inv_mem hk⟩
  }⟩

theorem mem_bot {x : G} : x ∈ (⊥ : Subgroup G) ↔ x = 1 := by
  rfl

theorem mem_top (x : G) : x ∈ (⊤ : Subgroup G) :=
  trivial

theorem mem_inf {p p' : Subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
  rfl

theorem eq_bot_iff_forall (H : Subgroup G) : H = ⊥ ↔ ∀ x, x ∈ H → x = 1 := by
  constructor
  · intro h _ hx
    subst h
    exact mem_bot.mp hx
  · intro h
    apply Subgroup.ext
    intro x
    rw [mem_bot]
    constructor
    · exact h x
    · intro h1
      subst h1
      exact H.one_mem

theorem eq_top_iff' (H : Subgroup G) : H = ⊤ ↔ ∀ x : G, x ∈ H := by
  constructor
  · intro h; subst h
    exact λ x => mem_top x
  · intro h
    apply Subgroup.ext
    intro x
    exact ⟨λ _ => mem_top x, λ _ => h x⟩

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
