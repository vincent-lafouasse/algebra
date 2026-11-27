import Base.Data.Set.Lattice

/-! # Disjointness

Mathlib: `Mathlib/Order/Disjoint.lean`, `Mathlib/Data/Set/Disjoint.lean` (`Set.disjoint_left`).

`Disjoint a b`: the only thing below both is `⊥`. For sets that is "no common element". Mathlib
asks for `[OrderBot α]` (a `⊥` that is below everything); here `[Bot α]` stands in. Double cosets
use it: two double cosets are equal or disjoint. -/

universe u

namespace My

variable {α : Type u} [PartialOrder α] [Bot α]

def Disjoint (a b : α) : Prop :=
  sorry

theorem disjoint_def {a b : α} : Disjoint a b ↔ ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥ :=
  sorry

theorem disjoint_comm {a b : α} : Disjoint a b ↔ Disjoint b a :=
  sorry

theorem Disjoint.symm {a b : α} (h : Disjoint a b) : Disjoint b a :=
  sorry

theorem Set.disjoint_left {β : Type u} {s t : Set β} : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  sorry

end My
