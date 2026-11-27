import Base.Data.Set

/-! # Products of sets

Mathlib: `Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` (`Set.mul`, `Set.mem_mul`).

`s * t = {x * y | x ∈ s, y ∈ t}`. Mathlib only turns it on after `open Pointwise` (it is a
`scoped` instance there); here it is global, like `a • s` in `Coset.lean`.

`H * N` for subgroups (`Subgroup/Pointwise.lean`) and double cosets `H * {a} * K`
(`DoubleCoset.lean`) are written with it. -/

universe u

namespace My

namespace Set

variable {α : Type u} [Mul α] {s t s₁ s₂ t₁ t₂ : Set α} {a b : α}

instance mul : Mul (Set α) :=
  sorry

theorem mem_mul : a ∈ s * t ↔ ∃ x ∈ s, ∃ y ∈ t, x * y = a :=
  sorry

theorem mul_mem_mul (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t :=
  sorry

theorem mul_subset_mul (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ * s₂ ⊆ t₁ * t₂ :=
  sorry

end Set

end My
