import Algebra.Group.Subgroup.Defs

/-! # Cosets

Mathlib: `Mathlib/GroupTheory/Coset/Defs.lean`, `Mathlib/GroupTheory/Coset/Basic.lean`,
`Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` (for `a • s`).

The left coset `aH` is written `a • (H : Set G)`: the set `a • s = {a * y | y ∈ s}`.
(Mathlib only turns on `a • s` for sets after `open Pointwise`.)

`leftRel H` is the relation "same left coset", `x ~ y ↔ x⁻¹ * y ∈ H`, packaged as a
`Setoid` (core's structure: a relation `r` with a proof `iseqv` that it is an equivalence).
Its quotient is `G ⧸ H`, in `Algebra/GroupTheory/QuotientGroup/Defs.lean`. -/

universe u

namespace My

/-! ### `a • s` -/

instance Set.smulSet {α : Type u} [Mul α] : SMul α (Set α) := ⟨fun a s => {x | ∃ y, y ∈ s ∧ a * y = x}⟩

theorem Set.mem_smul_set {α : Type u} [Mul α] {a : α} {s : Set α} {x : α} :
    x ∈ a • s ↔ ∃ y ∈ s, a * y = x :=
  sorry

variable {α : Type u} [Group α]

theorem mem_leftCoset_iff {s : Set α} {x : α} (a : α) : x ∈ a • s ↔ a⁻¹ * x ∈ s :=
  sorry

theorem mem_own_leftCoset (s : Subgroup α) (a : α) : a ∈ a • (s : Set α) :=
  sorry

theorem leftCoset_eq_iff (s : Subgroup α) {x y : α} :
    x • (s : Set α) = y • (s : Set α) ↔ x⁻¹ * y ∈ s :=
  sorry

/-! ### The relation "same left coset" -/

namespace QuotientGroup

def leftRel (s : Subgroup α) : Setoid α where
  r x y := x⁻¹ * y ∈ s
  iseqv := sorry

theorem leftRel_apply {s : Subgroup α} {x y : α} : (leftRel s).r x y ↔ x⁻¹ * y ∈ s :=
  sorry

def rightRel (s : Subgroup α) : Setoid α where
  r x y := y * x⁻¹ ∈ s
  iseqv := sorry

theorem rightRel_apply {s : Subgroup α} {x y : α} : (rightRel s).r x y ↔ y * x⁻¹ ∈ s :=
  sorry

end QuotientGroup
end My
