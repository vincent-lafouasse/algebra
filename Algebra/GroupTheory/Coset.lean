import Algebra.Group.Subgroup.Defs
import Base.Data.Set.Image

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

instance Set.smulSet {α : Type u} [Mul α] : SMul α (Set α) :=
  ⟨λ a s => {x | ∃ y, y ∈ s ∧ a * y = x}⟩

theorem Set.mem_smul_set {α : Type u} [Mul α] {a : α} {s : Set α} {x : α} :
    x ∈ a • s ↔ ∃ y ∈ s, a * y = x :=
  Iff.rfl

-- `a • s` is the image of `s` under left translation by `a` (Mathlib: `Set.image_smul`,
-- `(a • ·) '' t = a • t`, for any action; here `•` on sets is defined through `*`)
theorem Set.image_mul_left_eq_smul_set {α : Type u} [Mul α] {a : α} {s : Set α} :
    (a * ·) '' s = a • s :=
  rfl

variable {α : Type u} [Group α]

/-! ### Translating sets

Mathlib: `Mathlib/Algebra/Group/Pointwise/Set/Basic.lean`. Translating by `a` is a bijection with
inverse translation by `a⁻¹`, so an image under one is a preimage under the other. -/

namespace Set

variable {t : Set α} {a b : α}

theorem image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t :=
  sorry

theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t :=
  sorry

theorem image_mul_left' : (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t :=
  sorry

theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t :=
  sorry

-- the one `x` with `a * x = b`
theorem preimage_mul_left_singleton : (a * ·) ⁻¹' {b} = {a⁻¹ * b} :=
  sorry

theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} :=
  sorry

end Set

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
  r x y := sorry
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
