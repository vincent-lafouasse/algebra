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

variable {G : Type u} [Group G]

/-! ### Translating sets

Mathlib: `Mathlib/Algebra/Group/Pointwise/Set/Basic.lean`. Translating by `a` is a bijection with
inverse translation by `a⁻¹`, so an image under one is a preimage under the other. -/

namespace Set

variable {t : Set G} {a b : G}

theorem image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t := by
  apply Set.ext
  intro x
  rw [mem_image]
  rw [mem_preimage]
  apply Iff.intro
  · intro ⟨b, ⟨htb, h⟩⟩
    rw [← eq_inv_mul_iff_mul_eq] at h
    subst h
    exact htb
  · intro h
    refine ⟨a⁻¹ * x, ?_⟩
    refine ⟨h, ?_⟩
    rw [mul_inv_cancel_left]

theorem image_mul_left' : (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t := by
  rw [image_mul_left]
  rw [inv_inv]

theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  apply Set.ext
  intro x
  rw [mem_image]
  rw [mem_preimage]
  apply Iff.intro
  · intro ⟨x', ⟨ht, h⟩⟩
    rw [← eq_mul_inv_iff_mul_eq] at h
    rw [← h]
    exact ht
  · intro h
    refine ⟨x * b⁻¹, h, ?_⟩
    rw [inv_mul_cancel_right]

theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by
  rw [image_mul_right]
  rw [inv_inv]

-- the one `x` with `a * x = b`
theorem preimage_mul_left_singleton : (a * ·) ⁻¹' {b} = {a⁻¹ * b} := by
  apply Set.ext
  intro x
  rw [mem_preimage]
  rw [mem_singleton_iff]
  rw [mem_singleton_iff]
  rw [eq_inv_mul_iff_mul_eq]

theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  apply Set.ext
  intro x
  rw [mem_preimage]
  rw [mem_singleton_iff]
  rw [mem_singleton_iff]
  rw [eq_mul_inv_iff_mul_eq]

end Set

theorem leftCoset_eq_image_mul_left {s : Set G} : a • s = (a * ·) '' s := by
  apply Set.ext
  intro x
  rw [Set.mem_smul_set]
  rw [Set.mem_image]

theorem mem_leftCoset_iff {s : Set G} {x : G} (a : G) : x ∈ a • s ↔ a⁻¹ * x ∈ s := by
  rw [leftCoset_eq_image_mul_left]
  rw [Set.image_mul_left]
  rw [Set.mem_preimage]

theorem mem_own_leftCoset (H : Subgroup G) (a : G) : a ∈ a • (H : Set G) := by
  rw [mem_leftCoset_iff]
  rw [inv_mul_cancel]
  exact H.one_mem

theorem leftCoset_eq_iff (H : Subgroup G) {a b : G} :
    a • (H : Set G) = b • (H : Set G) ↔ a⁻¹ * b ∈ H := by
  rw [Set.ext_iff]
  simp only [mem_leftCoset_iff a]
  simp only [mem_leftCoset_iff b]
  simp only [Subgroup.mem_coe]
  apply Iff.intro
  · intro h
    apply (h b).mpr
    rw [inv_mul_cancel]
    exact H.one_mem
  · intro h x
    rw [← mul_mul_inv_mul_cancel a⁻¹ b x]
    rw [Subgroup.mul_mem_cancel_left H h]

/-! ### The relation "same left coset" -/

namespace QuotientGroup

def leftRel (H : Subgroup G) : Setoid G where
  r x y := x⁻¹ * y ∈ H
  iseqv :=
    { refl (a : G) := by
        rw [inv_mul_cancel]
        exact H.one_mem
      symm {a b : G} hab := by
        have h := H.inv_mem hab
        rw [mul_inv_rev] at h
        rw [inv_inv] at h
        exact h
      trans {x y z : G} hab hbc := by
        have h := H.mul_mem hab hbc
        rw [mul_mul_inv_mul_cancel] at h
        exact h }

theorem leftRel_apply {H : Subgroup G} {x y : G} : (leftRel H).r x y ↔ x⁻¹ * y ∈ H :=
  Iff.rfl

def rightRel (H : Subgroup G) : Setoid G :=
  sorry

theorem rightRel_apply {H : Subgroup G} {x y : G} : (rightRel H).r x y ↔ y * x⁻¹ ∈ H :=
  sorry

end QuotientGroup

end My
