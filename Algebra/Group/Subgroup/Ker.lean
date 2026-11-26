import Algebra.Group.Subgroup.Lattice
import Base.Data.Set.Image

/-! # Kernel and range

Mathlib: `Mathlib/Algebra/Group/Subgroup/Ker.lean`.

The carrier of `f.range` is `Set.range f`, so the set lemmas (`Set.mem_range`, …) apply to it
through `coe_range`. -/

universe u v

namespace My

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]

def ker (f : G →* H) : Subgroup G where
  carrier := f ⁻¹' {1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    rw [Set.mem_preimage, Set.mem_singleton_iff] at ha
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hb
    calc
      f (a * b)
      _ = f a * f b := by rw [f.map_mul]
      _ = 1 * 1 := by rw [ha, hb]
      _ = 1 := by rw [one_mul]
  one_mem' := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact f.map_one
  inv_mem' := by
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [f.map_inv]
    exact inv_eq_one.mpr hx

theorem mem_ker {f : G →* H} {x : G} : x ∈ f.ker ↔ f x = 1 := by
  show x ∈ f ⁻¹' {1} ↔ f x = 1
  rw [Set.mem_preimage, Set.mem_singleton_iff]

def range (f : G →* H) : Subgroup H where
  carrier := Set.range f
  mul_mem' := by
    intro y₁ y₂ ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
    refine Exists.intro (x₁ * x₂) ?_
    calc
      f (x₁ * x₂)
      _ = f x₁ * f x₂ := by rw [f.map_mul]
      _ = y₁ * y₂ := by rw [h₁, h₂]
  one_mem' := Exists.intro 1 f.map_one
  inv_mem' := by
    intro y ⟨x, h⟩
    refine Exists.intro x⁻¹ ?_
    rw [f.map_inv]
    exact inv_inj.mpr h

theorem coe_range (f : G →* H) : (f.range : Set H) = Set.range f :=
  rfl

theorem mem_range {f : G →* H} {y : H} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

-- f identifies x and y exactly when they differ by an element of the kernel
theorem eq_iff (f : G →* H) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker := by
  rw [mem_ker]
  rw [f.map_mul]
  rw [f.map_inv]
  rw [inv_mul_eq_one]
  rw [eq_comm]

theorem ker_eq_bot_iff (f : G →* H) : f.ker = ⊥ ↔ Function.Injective f := by
  apply Iff.intro
  · intro h _ _ he
    rw [← inv_mul_eq_one] at he
    rw [← f.map_inv, ← f.map_mul] at he
    rw [← mem_ker, h] at he
    rw [Subgroup.mem_bot] at he
    exact eq_of_inv_mul_eq_one he
  · intro h_inj
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [mem_ker] at hx
    rw [← f.map_one] at hx
    exact h_inj hx

theorem ker_eq_bot (f : G →* H) (hf : Function.Injective f) : f.ker = ⊥ :=
  (ker_eq_bot_iff f).mpr hf

theorem range_eq_top {f : G →* H} : f.range = ⊤ ↔ Function.Surjective f := by
  apply Iff.intro
  · intro h y
    have hy : y ∈ ⊤ := Subgroup.mem_top y
    rw [← h] at hy
    exact hy
  · intro h_surj
    rw [Subgroup.eq_top_iff']
    intro y
    exact h_surj y

/-! ### Restricting the codomain to the range -/

def rangeRestrict (f : G →* H) : G →* f.range where
  toFun x := ⟨f x, x, rfl⟩
  map_one' := Subtype.ext f.map_one
  map_mul' := λ a b => Subtype.ext (f.map_mul a b)

theorem coe_rangeRestrict (f : G →* H) (x : G) : (f.rangeRestrict x : H) = f x := by
  obtain ⟨y, hv⟩ := f.rangeRestrict x
  obtain ⟨a, ha⟩ := hv
  show y = f x
  rw [← ha]
  sorry

theorem rangeRestrict_surjective (f : G →* H) : Function.Surjective f.rangeRestrict :=
  sorry

theorem ker_rangeRestrict (f : G →* H) : f.rangeRestrict.ker = f.ker :=
  sorry

end MonoidHom

end My
