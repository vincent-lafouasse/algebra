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
  one_mem' := sorry
  inv_mem' := sorry

theorem mem_ker {f : G →* H} {x : G} : x ∈ f.ker ↔ f x = 1 :=
  sorry

def range (f : G →* H) : Subgroup H where
  carrier := Set.range f
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

theorem coe_range (f : G →* H) : (f.range : Set H) = Set.range f :=
  rfl

theorem mem_range {f : G →* H} {y : H} : y ∈ f.range ↔ ∃ x, f x = y :=
  sorry

-- f identifies x and y exactly when they differ by an element of the kernel
theorem eq_iff (f : G →* H) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker :=
  sorry

theorem ker_eq_bot_iff (f : G →* H) : f.ker = ⊥ ↔ Function.Injective f :=
  sorry

theorem ker_eq_bot (f : G →* H) (hf : Function.Injective f) : f.ker = ⊥ :=
  sorry

theorem range_eq_top {f : G →* H} : f.range = ⊤ ↔ Function.Surjective f :=
  sorry

/-! ### Restricting the codomain to the range -/

def rangeRestrict (f : G →* H) : G →* f.range where
  toFun x := ⟨f x, sorry⟩
  map_one' := sorry
  map_mul' := sorry

theorem coe_rangeRestrict (f : G →* H) (x : G) : (f.rangeRestrict x : H) = f x :=
  sorry

theorem rangeRestrict_surjective (f : G →* H) : Function.Surjective f.rangeRestrict :=
  sorry

theorem ker_rangeRestrict (f : G →* H) : f.rangeRestrict.ker = f.ker :=
  sorry

end MonoidHom

end My
