import Algebra.Group.Hom
import Algebra.Data.Set

/-! # Subgroups

Mathlib: `Mathlib/Algebra/Group/Subgroup/Defs.lean`.

A subgroup is a set (its `carrier`) closed under `*`, `1` and `⁻¹`. Mathlib builds it as
`Subgroup extends Submonoid extends Subsemigroup`, with the same field names as here.

`x ∈ H` means `x ∈ H.carrier`, and `(H : Set G)` is the carrier; the fields are primed
(`mul_mem'`) and the unprimed theorems (`H.mul_mem`) are the API.

A subgroup is also a group in its own right: `↥H`, the type of elements `⟨x, hx⟩` with
`hx : x ∈ H`. -/

universe u v

namespace My

structure Subgroup (G : Type u) [Group G] where
  carrier : Set G
  mul_mem' {a b : G} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem' : (1 : G) ∈ carrier
  inv_mem' {x : G} : x ∈ carrier → x⁻¹ ∈ carrier

namespace Subgroup

variable {G : Type u} [Group G]

instance : Membership G (Subgroup G) := ⟨fun H x => x ∈ H.carrier⟩

attribute [coe] Subgroup.carrier

instance : CoeTC (Subgroup G) (Set G) := ⟨Subgroup.carrier⟩

theorem mem_carrier {H : Subgroup G} {x : G} : x ∈ H.carrier ↔ x ∈ H :=
  Iff.rfl

-- (Mathlib: `SetLike.mem_coe`)
theorem mem_coe {H : Subgroup G} {x : G} : x ∈ (H : Set G) ↔ x ∈ H :=
  Iff.rfl

-- two subgroups with the same elements are equal (the closure proofs don't matter)
theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
  sorry

variable (H : Subgroup G) {x y : G}

protected theorem one_mem : (1 : G) ∈ H :=
  sorry

protected theorem mul_mem : x ∈ H → y ∈ H → x * y ∈ H :=
  sorry

protected theorem inv_mem : x ∈ H → x⁻¹ ∈ H :=
  sorry

theorem inv_mem_iff : x⁻¹ ∈ H ↔ x ∈ H :=
  sorry

theorem mul_mem_cancel_left (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
  sorry

theorem mul_mem_cancel_right (h : x ∈ H) : y * x ∈ H ↔ y ∈ H :=
  sorry

/-! ### Inclusion `H ≤ K`

Mathlib gets `≤` from `H ⊆ K` on carriers and proves `le_refl` etc. once for every partial
order; here they are stated for subgroups only. -/

instance : LE (Subgroup G) := ⟨fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K⟩

theorem le_def {H K : Subgroup G} : H ≤ K ↔ ∀ ⦃x⦄, x ∈ H → x ∈ K :=
  sorry

protected theorem le_refl : H ≤ H :=
  sorry

protected theorem le_trans {H K L : Subgroup G} (hHK : H ≤ K) (hKL : K ≤ L) : H ≤ L :=
  sorry

protected theorem le_antisymm {H K : Subgroup G} (hHK : H ≤ K) (hKH : K ≤ H) : H = K :=
  sorry

/-! ### A subgroup as a group -/

instance : CoeSort (Subgroup G) (Type u) := ⟨fun H => {x : G // x ∈ H}⟩

instance toGroup : Group H where
  mul a b := ⟨a.val * b.val, H.mul_mem a.property b.property⟩
  one := ⟨1, H.one_mem⟩
  inv a := ⟨a.val⁻¹, H.inv_mem a.property⟩
  mul_assoc := sorry
  one_mul := sorry
  inv_mul_cancel := sorry

-- the operations of `↥H` are those of `G` (`↑x` is `x.val`; equality in `↥H` is `Subtype.ext`)
theorem coe_mul (x y : H) : ((x * y : H) : G) = x * y :=
  sorry

theorem coe_inv (x : H) : ((x⁻¹ : H) : G) = (x : G)⁻¹ :=
  sorry

theorem coe_one : ((1 : H) : G) = 1 :=
  sorry

-- the inclusion `↥H → G`, as a hom
def subtype : H →* G where
  toFun := Subtype.val
  map_one' := sorry
  map_mul' := sorry

theorem subtype_apply {H : Subgroup G} (x : H) : H.subtype x = x :=
  sorry

theorem subtype_injective : Function.Injective H.subtype :=
  sorry

end Subgroup
end My
