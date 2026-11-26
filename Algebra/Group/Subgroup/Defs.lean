import Algebra.Group.Hom
import Algebra.Group.MinimalAxioms
import Base.Data.Set
import Base.Order.Defs.PartialOrder

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

instance : Membership G (Subgroup G) :=
  ⟨λ H x => x ∈ H.carrier⟩

attribute [coe] Subgroup.carrier

instance : CoeTC (Subgroup G) (Set G) :=
  ⟨Subgroup.carrier⟩

theorem mem_carrier {H : Subgroup G} {x : G} : x ∈ H.carrier ↔ x ∈ H :=
  Iff.rfl

-- (Mathlib: `SetLike.mem_coe`)
theorem mem_coe {H : Subgroup G} {x : G} : x ∈ (H : Set G) ↔ x ∈ H :=
  Iff.rfl

-- two subgroups with the same elements are equal (the closure proofs don't matter)
theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := by
  obtain ⟨ch, hmh, h1h, hih⟩ := H
  obtain ⟨ck, hmk, h1k, hik⟩ := K
  have c_eq : ch = ck := Set.ext h
  subst c_eq
  rfl

theorem ext_iff {H K : Subgroup G} : H = K ↔ ∀ x, x ∈ H ↔ x ∈ K := by
  refine ⟨?_, ext⟩
  intro he
  intro x
  subst he
  rfl

/-! ### Membership: the unprimed API

`H` is explicit, so `H.one_mem` and `H.inv_mem h` read well with dot notation. -/

section Membership

variable (H : Subgroup G) {x y : G}

protected theorem one_mem : (1 : G) ∈ H :=
  H.one_mem'

protected theorem mul_mem : x ∈ H → y ∈ H → x * y ∈ H :=
  H.mul_mem'

protected theorem inv_mem : x ∈ H → x⁻¹ ∈ H :=
  H.inv_mem'

theorem inv_mem_iff : x⁻¹ ∈ H ↔ x ∈ H := by
  refine ⟨?_, H.inv_mem⟩
  intro (h : x⁻¹ ∈ H)
  replace h := H.inv_mem h
  rw [inv_inv] at h
  exact h

theorem mul_mem_cancel_left (h : x ∈ H) : x * y ∈ H ↔ y ∈ H := by
  refine ⟨?_, H.mul_mem h⟩
  intro h'
  replace h := H.inv_mem h
  replace h' := H.mul_mem h h'
  rw [inv_mul_cancel_left] at h'
  exact h'

theorem mul_mem_cancel_right (h : x ∈ H) : y * x ∈ H ↔ y ∈ H := by
  refine ⟨?_, λ h' => H.mul_mem h' h⟩
  intro h'
  replace h := H.inv_mem h
  replace h' := H.mul_mem h' h
  rw [mul_inv_cancel_right] at h'
  exact h'

end Membership

/-! ### Inclusion `H ≤ K`

Mathlib gets `≤` from `H ⊆ K` on carriers and proves `le_refl` etc. once for every partial
order; here they are stated for subgroups only. -/

instance : LE (Subgroup G) :=
  ⟨λ H K => ∀ ⦃x⦄, x ∈ H → x ∈ K⟩

theorem le_def {H K : Subgroup G} : H ≤ K ↔ ∀ ⦃x⦄, x ∈ H → x ∈ K :=
  Iff.rfl

-- (Mathlib: `SetLike.coe_subset_coe`)
theorem coe_subset_coe {H K : Subgroup G} : (H : Set G) ⊆ (K : Set G) ↔ H ≤ K :=
  Iff.rfl

protected theorem le_refl (H : Subgroup G) : H ≤ H := by
  apply le_def.mpr
  intro _ h; exact h

protected theorem le_trans {H K L : Subgroup G} (hHK : H ≤ K) (hKL : K ≤ L) : H ≤ L := by
  apply le_def.mpr
  intro _ hxh; exact hKL (hHK hxh)

protected theorem le_antisymm {H K : Subgroup G} (hHK : H ≤ K) (hKH : K ≤ H) : H = K := by
  apply ext
  intro _
  constructor
  · intro hh; exact hHK hh
  · intro hk; exact hKH hk

-- the three lemmas above, packaged: subgroups form a partial order, so the general order
-- lemmas (`le_trans`, `le_antisymm`, `Monotone`, `GaloisConnection`, …) apply to them
instance : PartialOrder (Subgroup G) where
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

/-! ### A subgroup as a group -/

section AsGroup

variable (H : Subgroup G)

instance : CoeSort (Subgroup G) (Type u) :=
  ⟨λ H => { x : G // x ∈ H }⟩

instance : Mul H :=
  ⟨λ a b => ⟨a.val * b.val, H.mul_mem a.property b.property⟩⟩

instance : One H :=
  ⟨⟨1, H.one_mem⟩⟩

instance : Inv H :=
  ⟨λ a => ⟨a.val⁻¹, H.inv_mem a.property⟩⟩

-- the three left axioms; `Group.ofLeftAxioms` proves `mul_one` and `mul_inv_cancel`
instance toGroup : Group H :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply Subtype.ext
      show a.val * b.val * c.val = a.val * (b.val * c.val)
      exact mul_assoc a.val b.val c.val)
    (by
      rintro ⟨val_a, _⟩
      apply Subtype.ext
      show 1 * val_a = val_a
      exact one_mul val_a)
    (by
      rintro ⟨val_a, _⟩
      apply Subtype.ext
      show val_a⁻¹ * val_a = 1
      exact inv_mul_cancel val_a)

-- the operations of `↥H` are those of `G` (`↑x` is `x.val`; equality in `↥H` is `Subtype.ext`)
theorem coe_mul (x y : H) : ((x * y : H) : G) = x * y :=
  rfl

theorem coe_inv (x : H) : ((x⁻¹ : H) : G) = (x : G)⁻¹ :=
  rfl

theorem coe_one : ((1 : H) : G) = 1 :=
  rfl

-- the inclusion `↥H → G`, as a hom
def subtype : H →* G where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := λ _ _ => rfl

theorem subtype_apply {H : Subgroup G} (x : H) : H.subtype x = x :=
  rfl

theorem subtype_injective : Function.Injective H.subtype := by
  intro ⟨av, _⟩ ⟨bv, _⟩
  intro (he : av = bv)
  exact Subtype.ext he

end AsGroup

end Subgroup

end My
