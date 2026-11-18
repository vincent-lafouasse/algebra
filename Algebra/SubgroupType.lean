import Algebra.Subgroup

/-! # Subgroups as groups

A `Subgroup G` is a predicate on `G`. To talk about `range f` *as a group* (e.g. as the
target of an isomorphism), we turn a subgroup into a type: the elements of `G` that
belong to it, i.e. the subtype `{x : G // x ∈ S}`. Core Lean provides `Subtype`,
`Subtype.val` and `Subtype.ext`. -/

universe u

namespace My

open Group

namespace Subgroup

variable {G : Type u} [Group G]

-- `S` can be used where a type is expected: `(a : S)` means `a : {x : G // x ∈ S}`
instance : CoeSort (Subgroup G) (Type u) := ⟨λ S => {x : G // x ∈ S}⟩

-- two elements of S are equal if they are equal in G (`Subtype.ext`)
theorem val_inj {S : Subgroup G} {a b : S} (h : a.val = b.val) : a = b := by
  ext
  exact h

-- operations are computed in G; closure is what makes them land back in S
instance (S : Subgroup G) : Group S where
  mul a b := ⟨a.val * b.val, S.mul_mem a.property b.property⟩
  inv a := ⟨a.val⁻¹, S.inv_mem a.property⟩
  one := ⟨one, S.one_mem⟩
  mul_assoc := by
    intro a b c
    sorry
  one_mul := by
    intro a
    apply val_inj
    show one * a.val = a.val
    rw [one_mul]
  inv_mul_cancel := by
    intro a
    apply val_inj
    show a.val⁻¹ * a.val = one
    rw [inv_mul_cancel]

/-! ### API: what `val` does to the operations (all `rfl`) -/

theorem val_mul (S : Subgroup G) (a b : S) : (a * b).val = a.val * b.val :=
  sorry

theorem val_inv (S : Subgroup G) (a : S) : (a⁻¹).val = a.val⁻¹ :=
  sorry

theorem val_one (S : Subgroup G) : (one : S).val = one :=
  sorry

-- the inclusion S → G is a hom, and an injective one
def subtypeHom (S : Subgroup G) : S →* G :=
  sorry

theorem subtypeHom_apply (S : Subgroup G) (a : S) : subtypeHom S a = a.val :=
  sorry

theorem subtypeHom_injective (S : Subgroup G) : Function.Injective (subtypeHom S) :=
  sorry

end Subgroup
end My
