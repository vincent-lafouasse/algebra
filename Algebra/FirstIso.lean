import Algebra.Quotient
import Algebra.Iso
import Algebra.SubgroupType

/-! # The first isomorphism theorem

For a hom `f : G →* H`, the map `G / ker f → range f`, `mk a ↦ f a`, is a well-defined
isomorphism of groups: `G / ker f ≃* range f`.

Plan: lift `f` to the quotient (well-defined because `ker f` is exactly what `f` cannot
see), show the lift is a hom, injective and surjective, then use `Iso.ofBijective`. -/

universe u v

namespace My

open Group Subgroup

-- note: inside `namespace Hom`, a bare `mk` means `Hom.mk` (the constructor),
-- so the quotient projection is written `QuotientGroup.mk`

namespace Hom

variable {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)

-- the kernel is f's blind spot: same image ↔ same coset of ker f
theorem eq_iff_mem_ker (a b : G) : f a = f b ↔ a⁻¹ * b ∈ ker f := by
  rw [Hom.mem_ker]
  rw [f.map_mul]
  rw [← eq_inv_mul_iff_mul_eq]
  rw [mul_one]
  rw [map_inv]
  rw [inv_inv]
  rw [eq_comm]

-- mk a ↦ f a, as an element of range f; via `Quotient.lift` and `eq_iff_mem_ker`
def kerLift : QuotientGroup (ker f) → range f :=
  Quotient.lift
    (λ (x : G) => ⟨f x, ⟨x, rfl⟩⟩)
    (by
      intro a b (eq : leftRel (ker f) a b)
      rw [leftRel_iff] at eq
      rw [← eq_iff_mem_ker] at eq
      ext
      show f a = f b
      exact eq)

theorem kerLift_mk (a : G) : (kerLift f (QuotientGroup.mk (ker f) a)).val = f a := 
  rfl

-- the lift is a hom: reduce to representatives, then `map_mul`
def kerLiftHom : QuotientGroup (ker f) →* range f where
  toFun := f.kerLift
  map_mul := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    rename_i x y
    show f.kerLift (QuotientGroup.mk (ker f) (x * y)) =
      f.kerLift (QuotientGroup.mk (ker f) x) *
      f.kerLift (QuotientGroup.mk (ker f) y)
    apply val_inj
    show f (x * y) = f x * f y
    exact f.map_mul x y

theorem kerLiftHom_mk (a : G) : (kerLiftHom f (QuotientGroup.mk (ker f) a)).val = f a :=
  rfl

-- injective: f a = f b → mk a = mk b (`eq_iff_mem_ker`, `mk_eq_mk_iff`)
theorem kerLiftHom_injective : Function.Injective (kerLiftHom f) := by
  intro a b eq
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i x y
  show QuotientGroup.mk (ker f) x = QuotientGroup.mk (ker f) y
  rw [QuotientGroup.mk_eq_mk_iff]
  change f.kerLiftHom (QuotientGroup.mk (ker f) x) =
         f.kerLiftHom (QuotientGroup.mk (ker f) y) at eq
  sorry

-- surjective: an element of range f is f a for some a, by definition
theorem kerLiftHom_surjective : Function.Surjective (kerLiftHom f) :=
  sorry

/-- **First isomorphism theorem**: `G / ker f ≃* range f`. -/
noncomputable def firstIso : QuotientGroup (ker f) ≃* range f :=
  sorry

theorem firstIso_mk (a : G) : ((firstIso f).toHom (QuotientGroup.mk (ker f) a)).val = f a :=
  sorry

end Hom
end My
