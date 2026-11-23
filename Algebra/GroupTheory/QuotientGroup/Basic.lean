import Algebra.GroupTheory.QuotientGroup.Defs

/-! # The first isomorphism theorem

Mathlib: `Mathlib/GroupTheory/QuotientGroup/Basic.lean`.

A hom `φ : G →* M` that kills `N` factors through `G ⧸ N` (`lift`). With `N = ker φ` the
factored map is injective (`kerLift`), and onto its range (`rangeKerLift`): so
`G ⧸ ker φ ≃* range φ`. -/

universe u v

namespace My

namespace QuotientGroup

variable {G : Type u} {M : Type v} [Group G] [Group M]

/-! ### The universal property -/

def lift (N : Subgroup G) [N.Normal] (φ : G →* M) (HN : N ≤ φ.ker) : G ⧸ N →* M :=
  MonoidHom.mk' (Quotient.lift φ sorry) sorry

theorem lift_mk {N : Subgroup G} [N.Normal] {φ : G →* M} (HN : N ≤ φ.ker) (g : G) :
    lift N φ HN g = φ g :=
  sorry

/-! ### Through the kernel -/

variable (φ : G →* M)

def kerLift : G ⧸ φ.ker →* M :=
  lift φ.ker φ (Subgroup.le_refl _)

theorem kerLift_mk (g : G) : kerLift φ g = φ g :=
  sorry

theorem kerLift_injective : Function.Injective (kerLift φ) :=
  sorry

-- the same map, with its codomain cut down to the range
def rangeKerLift : G ⧸ φ.ker →* φ.range :=
  lift φ.ker φ.rangeRestrict sorry

theorem rangeKerLift_injective : Function.Injective (rangeKerLift φ) :=
  sorry

theorem rangeKerLift_surjective : Function.Surjective (rangeKerLift φ) :=
  sorry

/-! ### The theorem -/

noncomputable def quotientKerEquivRange : G ⧸ φ.ker ≃* φ.range :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

-- a surjective hom: G ⧸ ker φ ≃* M
noncomputable def quotientKerEquivOfSurjective (hφ : Function.Surjective φ) : G ⧸ φ.ker ≃* M :=
  MulEquiv.ofBijective (kerLift φ) ⟨kerLift_injective φ, sorry⟩

end QuotientGroup

end My
