import Algebra.GroupTheory.Commutator
import Algebra.GroupTheory.QuotientGroup.Basic

/-! # The abelianization `Gᵃᵇ = G ⧸ G'`

Mathlib: `Mathlib/GroupTheory/Abelianization/Defs.lean`.

Quotienting by the commutator subgroup forces everything to commute, and nothing more: every
hom from `G` to a commutative group factors through `Gᵃᵇ`, uniquely (`lift`). It is the
"best commutative approximation" of `G`.

This is the first payoff of Noether 1's toolkit: `lift` is `QuotientGroup.lift` with the
hypothesis `commutator G ≤ f.ker` (`commutator_le_ker`), which holds because `f ⁅a, b⁆ =
⁅f a, f b⁆ = 1` in a commutative target.

Mathlib states `lift` for `[Group A] [IsMulCommutative A]`; here `[CommGroup A]`. -/

universe u v

namespace My

namespace Group

-- explicit binders: with a `sorry` body, a `variable` would be dropped from the signature
def Abelianization (G : Type u) [Group G] : Type u :=
  sorry

variable {G : Type u} [Group G]

instance : CommGroup (Abelianization G) :=
  sorry

namespace Abelianization

-- the projection `G → Gᵃᵇ`
def of : G →* Abelianization G :=
  sorry

theorem ker_of : of.ker = commutator G :=
  sorry

variable {A : Type v} [CommGroup A]

theorem commutator_le_ker (f : G →* A) : commutator G ≤ f.ker :=
  sorry

-- every hom to a commutative group factors through `Gᵃᵇ`, in exactly one way
def lift : (G →* A) ≃ (Abelianization G →* A) :=
  sorry

theorem lift_apply_of (f : G →* A) (x : G) : lift f (of x) = f x :=
  sorry

theorem lift_unique (f : G →* A) (φ : Abelianization G →* A) (hφ : ∀ x : G, φ (of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  sorry

theorem hom_ext (φ ψ : Abelianization G →* A) (h : φ ∘* of = ψ ∘* of) : φ = ψ :=
  sorry

end Abelianization

end Group

end My
