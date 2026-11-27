import Algebra.GroupTheory.QuotientGroup.Defs
import Algebra.Group.Subgroup.Closure
import Base.Order.Hom.Basic

/-! # The first isomorphism theorem

Mathlib: `Mathlib/GroupTheory/QuotientGroup/Basic.lean`.

A hom `φ : G →* H` that kills `N` factors through `G ⧸ N` (`lift`). With `N = ker φ` the
factored map is injective (`kerLift`), and onto its range (`rangeKerLift`): so
`G ⧸ ker φ ≃* range φ`. -/

universe u v

namespace My

namespace QuotientGroup

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-! ### The universal property -/

def lift (N : Subgroup G) [N.Normal] (φ : G →* H) (HN : N ≤ φ.ker) : G ⧸ N →* H :=
  sorry

theorem lift_mk (N : Subgroup G) [N.Normal] {φ : G →* H} (HN : N ≤ φ.ker) (g : G) :
    lift N φ HN g = φ g :=
  sorry

/-! ### Through the kernel -/

variable (φ : G →* H)

def kerLift : G ⧸ φ.ker →* H :=
  sorry

theorem kerLift_mk (g : G) : kerLift φ g = φ g :=
  sorry

theorem kerLift_injective : Function.Injective (kerLift φ) :=
  sorry

-- the same map, with its codomain cut down to the range
def rangeKerLift : G ⧸ φ.ker →* φ.range :=
  sorry

theorem rangeKerLift_injective : Function.Injective (rangeKerLift φ) :=
  sorry

theorem rangeKerLift_surjective : Function.Surjective (rangeKerLift φ) :=
  sorry

/-! ### The theorem -/

noncomputable def quotientKerEquivRange : G ⧸ φ.ker ≃* φ.range :=
  sorry

-- a surjective hom: G ⧸ ker φ ≃* H
noncomputable def quotientKerEquivOfSurjective (hφ : Function.Surjective φ) : G ⧸ φ.ker ≃* H :=
  sorry

/-! ### Maps between quotients

(Mathlib: `Mathlib/GroupTheory/QuotientGroup/Defs.lean`.) A hom `f : G →* H` that sends `N`
into `K` induces `G ⧸ N →* H ⧸ K`: `lift` applied to `G → H → H ⧸ K`. -/

section Map

variable {G : Type u} {H : Type v} [Group G] [Group H] (N : Subgroup G) [N.Normal]

def map (K : Subgroup H) [K.Normal] (f : G →* H) (h : N ≤ K.comap f) : G ⧸ N →* H ⧸ K :=
  sorry

theorem map_mk (K : Subgroup H) [K.Normal] (f : G →* H) (h : N ≤ K.comap f) (x : G) :
    map N K f h x = (f x : H ⧸ K) :=
  sorry

end Map

/-! ### The second isomorphism theorem

`H ⧸ (H ∩ N) ≃* HN ⧸ N`, for `N` normal. `H ∩ N` and `N` are written `N.subgroupOf H` and
`N.subgroupOf (H ⊔ N)`: subgroups of `↥H` and of `↥(H ⊔ N)`, since a quotient `K ⧸ L` needs
`L` to be a subgroup of `K`. Proof idea: the first isomorphism theorem, for
`H → H ⊔ N → (H ⊔ N) ⧸ N`. -/

section SndIsomorphismThm

variable {G : Type u} [Group G]

noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [hN : N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  sorry

end SndIsomorphismThm

/-! ### The third isomorphism theorem

`(G ⧸ N) ⧸ (K ⧸ N) ≃* G ⧸ K`, for `N ≤ K` both normal. `K ⧸ N` is written
`K.map (mk' N)`: the image of `K` in `G ⧸ N`. Proof idea: `map N K (MonoidHom.id G) h`
is surjective, with kernel `K.map (mk' N)`. -/

section ThirdIsoThm

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal] (K : Subgroup G) [nK : K.Normal]

-- the image of a normal subgroup under the (surjective) quotient map is normal
instance map_normal : (K.map (QuotientGroup.mk' N)).Normal :=
  sorry

-- `h : N ≤ K` is an explicit argument (Mathlib: a section `variable`)
def quotientQuotientEquivQuotient (h : N ≤ K) : (G ⧸ N) ⧸ K.map (QuotientGroup.mk' N) ≃* G ⧸ K :=
  sorry

theorem quotientQuotientEquivQuotient_apply_mk (h : N ≤ K) (x : G) :
    quotientQuotientEquivQuotient N K h ((x : G ⧸ N) : (G ⧸ N) ⧸ K.map (QuotientGroup.mk' N)) =
      (x : G ⧸ K) :=
  sorry

theorem quotientQuotientEquivQuotient_symm_mk (h : N ≤ K) (x : G) :
    MulEquiv.symm (quotientQuotientEquivQuotient N K h) (x : G ⧸ K) =
      ((x : G ⧸ N) : (G ⧸ N) ⧸ K.map (QuotientGroup.mk' N)) :=
  sorry

end ThirdIsoThm

/-! ### The correspondence theorem

Subgroups of `G ⧸ N` correspond to subgroups of `G` containing `N`, in an order-preserving
way: `comap (mk' N)` one way, `map (mk' N)` the other. `Set.Ici N` is the set of subgroups
above `N`. -/

section CorrespTheorem

variable {G : Type u} [Group G]

theorem le_comap_mk' (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) :
    N ≤ Subgroup.comap (QuotientGroup.mk' N) H :=
  sorry

def comapMk'OrderIso (N : Subgroup G) [hn : N.Normal] : Subgroup (G ⧸ N) ≃o Set.Ici N :=
  sorry

end CorrespTheorem

end QuotientGroup

end My
