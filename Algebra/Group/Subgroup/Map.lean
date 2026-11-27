import Algebra.Group.Subgroup.Ker
import Base.Order.GaloisConnection.Defs

/-! # Image and preimage of a subgroup

Mathlib: `Mathlib/Algebra/Group/Subgroup/Map.lean`.

`map f H` is the image `f(H)`, `comap f K` the preimage `f⁻¹(K)`. Both live in the
`Subgroup` namespace and take the hom first.

Their carriers are the set image `f '' H` and preimage `f ⁻¹' K`, so the set lemmas of
`Base/Data/Set/Image.lean` apply through `coe_map` and `coe_comap`. In particular,
`map_le_iff_le_comap` is `Set.image_subset_iff` read through `coe_subset_coe`. -/

universe u v w

namespace My

variable {G : Type u} {N : Type v} {P : Type w} [Group G] [Group N] [Group P]

namespace Subgroup

def map (f : G →* N) (H : Subgroup G) : Subgroup N where
  carrier := f '' (H : Set G)
  mul_mem' := by
    intro ya yb ⟨xa, hxa, hfa⟩ ⟨xb, hxb, hfb⟩
    refine ⟨xa * xb, H.mul_mem hxa hxb, ?_⟩
    rw [← hfa, ← hfb]
    exact f.map_mul xa xb
  one_mem' :=
    ⟨1, H.one_mem, f.map_one⟩
  inv_mem' := by
    intro y ⟨x, hx, hf⟩
    refine ⟨x⁻¹, H.inv_mem hx, ?_⟩
    rw [f.map_inv]
    rw [inv_inj]
    exact hf

theorem coe_map (f : G →* N) (K : Subgroup G) : (map f K : Set N) = f '' (K : Set G) :=
  rfl

theorem mem_map {f : G →* N} {K : Subgroup G} {y : N} : y ∈ map f K ↔ ∃ x ∈ K, f x = y :=
  Iff.rfl

def comap (f : G →* N) (K : Subgroup N) : Subgroup G where
  carrier := f ⁻¹' (K : Set N)
  mul_mem' := by
    intro _ _ ha hb
    rw [Set.mem_preimage]
    rw [f.map_mul]
    exact K.mul_mem ha hb
  one_mem' := by
    rw [Set.mem_preimage]
    rw [f.map_one]
    exact K.one_mem
  inv_mem' := by
    intro x hx
    rw [Set.mem_preimage]
    rw [f.map_inv]
    exact K.inv_mem hx

theorem coe_comap (K : Subgroup N) (f : G →* N) : (comap f K : Set G) = f ⁻¹' (K : Set N) :=
  rfl

theorem mem_comap {K : Subgroup N} {f : G →* N} {x : G} : x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl

theorem map_id (K : Subgroup G) : map (MonoidHom.id G) K = K :=
  sorry

theorem map_map (K : Subgroup G) (g : N →* P) (f : G →* N) : map g (map f K) = map (g ∘* f) K :=
  sorry

theorem comap_comap (K : Subgroup P) (g : N →* P) (f : G →* N) :
    comap f (comap g K) = comap (g ∘* f) K :=
  sorry

-- map and comap are adjoint: f(K) ⊆ H iff K ⊆ f⁻¹(H)
theorem map_le_iff_le_comap {f : G →* N} {K : Subgroup G} {H : Subgroup N} :
    map f K ≤ H ↔ K ≤ comap f H :=
  sorry

-- the same, as a Galois connection: the general lemmas then apply to `map f` and `comap f`
theorem gc_map_comap (f : G →* N) : GaloisConnection (map f) (comap f) :=
  sorry

-- the unit of that connection
theorem le_comap_map (f : G →* N) (H : Subgroup G) : H ≤ comap f (map f H) :=
  sorry

/-! ### A subgroup of `K`, from a subgroup of `G`

`H.subgroupOf K` is `H ∩ K`, seen inside `↥K`: the elements of `K` that lie in `H`. It is
how `H ⧸ (H ⊓ N)` is written in the second isomorphism theorem. -/

def subgroupOf (H K : Subgroup G) : Subgroup K :=
  sorry

theorem mem_subgroupOf {H K : Subgroup G} {h : K} : h ∈ H.subgroupOf K ↔ (h : G) ∈ H :=
  sorry

end Subgroup

namespace MonoidHom

theorem comap_bot (f : G →* N) : Subgroup.comap f ⊥ = f.ker :=
  sorry

theorem range_eq_map (f : G →* N) : f.range = Subgroup.map f ⊤ :=
  sorry

end MonoidHom

end My
