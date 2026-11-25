import Algebra.Group.Subgroup.Ker

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
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

theorem coe_map (f : G →* N) (K : Subgroup G) : (map f K : Set N) = f '' (K : Set G) :=
  rfl

theorem mem_map {f : G →* N} {K : Subgroup G} {y : N} : y ∈ map f K ↔ ∃ x ∈ K, f x = y :=
  sorry

def comap (f : G →* N) (K : Subgroup N) : Subgroup G where
  carrier := f ⁻¹' (K : Set N)
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

theorem coe_comap (f : G →* N) (K : Subgroup N) : (comap f K : Set G) = f ⁻¹' (K : Set N) :=
  rfl

theorem mem_comap {K : Subgroup N} {f : G →* N} {x : G} : x ∈ comap f K ↔ f x ∈ K :=
  sorry

theorem map_id (K : Subgroup G) : map (MonoidHom.id G) K = K :=
  sorry

theorem map_map (g : N →* P) (f : G →* N) (K : Subgroup G) : map g (map f K) = map (g ∘* f) K :=
  sorry

theorem comap_comap (K : Subgroup P) (g : N →* P) (f : G →* N) :
    comap f (comap g K) = comap (g ∘* f) K :=
  sorry

-- map and comap are adjoint: f(K) ⊆ H iff K ⊆ f⁻¹(H)
theorem map_le_iff_le_comap {f : G →* N} {K : Subgroup G} {H : Subgroup N} :
    map f K ≤ H ↔ K ≤ comap f H :=
  sorry

end Subgroup

namespace MonoidHom

theorem comap_bot (f : G →* N) : Subgroup.comap f ⊥ = f.ker :=
  sorry

theorem range_eq_map (f : G →* N) : f.range = Subgroup.map f ⊤ :=
  sorry

end MonoidHom

end My
