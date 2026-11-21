import Algebra.Group.Subgroup.Ker

/-! # Image and preimage of a subgroup

Mathlib: `Mathlib/Algebra/Group/Subgroup/Map.lean`.

`map f H` is the image `f(H)`, `comap f K` the preimage `f⁻¹(K)`. Both live in the
`Subgroup` namespace and take the hom first. -/

universe u v w

namespace My

variable {G : Type u} {N : Type v} {P : Type w} [Group G] [Group N] [Group P]

namespace Subgroup

def map (f : G →* N) (H : Subgroup G) : Subgroup N where
  carrier := {y | ∃ x, x ∈ H ∧ f x = y}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

theorem mem_map {f : G →* N} {K : Subgroup G} {y : N} : y ∈ map f K ↔ ∃ x ∈ K, f x = y :=
  sorry

def comap (f : G →* N) (K : Subgroup N) : Subgroup G where
  carrier := {x | f x ∈ K}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

theorem mem_comap {K : Subgroup N} {f : G →* N} {x : G} : x ∈ comap f K ↔ f x ∈ K :=
  sorry

theorem map_id (K : Subgroup G) : map (MonoidHom.id G) K = K :=
  sorry

theorem map_map (g : N →* P) (f : G →* N) (K : Subgroup G) :
    map g (map f K) = map (g.comp f) K :=
  sorry

theorem comap_comap (K : Subgroup P) (g : N →* P) (f : G →* N) :
    comap f (comap g K) = comap (g.comp f) K :=
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
