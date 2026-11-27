import Algebra.Group.Subgroup.Map
import Algebra.Group.End

/-! # Normal subgroups

Mathlib: `Mathlib/Algebra/Group/Subgroup/Defs.lean` (the class),
`Mathlib/Algebra/Group/Subgroup/Basic.lean`, `Mathlib/Algebra/Group/Subgroup/Ker.lean`,
`Mathlib/Algebra/Group/Subgroup/Map.lean`.

`Normal` is a class, so that a quotient `G ⧸ N` can find the proof by itself. Lemmas that
*use* normality take it as an explicit argument `(nH : H.Normal)` (Mathlib's convention), so
you write `nH.mem_comm h`. -/

universe u v

namespace My

namespace Subgroup

variable {G : Type u} [Group G]

class Normal (H : Subgroup G) : Prop where
  conj_mem : ∀ n, n ∈ H → ∀ g : G, g * n * g⁻¹ ∈ H

-- conjugating the other way round also stays in H
theorem Normal.conj_mem' {H : Subgroup G} (nH : H.Normal) (n : G) (hn : n ∈ H) (g : G) :
    g⁻¹ * n * g ∈ H := by
  have h : g⁻¹ * n * g⁻¹⁻¹ ∈ H := nH.conj_mem n hn g⁻¹
  rw [inv_inv] at h
  exact h

theorem Normal.mem_comm {H : Subgroup G} (nH : H.Normal) {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  have h := nH.conj_mem (a * b) h a⁻¹
  rw [inv_inv] at h
  rw [← mul_assoc a⁻¹ a b] at h
  rw [inv_mul_cancel] at h
  rw [one_mul] at h
  exact h

theorem Normal.mem_comm_iff {H : Subgroup G} (nH : H.Normal) {a b : G} : a * b ∈ H ↔ b * a ∈ H :=
  Iff.intro (Normal.mem_comm nH) (Normal.mem_comm nH)

instance normal_bot : (⊥ : Subgroup G).Normal where
  conj_mem : ∀ n, n ∈ ⊥ → ∀ g : G, g * n * g⁻¹ ∈ ⊥ := by
    intro n hn g
    rw [mem_bot] at hn
    subst hn
    rw [mem_bot]
    rw [mul_one]
    rw [mul_inv_cancel]

instance normal_top : (⊤ : Subgroup G).Normal where
  conj_mem : ∀ n, n ∈ ⊤ → ∀ g : G, g * n * g⁻¹ ∈ ⊤ :=
    λ n _ g => mem_top (g * n * g⁻¹)

instance normal_inf_normal (H K : Subgroup G) [H.Normal] [K.Normal] : (H ⊓ K).Normal where
  conj_mem : ∀ n, n ∈ H ⊓ K → ∀ g : G, g * n * g⁻¹ ∈ H ⊓ K :=
    λ n ⟨hh, hk⟩ g => ⟨Normal.conj_mem n hh g, Normal.conj_mem n hk g⟩

-- in a commutative group every subgroup is normal (Mathlib: for `[IsMulCommutative G]`)
theorem normal_of_isMulCommutative {G : Type u} [CommGroup G] (H : Subgroup G) : H.Normal :=
  sorry

-- normal = invariant under every inner automorphism
theorem normal_iff_map_conj_eq {H : Subgroup G} :
    H.Normal ↔ ∀ g : G, map (MulEquiv.toMonoidHom (MulAut.conj g)) H = H :=
  sorry

variable {N : Type v} [Group N]

-- the image of a normal subgroup is normal *in the range*; under a surjective hom, in N
theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G →* N) (hf : Function.Surjective f) :
    (map f H).Normal :=
  sorry

instance normal_comap {H : Subgroup N} [H.Normal] (f : G →* N) : (comap f H).Normal :=
  sorry

-- `N ∩ H` is normal in `H` when `N` is normal in `G` (a special case of `normal_comap`)
instance normal_subgroupOf {H N : Subgroup G} [N.Normal] : (N.subgroupOf H).Normal :=
  sorry

end Subgroup

instance MonoidHom.normal_ker {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.ker.Normal :=
  sorry

end My
