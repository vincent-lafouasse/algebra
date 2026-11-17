import Algebra.Normal

universe u

namespace Algebra

open Group

namespace Subgroup

variable {G : Type u} [Group G]

-- aN = { a * n | n ∈ N }, as a predicate on G
def leftCoset (a : G) (N : Subgroup G) : G → Prop := λ x => ∃ n ∈ N, x = a * n

-- Na = { n * a | n ∈ N }
def rightCoset (N : Subgroup G) (a : G) : G → Prop := λ x => ∃ n ∈ N, x = n * a

-- x ∈ aN ↔ a⁻¹x ∈ N
theorem mem_leftCoset_iff (N : Subgroup G) (a x : G) :
    leftCoset a N x ↔ a⁻¹ * x ∈ N := by
  constructor
  · intro x_in_aN
    rw [leftCoset] at x_in_aN
    obtain ⟨z, hz⟩ := x_in_aN
    rw [hz.2]
    rw [inv_mul_cancel_left]
    exact hz.1
  · intro h
    rw [leftCoset]
    refine ⟨a⁻¹ * x, ?_⟩
    refine ⟨h, ?_⟩
    rw [mul_inv_cancel_left]

-- aN = bN ↔ a⁻¹b ∈ N
theorem leftCoset_eq_iff (N : Subgroup G) (a b : G) :
    leftCoset a N = leftCoset b N ↔ a⁻¹ * b ∈ N := by
  constructor
  · intro e
    have hb : leftCoset b N b := by
      rw [leftCoset]
      refine ⟨one, ?_⟩
      refine ⟨N.one_mem, ?_⟩
      rw [mul_one]
    rw [← e] at hb
    rw [leftCoset] at hb
    obtain ⟨z, hbz⟩ := hb
    rw [hbz.2]
    rw [inv_mul_cancel_left]
    exact hbz.1
  · intro h_ainv_b
    funext x
    sorry

-- the book's definition: N is normal iff aN = Na for every a
theorem normal_iff_cosets (N : Subgroup G) :
    N.Normal ↔ ∀ a : G, leftCoset a N = rightCoset N a :=
  sorry

-- the coset relation: a ~ b ↔ a⁻¹b ∈ N
def leftRel (N : Subgroup G) : G → G → Prop := λ a b => a⁻¹ * b ∈ N

theorem leftRel_iff (N : Subgroup G) (a b : G) : leftRel N a b ↔ a⁻¹ * b ∈ N :=
  sorry

-- reflexive: one_mem, symmetric: inv_mem + inv_prod, transitive: mul_mem
theorem leftRel_equivalence (N : Subgroup G) : Equivalence (leftRel N) :=
  sorry

-- a `def`, not an `instance`: each subgroup gives a different setoid on the same G
def leftSetoid (N : Subgroup G) : Setoid G :=
  ⟨leftRel N, leftRel_equivalence N⟩

end Subgroup
end Algebra
