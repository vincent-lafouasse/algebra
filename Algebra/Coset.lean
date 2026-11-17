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

theorem inv_mul_mem_swap (N : Subgroup G) {a b : G} (h : a⁻¹ * b ∈ N) : b⁻¹ * a ∈ N := by
  have h' := N.inv_mem h
  rw [inv_prod] at h'
  rw [inv_inv] at h'
  exact h'

theorem in_own_coset (N : Subgroup G) (b : G) : leftCoset b N b := by
  rw [mem_leftCoset_iff]
  rw [inv_mul_cancel]
  exact N.one_mem

-- aN = bN ↔ a⁻¹b ∈ N
theorem leftCoset_eq_iff (N : Subgroup G) (a b : G) :
    leftCoset a N = leftCoset b N ↔ a⁻¹ * b ∈ N := by
  constructor
  · intro e
    have hb : leftCoset b N b := in_own_coset N b
    rw [← e] at hb
    rw [mem_leftCoset_iff] at hb
    exact hb
  · intro h_ainv_b
    funext x
    apply propext
    constructor
    · intro h
      rw [leftCoset] at h
      obtain ⟨z, hz⟩ := h
      rw [leftCoset]
      rw [hz.2]
      refine ⟨b⁻¹ * a * z, ?_⟩
      have h_binv_a := inv_mul_mem_swap N h_ainv_b
      refine ⟨N.mul_mem h_binv_a hz.1, ?_⟩
      rw [Group.mul_assoc]
      rw [← hz.2]
      rw [mul_inv_cancel_left]
    · intro h
      rw [leftCoset] at h
      obtain ⟨z, hz⟩ := h
      rw [leftCoset]
      rw [hz.2]
      refine ⟨a⁻¹ * b * z, ?_⟩
      refine ⟨N.mul_mem h_ainv_b hz.1, ?_⟩
      rw [Group.mul_assoc]
      rw [← hz.2]
      rw [mul_inv_cancel_left]

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
