import Algebra.Normal
import Algebra.Core.Relation

universe u

namespace My

open Group

namespace Subgroup

variable {G : Type u} [Group G]

-- aN = { a * n | n ∈ N }, as a predicate on G
def leftCoset (a : G) (N : Subgroup G) : G → Prop := λ x => ∃ n ∈ N, x = a * n

-- Na = { n * a | n ∈ N }
def rightCoset (N : Subgroup G) (a : G) : G → Prop := λ x => ∃ n ∈ N, x = n * a

-- the coset relation: a ~ b ↔ a⁻¹b ∈ N
def leftRel (N : Subgroup G) : G → G → Prop := λ a b => a⁻¹ * b ∈ N

theorem leftRel_iff (N : Subgroup G) (a b : G) : leftRel N a b ↔ a⁻¹ * b ∈ N := Iff.rfl

theorem leftCoset_eq_eqvClass (N : Subgroup G) (a : G) :
    leftCoset a N = eqvClass (leftRel N) a := by
  funext x
  rw [mem_eqvClass_iff]
  rw [leftRel_iff]
  unfold leftCoset
  apply propext
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h
    rw [eq_inv_mul_of_mul_eq hz.2.symm] at hz
    exact hz.1
  · intro h
    refine ⟨a⁻¹ * x, ?_⟩
    refine ⟨h, ?_⟩
    rw [mul_inv_cancel_left]

theorem leftRel_refl {N : Subgroup G} (x : G) : leftRel N x x := by
  rw [leftRel_iff]
  rw [inv_mul_cancel]
  exact N.one_mem

theorem leftRel_symm {N : Subgroup G} {x y : G} (h : leftRel N x y) : leftRel N y x := by
  rw [leftRel_iff]
  rw [leftRel_iff] at h
  have h' := N.inv_mem h
  rw [inv_prod] at h'
  rw [Group.inv_inv] at h'
  exact h'

theorem leftRel_trans {N : Subgroup G} {x y z : G}
    (hxy : leftRel N x y) (hyz : leftRel N y z) : leftRel N x z := by
  rw [leftRel_iff]
  rw [leftRel_iff] at hxy
  rw [leftRel_iff] at hyz
  rw [← mul_inv_cancel_left y z]
  rw [← mul_assoc]
  exact N.mul_mem hxy hyz

-- reflexive: one_mem, symmetric: inv_mem + inv_prod, transitive: mul_mem
theorem leftRel_equivalence (N : Subgroup G) : Equivalence (leftRel N) where
  refl := leftRel_refl
  symm := leftRel_symm
  trans := leftRel_trans

-- x ∈ aN ↔ a⁻¹x ∈ N
theorem mem_leftCoset_iff (N : Subgroup G) (a x : G) :
    leftCoset a N x ↔ a⁻¹ * x ∈ N := by
  rw [leftCoset_eq_eqvClass]
  rw [← leftRel_iff]
  rw [mem_eqvClass_iff]

-- x ∈ Na ↔ xa⁻¹ ∈ N
theorem mem_rightCoset_iff (N : Subgroup G) (a x : G) :
    rightCoset N a x ↔ x * a⁻¹ ∈ N :=
  sorry

theorem mem_leftCoset_self (N : Subgroup G) (b : G) : leftCoset b N b := by
  rw [leftCoset_eq_eqvClass]
  exact mem_eqvClass_self (leftRel_equivalence N) b

-- aN = bN ↔ a⁻¹b ∈ N
theorem leftCoset_eq_iff (N : Subgroup G) (a b : G) :
    leftCoset a N = leftCoset b N ↔ a⁻¹ * b ∈ N := by
  rw [← mem_leftCoset_iff]
  rw [leftCoset_eq_eqvClass, leftCoset_eq_eqvClass]
  rw [eqvClass_eq_iff (leftRel_equivalence N) a b]
  rw [mem_eqvClass_iff]

-- the book's definition: N is normal iff aN = Na for every a
theorem normal_iff_cosets (N : Subgroup G) :
    N.Normal ↔ ∀ a : G, leftCoset a N = rightCoset N a :=
  sorry

-- a `def`, not an `instance`: each subgroup gives a different setoid on the same G
def leftSetoid (N : Subgroup G) : Setoid G :=
  ⟨leftRel N, leftRel_equivalence N⟩

end Subgroup
end My
