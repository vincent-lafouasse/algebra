import Algebra.Subgroup

/-! # Commuting elements

`Commute a b` means `a * b = b * a`. It's a relation between two elements, not a `class`.
It's opaque on purpose: build one with `Commute.of_eq`, use one with `h.eq`, and otherwise
stay in the API. It only needs `Mul`; the lemmas add `Group` when they need inverses.

The closure lemmas (`one_right`, `mul_right`, `inv_right`) say that the elements commuting
with a fixed `c` form a subgroup: the centralizer of `c`. The center is what commutes
with everything, i.e. the intersection of all centralizers.

Powers (`Commute.pow_left`, `Commute.mul_pow`, …) live in `Pow.lean`. -/

universe u

namespace My

@[irreducible]
def Commute {α : Type u} [Mul α] (a b : α) : Prop := a * b = b * a

-- the boundary: unfold here, nowhere else
theorem commute_iff_eq {α : Type u} [Mul α] (a b : α) : Commute a b ↔ a * b = b * a := by
  unfold Commute
  rfl

namespace Commute

section Mul

variable {α : Type u} [Mul α] {a b : α}

theorem of_eq (h : a * b = b * a) : Commute a b := by
  rw [commute_iff_eq]
  exact h

-- use a commuting hypothesis as an equation: `h.eq`
theorem eq (h : Commute a b) : a * b = b * a := by
  rw [← commute_iff_eq]
  exact h

theorem refl (a : α) : Commute a a :=
  of_eq rfl

theorem symm (h : Commute a b) : Commute b a :=
  of_eq h.eq.symm

end Mul

section Group

open Group

variable {G : Type u} [Group G] {a b c : G}

theorem one_left (a : G) : Commute one a :=
  of_eq (by rw [one_mul, mul_one])

theorem one_right (a : G) : Commute a one :=
  (one_left a).symm

-- if a commutes with b and with c, it commutes with b * c
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) := by
  apply of_eq
  rw [mul_assoc]
  rw [← hac.eq]
  rw [← mul_assoc b a c]
  rw [← hab.eq]
  rw [mul_assoc]

theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  (mul_right hac.symm hbc.symm).symm

-- move a factor across (`eq_inv_mul_iff_mul_eq` and friends)
theorem inv_right (h : Commute a b) : Commute a b⁻¹ := by
  apply of_eq
  rw [eq_inv_mul_iff_mul_eq]
  rw [← mul_assoc]
  rw [mul_inv_eq_iff_eq_mul]
  exact h.symm.eq

theorem inv_left (h : Commute a b) : Commute a⁻¹ b :=
  (inv_right h.symm).symm

theorem inv_inv (h : Commute a b) : Commute a⁻¹ b⁻¹ := by
  apply inv_left
  apply inv_right
  exact h

theorem inv_inv_iff : Commute a b ↔ Commute a⁻¹ b⁻¹ :=
  sorry

theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b := by
  constructor
  · intro h
    have h' := inv_right h
    rw [Group.inv_inv] at h'
    exact h'
  · intro h
    exact inv_right h

theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b := by
  sorry

end Group

end Commute

/-! ### Centralizers and the center -/

namespace Subgroup

open Group

variable {G : Type u} [Group G]

-- everything that commutes with c: the closure proofs are the lemmas above
def centralizer (c : G) : Subgroup G where
  mem := λ x => Commute c x
  one_mem := sorry
  mul_mem := sorry
  inv_mem := sorry

theorem mem_centralizer_iff (c x : G) : x ∈ centralizer c ↔ Commute c x :=
  sorry

theorem mem_centralizer_self (c : G) : c ∈ centralizer c :=
  sorry

-- `mem_center` restated with `Commute`
theorem mem_center_iff_commute (x : G) : x ∈ center G ↔ ∀ g, Commute g x :=
  sorry

-- the center is the intersection of all the centralizers
theorem mem_center_iff_forall_mem_centralizer (x : G) :
    x ∈ center G ↔ ∀ g, x ∈ centralizer g :=
  sorry

theorem center_le_centralizer (c : G) : ∀ x, x ∈ center G → x ∈ centralizer c :=
  sorry

end Subgroup
end My
