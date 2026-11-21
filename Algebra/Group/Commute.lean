import Algebra.Group.Basic

/-! # Commuting elements

Mathlib: `Mathlib/Algebra/Group/Commute/Defs.lean`, `Mathlib/Algebra/Group/Commute/Basic.lean`.

`Commute a b` says `a * b = b * a`. It is a definition, so that lemmas about it can be used
with dot notation (`h.symm`, `h.inv_right`); `commute_iff_eq` is the way in and out.
(Mathlib defines it as `SemiconjBy a b b`, which unfolds to the same equation.) -/

universe u

namespace My

def Commute {S : Type u} [Mul S] (a b : S) : Prop := a * b = b * a

theorem commute_iff_eq {S : Type u} [Mul S] (a b : S) : Commute a b ↔ a * b = b * a :=
  sorry

namespace Commute

section Mul

variable {S : Type u} [Mul S] {a b : S}

protected theorem eq (h : Commute a b) : a * b = b * a :=
  sorry

protected theorem refl (a : S) : Commute a a :=
  sorry

protected theorem symm (h : Commute a b) : Commute b a :=
  sorry

protected theorem symm_iff : Commute a b ↔ Commute b a :=
  sorry

end Mul

variable {G : Type u} [Group G] {a b c : G}

theorem one_left (a : G) : Commute 1 a :=
  sorry

theorem one_right (a : G) : Commute a 1 :=
  sorry

theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  sorry

theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  sorry

theorem inv_right (h : Commute a b) : Commute a b⁻¹ :=
  sorry

theorem inv_left (h : Commute a b) : Commute a⁻¹ b :=
  sorry

theorem inv_inv (h : Commute a b) : Commute a⁻¹ b⁻¹ :=
  sorry

-- oriented like Mathlib's: the inverses are on the left, so `rw` removes them
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  sorry

theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b :=
  sorry

theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b :=
  sorry

-- conjugating b by an element it commutes with does nothing
protected theorem inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b :=
  sorry

protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b :=
  sorry

end Commute

-- in a commutative group everything commutes (Mathlib states it for any `CommMagma`)
theorem Commute.all {G : Type u} [CommGroup G] (a b : G) : Commute a b :=
  sorry

end My
