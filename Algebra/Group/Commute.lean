import Algebra.Group.Basic

/-! # Commuting elements

Mathlib: `Mathlib/Algebra/Group/Commute/Defs.lean`, `Mathlib/Algebra/Group/Commute/Basic.lean`.

`Commute a b` says `a * b = b * a`. It is a definition, so that lemmas about it can be used
with dot notation (`h.symm`, `h.inv_right`); `commute_iff_eq` is the way in and out.
(Mathlib defines it as `SemiconjBy a b b`, which unfolds to the same equation.) -/

universe u

namespace My

@[irreducible]
def Commute {S : Type u} [Mul S] (a b : S) : Prop :=
  a * b = b * a

theorem commute_iff_eq {S : Type u} [Mul S] (a b : S) : Commute a b ↔ a * b = b * a := by
  unfold Commute
  rfl

namespace Commute

section Mul

variable {S : Type u} [Mul S] {a b : S}

protected theorem eq (h : Commute a b) : a * b = b * a :=
  (commute_iff_eq a b).1 h

-- (not in Mathlib: there `Commute` is transparent, so `h` itself proves `Commute a b`)
protected theorem of_eq (h : a * b = b * a) : Commute a b :=
  (commute_iff_eq a b).2 h

protected theorem refl (a : S) : Commute a a :=
  Commute.of_eq rfl

protected theorem symm (h : Commute a b) : Commute b a :=
  h |> Commute.eq |> Eq.symm |> Commute.of_eq

protected theorem symm_iff : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

end Mul

variable {G : Type u} [Group G] {a b c : G}

theorem one_left (a : G) : Commute 1 a :=
  have h : 1 * a = a * 1 := by rw [mul_one, one_mul]
  Commute.of_eq h

theorem one_right (a : G) : Commute a 1 :=
  Commute.symm (one_left a)

theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) := by
  apply Commute.of_eq
  calc
    a * (b * c)
    _ = (a * b) * c := by rw [mul_assoc]
    _ = (b * a) * c := by rw [hab.eq]
    _ = b * (a * c) := by rw [← mul_assoc]
    _ = b * (c * a) := by rw [hac.eq]
    _ = b * c * a := by rw [← mul_assoc]

theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  Commute.symm (mul_right hac.symm hbc.symm)

-- swapping two neighbours that commute, inside a longer product
protected theorem right_comm (h : Commute b c) (a : G) : a * b * c = a * c * b :=
  sorry

protected theorem left_comm (h : Commute a b) (c : G) : a * (b * c) = b * (a * c) :=
  sorry

protected theorem mul_mul_mul_comm (hbc : Commute b c) (a d : G) :
    a * b * (c * d) = a * c * (b * d) :=
  sorry

theorem inv_right (h : Commute a b) : Commute a b⁻¹ := by
  apply Commute.of_eq
  rw [eq_inv_mul_iff_mul_eq]
  rw [← mul_assoc]
  rw [mul_inv_eq_iff_eq_mul]
  exact h |> Commute.symm |> Commute.eq

theorem inv_left (h : Commute a b) : Commute a⁻¹ b :=
  h |> Commute.symm |> inv_right |> Commute.symm

theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b := by
  refine ⟨?_, inv_right⟩
  intro h
  replace h := inv_right h
  rw [My.inv_inv] at h
  exact h

theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b := by
  rw [Commute.symm_iff]
  rw [inv_right_iff]
  rw [Commute.symm_iff]

theorem inv_left_self (a : G) : Commute a⁻¹ a :=
  inv_left (Commute.refl a)

theorem inv_right_self (a : G) : Commute a a⁻¹ :=
  inv_right (Commute.refl a)

theorem inv_inv (h : Commute a b) : Commute a⁻¹ b⁻¹ :=
  h |> inv_left |> inv_right

-- oriented like Mathlib's: the inverses are on the left, so `rw` removes them
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b := by rw [inv_left_iff, inv_right_iff]

-- conjugating b by an element it commutes with does nothing
protected theorem inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b :=
  calc
    a⁻¹ * b * a
    _ = b * a⁻¹ * a := by rw [Commute.eq (inv_left h)]
    _ = b := by rw [inv_mul_cancel_right]

protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [mul_inv_eq_iff_eq_mul]
  exact h |> Commute.eq

-- the same two, bracketed the other way
theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b :=
  sorry

theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b :=
  sorry

-- `(ab)⁻¹ = b⁻¹a⁻¹` always; `a⁻¹b⁻¹` when they commute (Mathlib also calls it `Commute.inv`)
protected theorem mul_inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
  sorry

-- conjugating by the same `h` preserves commuting, both ways (`h` is an element here)
protected theorem conj_iff (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b :=
  sorry

protected theorem conj (comm : Commute a b) (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) :=
  sorry

end Commute

-- in a commutative group everything commutes (Mathlib states it for any `CommMagma`)
theorem Commute.all {G : Type u} [CommGroup G] (a b : G) : Commute a b :=
  mul_comm a b |> Commute.of_eq

end My
