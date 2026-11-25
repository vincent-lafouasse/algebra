import Algebra.Group.Equiv

/-! # Automorphisms and conjugation

Mathlib: `Mathlib/Algebra/Group/End.lean`.

`MulAut G` is `G ≃* G`, made a group under composition. It is a `def` (not an `abbrev`) as
in Mathlib, so the group structure only shows up when you write `MulAut G`.

Mathlib's convention: `e₁ * e₂` is "first `e₂`, then `e₁`", like function composition, so
`e₁ * e₂ = e₂.trans e₁`. -/

universe u

namespace My

def MulAut (G : Type u) [Group G] : Type u :=
  G ≃* G

namespace MulAut

variable {G : Type u} [Group G]

instance : CoeFun (MulAut G) (fun _ => G → G) :=
  ⟨fun e => (MulEquiv.toEquiv e).toFun⟩

instance : Group (MulAut G) where
  mul e₁ e₂ := MulEquiv.trans e₂ e₁
  one := MulEquiv.refl G
  inv := MulEquiv.symm
  mul_assoc := λ _ _ _ => rfl
  one_mul := by
    intro a
    show a.trans (MulEquiv.refl G) = a
    rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

theorem mul_def (e₁ e₂ : MulAut G) : e₁ * e₂ = MulEquiv.trans e₂ e₁ :=
  rfl

theorem one_def : (1 : MulAut G) = MulEquiv.refl G :=
  rfl

theorem inv_def (e : MulAut G) : e⁻¹ = MulEquiv.symm e :=
  rfl

theorem mul_apply (e₁ e₂ : MulAut G) (x : G) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

theorem one_apply (x : G) : (1 : MulAut G) x = x :=
  rfl

theorem inv_apply (e : MulAut G) (x : G) : e⁻¹ x = MulEquiv.symm e x :=
  rfl

/-! ### Conjugation

`conj g` is the inner automorphism `x ↦ g * x * g⁻¹`, and `conj` itself is a hom. -/

def conj : G →* MulAut G where
  toFun g :=
    { toFun := fun x => g * x * g⁻¹
      invFun := fun x => g⁻¹ * x * g
      left_inv := by
        intro x
        show g⁻¹ * (g * x * g⁻¹) * g = x
        rw [mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left]
      right_inv := by
        intro x
        show g * (g⁻¹ * x * g) * g⁻¹ = x
        rw [mul_assoc, mul_inv_cancel_right, mul_inv_cancel_left]
      map_mul' := by
        intro x y
        apply Eq.symm
        calc
          g * x * g⁻¹ * (g * y * g⁻¹)
          _ = g * x * (g⁻¹ * g) * y * g⁻¹ := by simp only [mul_assoc]
          _ = g * x * y * g⁻¹ := by rw [inv_mul_cancel, mul_one]
          _ = g * (x * y) * g⁻¹ := by simp only [mul_assoc] }
  map_one' := by
    apply MulEquiv.ext
    intro x
    show 1 * x * 1⁻¹ = x
    rw [one_mul, inv_one, mul_one]
  map_mul' := by
    intro x y
    apply MulEquiv.ext
    intro a
    show x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹
    calc
      x * y * a * (x * y)⁻¹
      _ = x * y * a * (y⁻¹ * x⁻¹) := by rw [mul_inv_rev]
      _ = x * (y * a * y⁻¹) * x⁻¹ := by simp only [mul_assoc]

theorem conj_apply (g x : G) : conj g x = g * x * g⁻¹ :=
  rfl

theorem conj_symm_apply (g x : G) : MulEquiv.symm (conj g) x = g⁻¹ * x * g :=
  rfl

theorem conj_inv_apply (g x : G) : (conj g)⁻¹ x = g⁻¹ * x * g :=
  rfl

end MulAut

end My
