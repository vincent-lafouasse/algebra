import Algebra.Group.Equiv
import Algebra.Group.Units.Equiv
import Algebra.Group.MinimalAxioms

/-! # Automorphisms and conjugation

Mathlib: `Mathlib/Algebra/Group/End.lean`.

`MulAut G` is `G ≃* G`, made a group under composition. It is an `abbrev`, as in Mathlib
(which made it one in 2026; it used to be a `def`): Lean sees through it, so every `MulEquiv`
lemma (`symm_apply_apply`, …) and the `MulEquiv` coercion to functions apply to `MulAut G`
directly, and `rw` with them works.

Mathlib's convention: `e₁ * e₂` is "first `e₂`, then `e₁`", like function composition, so
`e₁ * e₂ = e₂.trans e₁`. -/

universe u

namespace My

/-! ### Permutations

`Equiv.Perm α` (`α ≃ α`, in `Base/Logic/Equiv.lean`) is a group under composition, with the
same conventions as `MulAut` below: `f * g` is "first `g`, then `f`". -/

namespace Equiv.Perm

variable {α : Type u}

instance : Mul (Perm α) :=
  sorry

instance : One (Perm α) :=
  sorry

instance : Inv (Perm α) :=
  sorry

-- the three left axioms; `Group.ofLeftAxioms` proves the rest (as for `MulAut`)
instance permGroup : Group (Perm α) :=
  sorry

theorem mul_apply (f g : Perm α) (x : α) : (f * g) x = f (g x) :=
  sorry

theorem one_apply (x : α) : (1 : Perm α) x = x :=
  sorry

theorem one_def : (1 : Perm α) = Equiv.refl α :=
  sorry

theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  sorry

theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  sorry

-- the same three, as equations of functions
theorem coe_mul (f g : Perm α) : ((f * g : Perm α) : α → α) = f ∘ g :=
  sorry

theorem coe_one : ((1 : Perm α) : α → α) = id :=
  sorry

theorem coe_inv (f : Perm α) : ((f⁻¹ : Perm α) : α → α) = f.symm :=
  sorry

-- moving `f` across an equation
theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  sorry

theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  sorry

end Equiv.Perm

/-! ### Composing translations

Mathlib: `Mathlib/Algebra/Group/End.lean`. The translations themselves are in
`Algebra/Group/Units/Equiv.lean`.

`a ↦ mulLeft a` is a hom `G → Perm G` (`mulLeft_mul`, `mulLeft_one`), and an injective one:
that is Cayley's theorem (`Algebra/GroupTheory/GroupAction.lean`). Right translation reverses
the order: `mulRight (a * b) = mulRight b * mulRight a`. -/

namespace Equiv

variable {G : Type u} [Group G]

/-! #### `a ↦ mulLeft a` is a hom, `a ↦ mulRight a` an anti-hom -/

section

variable (a b : G)

theorem mulLeft_one : Equiv.mulLeft (1 : G) = 1 :=
  sorry

theorem mulRight_one : Equiv.mulRight (1 : G) = 1 :=
  sorry

theorem mulLeft_mul : Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b :=
  sorry

-- the order reverses
theorem mulRight_mul : Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a :=
  sorry

theorem inv_mulLeft : (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹ :=
  sorry

theorem inv_mulRight : (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹ :=
  sorry

theorem pow_mulLeft (n : Nat) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) :=
  sorry

theorem pow_mulRight (n : Nat) : Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n) :=
  sorry

theorem zpow_mulLeft (n : Int) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) :=
  sorry

theorem zpow_mulRight (n : Int) : Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n) :=
  sorry

end

end Equiv

abbrev MulAut (G : Type u) [Group G] : Type u :=
  G ≃* G

namespace MulAut

variable {G : Type u} [Group G]

instance : Mul (MulAut G) :=
  ⟨λ e₁ e₂ => MulEquiv.trans e₂ e₁⟩

instance : One (MulAut G) :=
  ⟨MulEquiv.refl G⟩

instance : Inv (MulAut G) :=
  ⟨MulEquiv.symm⟩

-- the three left axioms; `Group.ofLeftAxioms` proves `mul_one` and `mul_inv_cancel`
instance : Group (MulAut G) :=
  Group.ofLeftAxioms (λ _ _ _ => rfl)
    (by
      intro a
      show a.trans (MulEquiv.refl G) = a
      rfl)
    MulEquiv.self_trans_symm

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
    { toFun := λ x => g * x * g⁻¹
      invFun := λ x => g⁻¹ * x * g
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
