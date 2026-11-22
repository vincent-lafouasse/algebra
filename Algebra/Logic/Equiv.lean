import Algebra.Logic.Function

/-! # Bijections `α ≃ β`

Mathlib: `Mathlib/Logic/Equiv/Defs.lean`.

An equivalence is a function *with a chosen inverse*, not a bijective function: the inverse is
data. `e x` applies it; `e.symm` is the inverse. -/

universe u v w x

namespace My

structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

infixl:25 " ≃ " => Equiv

namespace Equiv

variable {α : Sort u} {β : Sort v} {γ : Sort w}

attribute [coe] Equiv.toFun

instance : CoeFun (α ≃ β) (fun _ => α → β) := ⟨Equiv.toFun⟩

-- two equivalences with the same forward function are equal (the inverse is determined)
theorem ext {e e' : α ≃ β} (h : ∀ x, e x = e' x) : e = e' := by
  obtain ⟨f, g, hl, hr⟩ := e
  obtain ⟨f', g', hl', hr'⟩ := e'
  have hfe : f = f' := by funext x; exact h x
  have hge : g = g' := by funext y; sorry
  subst hfe
  subst hge
  rfl

protected def refl (α : Sort u) : α ≃ α where
  toFun := id
  invFun := id
  left_inv := sorry
  right_inv := sorry

protected def symm (e : α ≃ β) : β ≃ α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := sorry
  right_inv := sorry

protected def trans (e : α ≃ β) (e' : β ≃ γ) : α ≃ γ where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  left_inv := sorry
  right_inv := sorry

theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm :=
  sorry

theorem refl_apply (x : α) : Equiv.refl α x = x :=
  sorry

theorem trans_apply (e : α ≃ β) (e' : β ≃ γ) (x : α) : e.trans e' x = e' (e x) :=
  sorry

theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
  sorry

theorem apply_symm_apply (e : α ≃ β) (y : β) : e (e.symm y) = y :=
  sorry

theorem symm_symm (e : α ≃ β) : e.symm.symm = e :=
  sorry

theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e :=
  sorry

theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e :=
  sorry

theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α :=
  sorry

theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β :=
  sorry

theorem trans_assoc {δ : Sort x} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
  sorry

protected theorem injective (e : α ≃ β) : Function.Injective e :=
  sorry

protected theorem surjective (e : α ≃ β) : Function.Surjective e :=
  sorry

protected theorem bijective (e : α ≃ β) : Function.Bijective e :=
  sorry

-- the converse: a bijective function gets an inverse, by choice (`Function.surjInv`)
noncomputable def ofBijective (f : α → β) (hf : Function.Bijective f) : α ≃ β where
  toFun := f
  invFun := Function.surjInv hf.2
  left_inv := sorry
  right_inv := sorry

theorem ofBijective_apply (f : α → β) (hf : Function.Bijective f) (x : α) :
    ofBijective f hf x = f x :=
  sorry

end Equiv
end My
