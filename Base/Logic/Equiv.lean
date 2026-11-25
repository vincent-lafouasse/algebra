import Base.Logic.Function

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

instance : CoeFun (α ≃ β) (fun _ => α → β) :=
  ⟨Equiv.toFun⟩

-- two equivalences with the same forward function are equal (the inverse is determined)
theorem ext {e e' : α ≃ β} (h : ∀ x, e x = e' x) : e = e' := by
  obtain ⟨f, g, hl, _⟩ := e
  obtain ⟨f', g', _, hr'⟩ := e'
  have hfe : f = f' := funext h
  subst hfe
  have hge : g = g' := by
    funext y
    calc
      g y
      _ = g (f (g' y)) := by rw [hr']
      _ = g' y := by rw [hl]
  subst hge
  rfl

protected def refl (α : Sort u) : α ≃ α where
  toFun := id
  invFun := id
  left_inv := λ _ => rfl
  right_inv := λ _ => rfl

protected def symm (e : α ≃ β) : β ≃ α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

protected def trans (e : α ≃ β) (e' : β ≃ γ) : α ≃ γ where
  toFun := e'.toFun ∘ e.toFun
  invFun := e.invFun ∘ e'.invFun
  left_inv := by
    intro x
    repeat rw [Function.comp_apply]
    rw [e'.left_inv]
    rw [e.left_inv]
  right_inv := by
    intro y
    repeat rw [Function.comp_apply]
    rw [e.right_inv]
    rw [e'.right_inv]

theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm :=
  rfl

theorem refl_apply (x : α) : Equiv.refl α x = x :=
  rfl

theorem trans_apply (e : α ≃ β) (e' : β ≃ γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl

theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
  calc
    e.symm (e x)
    _ = e.invFun (e x) := rfl
    _ = x := by rw [e.left_inv]

theorem apply_symm_apply (e : α ≃ β) (y : β) : e (e.symm y) = y :=
  calc
    e (e.symm y)
    _ = e.toFun (e.invFun y) := rfl
    _ = y := by rw [e.right_inv]

theorem symm_symm (e : α ≃ β) : e.symm.symm = e :=
  rfl

theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e :=
  rfl

theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e :=
  rfl

theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α := by
  apply ext
  intro x
  rw [trans_apply]
  rw [symm_apply_apply]
  rfl

theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β := by
  apply ext
  intro y
  rw [trans_apply]
  rw [apply_symm_apply]
  rfl

theorem trans_assoc {δ : Sort x} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
  rfl

protected theorem injective (e : α ≃ β) : Function.Injective e :=
  Function.LeftInverse.injective e.left_inv

protected theorem surjective (e : α ≃ β) : Function.Surjective e :=
  Function.RightInverse.surjective e.right_inv

protected theorem bijective (e : α ≃ β) : Function.Bijective e :=
  ⟨Equiv.injective e, Equiv.surjective e⟩

-- the converse: a bijective function gets an inverse, by choice (`Function.surjInv`)
noncomputable def ofBijective (f : α → β) (hf : Function.Bijective f) : α ≃ β where
  toFun := f
  invFun := Function.surjInv hf.surjective
  left_inv := Function.leftInverse_surjInv hf
  right_inv := Function.rightInverse_surjInv hf.surjective

theorem ofBijective_apply (f : α → β) (hf : Function.Bijective f) (x : α) :
    ofBijective f hf x = f x :=
  rfl

end Equiv

end My
