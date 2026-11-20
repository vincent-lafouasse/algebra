import Algebra.Core.Function

/-! # Bijections

`α ≃ β`: a function together with a two-sided inverse. Same shape as `Iso` (`G ≃* H`)
without `map_mul`, so the proofs should feel familiar. Core Lean has no `Equiv`.

`Perm α := α ≃ α` will be a group (in `Algebra/`, since Core doesn't know groups). -/

universe u v w x

namespace My

structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

scoped infixl:25 " ≃ " => Equiv

attribute [coe] Equiv.toFun

namespace Equiv

variable {α : Sort u} {β : Sort v} {γ : Sort w}

instance : CoeFun (α ≃ β) (fun _ => α → β) where
  coe e := e.toFun

-- like `Iso.ext`: the inverse is determined by the function, so only `toFun` matters
@[ext]
theorem ext {e e' : α ≃ β} (h : ∀ x, e x = e' x) : e = e' := by
  obtain ⟨f, g, hl, hr⟩ := e
  obtain ⟨f', g', hl', hr'⟩ := e'
  have hfe : f = f' := funext h
  subst hfe
  clear h
  have hge : g = g' := by
    funext y
    conv => lhs; rw [← hr y]
    conv => rhs; rw [← hr y]
    rw [hl, hl']
  subst hge
  rfl

/-! ### refl, symm, trans -/

protected def refl (α : Sort u) : α ≃ α where
  toFun := λ x => x
  invFun := λ x => x
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

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
    show e.invFun (e'.invFun (e'.toFun (e.toFun x))) = x
    rw [e'.left_inv]
    rw [e.left_inv]
  right_inv := by
    intro x
    show e'.toFun (e.toFun (e.invFun (e'.invFun x))) = x
    rw [e.right_inv]
    rw [e'.right_inv]

-- computation lemmas (`rfl` once the defs exist)
theorem refl_apply (x : α) : Equiv.refl α x = x :=
  rfl

theorem trans_apply (e : α ≃ β) (e' : β ≃ γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl

theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := by
  exact e.left_inv x

theorem apply_symm_apply (e : α ≃ β) (y : β) : e (e.symm y) = y := by
  exact e.right_inv y

/-! ### Algebra of equivalences (all by `ext`) -/

theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by
  ext x
  rfl

theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e :=
  rfl

theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e :=
  rfl

theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α := by
  ext x
  rw [refl_apply x]
  show e.invFun (e.toFun x) = x
  rw [e.left_inv]

theorem trans_assoc {δ : Sort x} (e₁ : α ≃ β) (e₂ : β ≃ γ) (e₃ : γ ≃ δ) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  sorry

/-! ### Equivalences are exactly the bijections -/

protected theorem injective (e : α ≃ β) : Function.Injective e :=
  sorry

protected theorem surjective (e : α ≃ β) : Function.Surjective e :=
  sorry

protected theorem bijective (e : α ≃ β) : Bijective e :=
  sorry

-- the converse needs a choice of preimages: `invFun` from Core/Function.lean
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

theorem ofBijective_apply (f : α → β) (hf : Bijective f) (x : α) : ofBijective f hf x = f x :=
  sorry

end Equiv

/-! ### Building equivalences between types (for counting) -/

namespace Equiv

variable {α α' : Type u} {β β' : Type v}

-- act on each component
def prodCongr (e : α ≃ α') (e' : β ≃ β') : α × β ≃ α' × β' :=
  sorry

def prodComm (α : Type u) (β : Type v) : α × β ≃ β × α :=
  sorry

-- act on each side of a disjoint union (`Sum.inl` / `Sum.inr`; define by `match`)
def sumCongr (e : α ≃ α') (e' : β ≃ β') : α ⊕ β ≃ α' ⊕ β' :=
  sorry

-- what they compute
theorem prodCongr_apply (e : α ≃ α') (e' : β ≃ β') (p : α × β) :
    prodCongr e e' p = (e p.1, e' p.2) :=
  sorry

theorem prodComm_apply (p : α × β) : prodComm α β p = (p.2, p.1) :=
  sorry

theorem sumCongr_inl (e : α ≃ α') (e' : β ≃ β') (x : α) :
    sumCongr e e' (Sum.inl x) = Sum.inl (e x) :=
  sorry

theorem sumCongr_inr (e : α ≃ α') (e' : β ≃ β') (y : β) :
    sumCongr e e' (Sum.inr y) = Sum.inr (e' y) :=
  sorry

end Equiv
end My
