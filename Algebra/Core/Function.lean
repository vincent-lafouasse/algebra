universe u v

namespace My

variable {α : Sort u} {β : Sort v}

-- not in core Lean (Mathlib has it)
def Bijective (f : α → β) : Prop := Function.Injective f ∧ Function.Surjective f

-- careful with core's naming: `Function.RightInverse g f` means `∀ y, f (g y) = y`
-- i.e. g is a right inverse *of f*. `#print` them before starting.

-- a right inverse of a surjective function, picked by choice
-- (`Classical.choose` has no computational content, hence `noncomputable`)
noncomputable def invFun (f : α → β) (hs : Function.Surjective f) : β → α :=
  λ y => Classical.choose (hs y)

theorem invFun_spec (f : α → β) (hs : Function.Surjective f) (y : β) :
    f (invFun f hs y) = y :=
  Classical.choose_spec (hs y)

-- the contrapositive form: distinct inputs give distinct outputs
-- (the ← direction needs classical logic: `Classical.byContradiction`)
theorem injective_iff_ne (f : α → β) :
    Function.Injective f ↔ ∀ a b : α, a ≠ b → f a ≠ f b :=
  sorry

-- the → direction needs `Classical.choose`, like `Iso.invFun`
theorem surjective_iff_hasRightInverse (f : α → β) :
    Function.Surjective f ↔ ∃ g : β → α, Function.RightInverse g f :=
  sorry

-- `Nonempty α` is needed: if α is empty and β isn't, there is no `β → α` at all
theorem injective_iff_hasLeftInverse [Nonempty α] (f : α → β) :
    Function.Injective f ↔ ∃ g : β → α, Function.LeftInverse g f :=
  sorry

theorem bijective_iff_hasInverse (f : α → β) :
    Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  sorry

end My
