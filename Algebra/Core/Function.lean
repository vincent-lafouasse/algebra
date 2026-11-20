universe u v w

namespace My

variable {α : Sort u} {β : Sort v}

-- not in core Lean (Mathlib has it)
def Bijective (f : α → β) : Prop := Function.Injective f ∧ Function.Surjective f

theorem bijective_iff (f : α → β) : Bijective f ↔ Function.Injective f ∧ Function.Surjective f := by
  unfold Bijective
  rfl

-- careful with core's naming: `Function.RightInverse g f` means `∀ y, f (g y) = y`
-- i.e. g is a right inverse *of f*. `#print` them before starting.

-- a right inverse of a surjective function, picked by choice
-- (`Classical.choose` has no computational content, hence `noncomputable`)
noncomputable def invFun (f : α → β) (hs : Function.Surjective f) : β → α :=
  λ y => Classical.choose (hs y)

theorem invFun_spec (f : α → β) (hs : Function.Surjective f) (y : β) :
    f (invFun f hs y) = y :=
  Classical.choose_spec (hs y)

/-! ### Composition and identity

Core has `Function.Injective.comp`, `Function.Surjective.comp`, `Function.injective_id`,
`Function.LeftInverse.injective`, `Function.RightInverse.surjective`, … Prove the ones
below yourself first, then compare with `#print`. -/

section

variable {γ : Sort w}

theorem injective_comp {g : β → γ} {f : α → β}
    (hg : Function.Injective g) (hf : Function.Injective f) : Function.Injective (g ∘ f) := by
  intro a1 a2 h_gf_eq
  have h_f_eq := hg h_gf_eq
  exact hf h_f_eq

theorem surjective_comp {g : β → γ} {f : α → β}
    (hg : Function.Surjective g) (hf : Function.Surjective f) : Function.Surjective (g ∘ f) := by
  intro (g : γ)
  obtain ⟨b, hb⟩ := hg g
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  rw [← ha] at hb
  exact hb

theorem bijective_comp {g : β → γ} {f : α → β} (hg : Bijective g) (hf : Bijective f) :
    Bijective (g ∘ f) := 
  ⟨injective_comp hg.1 hf.1, surjective_comp hg.2 hf.2⟩

theorem bijective_id : Bijective (λ x : α => x) := by
  constructor
  · intro a b h
    exact h
  · intro y
    refine ⟨y, ?_⟩
    rfl

-- the contrapositive form: distinct inputs give distinct outputs
-- (the ← direction needs classical logic: `Classical.byContradiction`)
theorem injective_iff_ne (f : α → β) :
    Function.Injective f ↔ ∀ a b : α, a ≠ b → f a ≠ f b := by
  constructor
  · intro h a b h_ne h_e
    have he' := h h_e
    exact h_ne he'
  · intro h a b h_e
    apply Classical.byContradiction
    intro h_ne
    have hf_ne := h a b h_ne
    exact hf_ne h_e

-- the → direction needs `Classical.choose`, like `Iso.invFun`
theorem surjective_iff_hasRightInverse (f : α → β) :
    Function.Surjective f ↔ ∃ g : β → α, Function.RightInverse g f := by
  unfold Function.RightInverse
  unfold Function.LeftInverse
  unfold Function.Surjective
  constructor
  · intro h
    let g : β → α := λ b => Classical.choose (h b)
    refine ⟨g, ?_⟩
    intro y
    show f (Classical.choose (h y)) = y
    sorry
  · intro h
    obtain ⟨g, hg⟩ := h
    intro b
    have hgb := hg b
    exact ⟨g b, hgb⟩

-- `Nonempty α` is needed: if α is empty and β isn't, there is no `β → α` at all
theorem injective_iff_hasLeftInverse [Nonempty α] (f : α → β) :
    Function.Injective f ↔ ∃ g : β → α, Function.LeftInverse g f :=
  sorry

theorem bijective_iff_hasInverse (f : α → β) :
    Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  sorry

-- a two-sided inverse makes f bijective (the converse is `Equiv.ofBijective`)
theorem bijective_of_inverse {f : α → β} {g : β → α}
    (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) : Bijective f :=
  sorry

-- if g ∘ f is injective, f is; if g ∘ f is surjective, g is
theorem injective_of_comp {g : β → γ} {f : α → β} (h : Function.Injective (g ∘ f)) :
    Function.Injective f :=
  sorry

theorem surjective_of_comp {g : β → γ} {f : α → β} (h : Function.Surjective (g ∘ f)) :
    Function.Surjective g :=
  sorry

end

end My
