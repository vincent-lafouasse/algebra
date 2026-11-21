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

-- an inverse of *any* f: a preimage of y if there is one, an arbitrary element if not
-- (Mathlib calls it `Function.invFun`). The `if` on a Prop needs `open Classical in`
-- in front of the `def`, and "an arbitrary element" is where `[Nonempty α]` comes in.
noncomputable def inverse [Nonempty α] (f : α → β) : β → α :=
  sorry

-- the only interface lemma that looks inside `inverse` (Mathlib: `Function.invFun_eq`)
theorem inverse_spec [Nonempty α] {f : α → β} (y : β) (h : ∃ x, f x = y) :
    f (inverse f y) = y :=
  sorry

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

-- no `Nonempty α` here, so `inverse` is not available: the → witness is `invFun`
theorem surjective_iff_hasRightInverse (f : α → β) :
    Function.Surjective f ↔ ∃ g : β → α, Function.RightInverse g f :=
  sorry

/-! ### `inverse` as a left / right inverse

From here on, use `inverse_spec`, never the definition of `inverse`. -/

-- (Mathlib: `Function.leftInverse_invFun`)
theorem leftInverse_inverse [Nonempty α] {f : α → β} (hf : Function.Injective f) :
    Function.LeftInverse (inverse f) f :=
  sorry

-- (Mathlib: `Function.rightInverse_invFun`)
theorem rightInverse_inverse [Nonempty α] {f : α → β} (hf : Function.Surjective f) :
    Function.RightInverse (inverse f) f :=
  sorry

-- f is injective iff `inverse f` undoes it
theorem injective_iff_leftInverse_inverse [Nonempty α] (f : α → β) :
    Function.Injective f ↔ Function.LeftInverse (inverse f) f :=
  sorry

-- f is surjective iff `inverse f` is a section of it
theorem surjective_iff_rightInverse_inverse [Nonempty α] (f : α → β) :
    Function.Surjective f ↔ Function.RightInverse (inverse f) f :=
  sorry

-- `Nonempty α` is needed: if α is empty and β isn't, there is no `β → α` at all
-- (→ has a one-word witness now)
theorem injective_iff_hasLeftInverse [Nonempty α] (f : α → β) :
    Function.Injective f ↔ ∃ g : β → α, Function.LeftInverse g f :=
  sorry

theorem bijective_iff_hasInverse (f : α → β) :
    Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  constructor
  · intro h
    obtain ⟨h_inj, h_surj⟩ := h
    rw [surjective_iff_hasRightInverse] at h_surj
    sorry
  · intro h
    obtain ⟨g, h_left, h_right⟩ := h
    apply And.intro
    intro a b h_eq
    unfold Function.LeftInverse at h_left
    have h_eq := congrArg g h_eq
    rw [← h_left a]
    rw [← h_left b]
    exact h_eq
    rw [surjective_iff_hasRightInverse]
    exact ⟨g, h_right⟩

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
