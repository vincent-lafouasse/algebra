universe u v w

namespace My

/-! Everything here lives in `My.Function`, as in Mathlib's `Function` namespace. Inside
`namespace My`, `Function.Bijective` means `My.Function.Bijective`, and
`Function.Injective` still means core's (there is no `My.Function.Injective`). -/

namespace Function

variable {α : Sort u} {β : Sort v}

-- not in core Lean (Mathlib has it)
def Bijective (f : α → β) : Prop := Function.Injective f ∧ Function.Surjective f

-- (not in Mathlib: there, `Bijective` unfolds by `Iff.rfl`)
theorem bijective_iff (f : α → β) : Bijective f ↔ Function.Injective f ∧ Function.Surjective f := by
  unfold Bijective
  rfl

-- careful with core's naming: `Function.RightInverse g f` means `∀ y, f (g y) = y`
-- i.e. g is a right inverse *of f*. `#print` them before starting.

-- a right inverse of a surjective function, picked by choice
-- (`Classical.choose` has no computational content, hence `noncomputable`)
noncomputable def surjInv {f : α → β} (h : Function.Surjective f) (b : β) : α :=
  Classical.choose (h b)

theorem surjInv_eq {f : α → β} (h : Function.Surjective f) (b : β) :
    f (surjInv h b) = b :=
  Classical.choose_spec (h b)

-- an inverse of *any* f: a preimage of y if there is one, an arbitrary element if not
-- (needs no surjectivity, unlike `surjInv`). The `if` on a Prop needs `open Classical in`
-- in front of the `def`, and "an arbitrary element" is where `[Nonempty α]` comes in.
noncomputable def invFun [Nonempty α] (f : α → β) : β → α :=
  sorry

-- the only interface lemma that looks inside `invFun`
theorem invFun_eq [Nonempty α] {f : α → β} {b : β} (h : ∃ a, f a = b) :
    f (invFun f b) = b :=
  sorry

/-! ### Composition and identity

Core already has `Function.Injective.comp` and `Function.Surjective.comp`: the ones below are
`My.Function.Injective.comp` etc., the same statements proved again. Inside `namespace My`,
`Function.Injective.comp` names yours, but dot notation `hg.comp hf` on `hg : Function.Injective g`
looks up core's (the type is core's `Function.Injective`). Compare with `#print`. -/

section

variable {γ : Sort w}

theorem Injective.comp {g : β → γ} {f : α → β}
    (hg : Function.Injective g) (hf : Function.Injective f) : Function.Injective (g ∘ f) := by
  intro a1 a2 h_gf_eq
  have h_f_eq := hg h_gf_eq
  exact hf h_f_eq

theorem Surjective.comp {g : β → γ} {f : α → β}
    (hg : Function.Surjective g) (hf : Function.Surjective f) : Function.Surjective (g ∘ f) := by
  intro (g : γ)
  obtain ⟨b, hb⟩ := hg g
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  rw [← ha] at hb
  exact hb

theorem Bijective.comp {g : β → γ} {f : α → β} (hg : Bijective g) (hf : Bijective f) :
    Bijective (g ∘ f) :=
  ⟨Injective.comp hg.1 hf.1, Surjective.comp hg.2 hf.2⟩

theorem bijective_id : Bijective (@id α) := by
  constructor
  · intro a b h
    exact h
  · intro y
    refine ⟨y, ?_⟩
    rfl

-- the contrapositive form: distinct inputs give distinct outputs (not in Mathlib)
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

-- no `Nonempty α` here, so `invFun` is not available: the → witness is `surjInv`
theorem surjective_iff_hasRightInverse (f : α → β) :
    Function.Surjective f ↔ Function.HasRightInverse f :=
  sorry

/-! ### `invFun` as a left / right inverse

From here on, use `invFun_eq`, never the definition of `invFun`. -/

theorem leftInverse_invFun [Nonempty α] {f : α → β} (hf : Function.Injective f) :
    Function.LeftInverse (invFun f) f :=
  sorry

theorem rightInverse_invFun [Nonempty α] {f : α → β} (hf : Function.Surjective f) :
    Function.RightInverse (invFun f) f :=
  sorry

-- f is injective iff `invFun f` undoes it (not in Mathlib, which only has the → direction)
theorem injective_iff_leftInverse_invFun [Nonempty α] (f : α → β) :
    Function.Injective f ↔ Function.LeftInverse (invFun f) f :=
  sorry

-- f is surjective iff `invFun f` is a section of it (not in Mathlib either)
theorem surjective_iff_rightInverse_invFun [Nonempty α] (f : α → β) :
    Function.Surjective f ↔ Function.RightInverse (invFun f) f :=
  sorry

-- `Nonempty α` is needed: if α is empty and β isn't, there is no `β → α` at all
-- `Function.HasLeftInverse f` is core's name for `∃ g, LeftInverse g f` (→ has a one-word witness now)
theorem injective_iff_hasLeftInverse [Nonempty α] (f : α → β) :
    Function.Injective f ↔ Function.HasLeftInverse f :=
  sorry

theorem bijective_iff_has_inverse (f : α → β) :
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
-- (not in Mathlib under this name: it's `bijective_iff_has_inverse.mpr ⟨g, hl, hr⟩`)
theorem bijective_of_inverse {f : α → β} {g : β → α}
    (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) : Bijective f :=
  sorry

-- if f ∘ g is injective, the inner g is; if f ∘ g is surjective, the outer f is
-- (Mathlib's letters: g : γ → α is applied first)
theorem Injective.of_comp {f : α → β} {g : γ → α} (I : Function.Injective (f ∘ g)) :
    Function.Injective g :=
  sorry

theorem Surjective.of_comp {f : α → β} {g : γ → α} (S : Function.Surjective (f ∘ g)) :
    Function.Surjective f :=
  sorry

end

end Function
end My
