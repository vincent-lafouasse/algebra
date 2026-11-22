/-! # Functions

Mathlib: `Mathlib/Logic/Function/Defs.lean`, `Mathlib/Logic/Function/Basic.lean`.

Core Lean already has `Function.Injective`, `Function.Surjective`, `Function.LeftInverse`,
`Function.RightInverse`, `Function.HasLeftInverse`, `Function.HasRightInverse`. Careful with
the naming: `Function.RightInverse g f` means `∀ y, f (g y) = y`, i.e. g is a right inverse
*of f*. `#print` them before starting.

Everything here lives in `My.Function`, like Mathlib's `Function` namespace. Inside
`namespace My`, `Function.Bijective` means `My.Function.Bijective`, and `Function.Injective`
still means core's (there is no `My.Function.Injective`). -/

universe u v w

namespace My
namespace Function

variable {α : Sort u} {β : Sort v} {γ : Sort w}

def Bijective (f : α → β) : Prop := Function.Injective f ∧ Function.Surjective f

-- (not in Mathlib: there, `Bijective` unfolds by `Iff.rfl`)
theorem bijective_iff (f : α → β) :
    Bijective f ↔ Function.Injective f ∧ Function.Surjective f :=
  Iff.rfl

/-! ### Composition and identity

Core already has `Function.Injective.comp` and `Function.Surjective.comp`: the ones below are
`My.Function.Injective.comp` etc., the same statements proved again. Inside `namespace My`,
`Function.Injective.comp` names yours, but dot notation `hg.comp hf` on
`hg : Function.Injective g` finds core's (the type is core's `Function.Injective`). -/

theorem Injective.comp {g : β → γ} {f : α → β}
    (hg : Function.Injective g) (hf : Function.Injective f) : Function.Injective (g ∘ f) :=
  λ _ _ hgf => hf (hg hgf)

theorem Surjective.comp {g : β → γ} {f : α → β}
    (hg : Function.Surjective g) (hf : Function.Surjective f) : Function.Surjective (g ∘ f) := by
  intro (c : γ)
  obtain ⟨b, hb⟩ := hg c
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  rw [← hb, ← ha]
  rfl

theorem Bijective.comp {g : β → γ} {f : α → β} (hg : Bijective g) (hf : Bijective f) :
    Bijective (g ∘ f) :=
  ⟨Injective.comp hg.1 hf.1, Surjective.comp hg.2 hf.2⟩

theorem bijective_id : Bijective (@id α) :=
  have is_inj : Function.Injective (@id α) :=
    λ _ _ h => h
  have is_surj : Function.Surjective (@id α) :=
    λ a => ⟨a, rfl⟩
  ⟨is_inj, is_surj⟩

-- if f ∘ g is injective, the inner g is; if f ∘ g is surjective, the outer f is
theorem Injective.of_comp {f : α → β} {g : γ → α} (I : Function.Injective (f ∘ g)) :
    Function.Injective g :=
  λ _ _ h => I (congrArg f h)

theorem Surjective.of_comp {f : α → β} {g : γ → α} (S : Function.Surjective (f ∘ g)) :
    Function.Surjective f := by
  intro b
  obtain ⟨a, ha⟩ := S b
  exact ⟨g a, ha⟩

-- a left inverse makes f injective, a right inverse makes it surjective (core has both)
theorem LeftInverse.injective {g : β → α} {f : α → β} (h : Function.LeftInverse g f) :
    Function.Injective f := by
  intro a b he
  replace he := congrArg g he
  rw [h a, h b] at he
  exact he

theorem RightInverse.surjective {f : α → β} {g : β → α} (h : Function.RightInverse g f) :
    Function.Surjective f :=
  λ b => ⟨g b, h b⟩

-- (not in Mathlib; the closest is `not_injective_iff`)
-- the ← direction needs classical logic: `Classical.byContradiction`
theorem injective_iff_ne (f : α → β) :
    Function.Injective f ↔ ∀ a b : α, a ≠ b → f a ≠ f b := by
  refine ⟨λ h_inj _ _ hne hfne => hne (h_inj hfne), ?_⟩
  intro h a b hfeq
  refine Classical.byContradiction ?_
  intro hne
  exact (h a b hne) hfeq

/-! ### Inverses by choice

`Classical.choose` has no computational content, hence `noncomputable`. -/

-- a right inverse of a surjective function, picked by choice
noncomputable def surjInv {f : α → β} (h : Function.Surjective f) (b : β) : α :=
  Classical.choose (h b)

theorem surjInv_eq {f : α → β} (h : Function.Surjective f) (b : β) : f (surjInv h b) = b :=
  Classical.choose_spec (h b)

theorem rightInverse_surjInv {f : α → β} (hf : Function.Surjective f) :
    Function.RightInverse (surjInv hf) f :=
  λ b => surjInv_eq hf b

theorem leftInverse_surjInv {f : α → β} (hf : Bijective f) :
    Function.LeftInverse (surjInv hf.2) f := by
  obtain ⟨h_inj, h_surj⟩ := hf
  intro a
  let b := surjInv h_surj (f a)
  have hfeq : f b = f a := surjInv_eq h_surj (f a)
  exact h_inj hfeq

-- an inverse of *any* f: a preimage of y if there is one, an arbitrary element if not.
-- The `if` on a Prop needs `open Classical in` in front of the `def`, and "an arbitrary
-- element" is where `[Nonempty α]` comes in.
open Classical in
noncomputable def invFun [Nonempty α] (f : α → β) : β → α :=
  λ b =>
    if has_preimage : ∃ a, f a = b
    then Classical.choose has_preimage
    else Classical.choice ‹Nonempty α›

-- the only interface lemma that looks inside `invFun`
theorem invFun_eq [Nonempty α] {f : α → β} {b : β} (h : ∃ a, f a = b) : f (invFun f b) = b := by
  unfold invFun
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem leftInverse_invFun [Nonempty α] {f : α → β} (hf : Function.Injective f) :
    Function.LeftInverse (invFun f) f := by
  intro a
  let b := invFun f (f a)
  have hfeq : f b = f a := invFun_eq ⟨a, rfl⟩
  exact hf hfeq

theorem rightInverse_invFun [Nonempty α] {f : α → β} (hf : Function.Surjective f) :
    Function.RightInverse (invFun f) f :=
  sorry

-- `Nonempty α` is needed: if α is empty and β isn't, there is no `β → α` at all
theorem injective_iff_hasLeftInverse [Nonempty α] (f : α → β) :
    Function.Injective f ↔ Function.HasLeftInverse f :=
  sorry

-- no `Nonempty α` here, so `invFun` is not available: the → witness is `surjInv`
theorem surjective_iff_hasRightInverse (f : α → β) :
    Function.Surjective f ↔ Function.HasRightInverse f :=
  sorry

theorem bijective_iff_has_inverse (f : α → β) :
    Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  sorry

end Function
end My
