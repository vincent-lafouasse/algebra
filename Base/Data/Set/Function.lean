import Base.Data.Set.Image
import Base.Logic.Equiv

/-! # Functions between sets

Mathlib: `Mathlib/Data/Set/Function.lean`.

`Function.Injective f` speaks about all of `α`. Often only part of it matters: `f` sends
`s` into `t`, is injective on `s`, hits all of `t`. These are the "`On`" versions:

- `MapsTo f s t`: `f` sends `s` into `t`;
- `InjOn f s`: `f` is injective on `s`;
- `SurjOn f s t`: every point of `t` is `f x` for some `x ∈ s`;
- `BijOn f s t`: all three, a bijection from `s` onto `t`;
- `EqOn f g s`: `f` and `g` agree on `s`;
- `LeftInvOn g f s`, `InvOn g f s t`: inverses on sets.

`f` stays a function on all of `α`; nothing is restricted until `MapsTo.restrict`, which
turns a `MapsTo` into a genuine function `↥s → ↥t`. With that, `BijOn f s t` gives
`↥s ≃ ↥t`: how a bijection between sets becomes a bijection between types. -/

universe u v w

namespace My

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x ∈ t

def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ s → ∀ ⦃a₂⦄, a₂ ∈ s → f a₁ = f a₂ → a₁ = a₂

def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  t ⊆ f '' s

def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

-- `f'` undoes `f` on `s`
def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f' (f x) = x

-- `f'` is undone by `f` on `t`
abbrev RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop :=
  LeftInvOn f f' t

def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t

/-! ### `MapsTo` -/

theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) :=
  sorry

theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t :=
  sorry

theorem mapsTo_iff_subset_preimage {f : α → β} {s : Set α} {t : Set β} :
    MapsTo f s t ↔ s ⊆ f ⁻¹' t :=
  sorry

theorem MapsTo.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {p : Set γ}
    (hg : MapsTo g t p) (hf : MapsTo f s t) : MapsTo (g ∘ f) s p :=
  sorry

/-- `f`, seen as a function `↥s → ↥t`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  fun x => ⟨f x.val, h x.property⟩

-- (Mathlib: `MapsTo.val_restrict_apply`)
theorem MapsTo.val_restrict_apply {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t)
    (x : s) : (MapsTo.restrict f s t h x).val = f x.val :=
  sorry

/-! ### `InjOn` -/

-- injective on a set, then on any smaller one
theorem InjOn.mono {f : α → β} {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ :=
  sorry

theorem injOn_univ {f : α → β} : InjOn f univ ↔ Function.Injective f :=
  sorry

theorem InjOn.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : InjOn g t)
    (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  sorry

-- a left inverse on `s` makes `f` injective on `s` (compare `LeftInverse.injective`)
theorem LeftInvOn.injOn {f' : β → α} {f : α → β} {s : Set α} (h : LeftInvOn f' f s) :
    InjOn f s :=
  sorry

/-! ### `SurjOn` -/

theorem surjective_iff_surjOn_univ {f : α → β} : Function.Surjective f ↔ SurjOn f univ univ :=
  sorry

theorem SurjOn.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {p : Set γ}
    (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  sorry

/-! ### `BijOn` -/

theorem BijOn.mk {f : α → β} {s : Set α} {t : Set β} (h₁ : MapsTo f s t) (h₂ : InjOn f s)
    (h₃ : SurjOn f s t) : BijOn f s t :=
  sorry

theorem BijOn.image_eq {f : α → β} {s : Set α} {t : Set β} (h : BijOn f s t) : f '' s = t :=
  sorry

theorem BijOn.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {p : Set γ}
    (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  sorry

theorem bijective_iff_bijOn_univ {f : α → β} : Function.Bijective f ↔ BijOn f univ univ :=
  sorry

-- inverses on sets give a bijection (compare `Function.bijective_iff_has_inverse`)
theorem InvOn.bijOn {f : α → β} {f' : β → α} {s : Set α} {t : Set β} (h : InvOn f' f s t)
    (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  sorry

/-- A bijection between sets is a bijection between their types. Build it from
`MapsTo.restrict` and `Equiv.ofBijective`: the work is showing the restriction is bijective. -/
noncomputable def BijOn.equiv (f : α → β) {s : Set α} {t : Set β} (h : BijOn f s t) : s ≃ t :=
  sorry

/-! ### `EqOn` -/

-- functions that agree on `s` have the same image of `s`
theorem EqOn.image_eq {f₁ f₂ : α → β} {s : Set α} (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  sorry

end Set

end My
