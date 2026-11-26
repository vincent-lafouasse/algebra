import Base.Order.Defs.PartialOrder

/-! # Monotone functions

Mathlib: `Mathlib/Order/Monotone/Defs.lean`.

`Monotone f`: `a ≤ b → f a ≤ f b`. `Antitone f`: the order is reversed, `a ≤ b → f b ≤ f a`.
Both are stated with `⦃a b⦄`, so `hf h` works directly on `h : a ≤ b`. -/

universe u v w

namespace My

variable {α : Type u} {β : Type v} {γ : Type w} [Preorder α] [Preorder β] [Preorder γ]

def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

theorem monotone_id : Monotone (id : α → α) :=
  sorry

theorem monotone_const {c : β} : Monotone λ _ : α => c :=
  sorry

protected theorem Monotone.comp {g : β → γ} {f : α → β} (hg : Monotone g) (hf : Monotone f) :
    Monotone (g ∘ f) :=
  sorry

-- reversing the order twice preserves it
protected theorem Antitone.comp {g : β → γ} {f : α → β} (hg : Antitone g) (hf : Antitone f) :
    Monotone (g ∘ f) :=
  sorry

end My
