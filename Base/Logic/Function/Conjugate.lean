import Base.Logic.Function

/-! # Semiconjugate and commuting maps

Mathlib: `Mathlib/Logic/Function/Conjugate.lean`.

`Semiconj f ga gb`: `f` turns `ga` into `gb`, i.e. `f (ga x) = gb (f x)`, or `f ∘ ga = gb ∘ f`:

    α --ga--> α
    |f        |f
    β --gb--> β

`Function.Commute f g` is the case `f := f`, `ga = gb := g`: `f (g x) = g (f x)`. It is the
function version of `Commute a b` for elements (`Commute.function_commute_mul_left`: if `a`
and `b` commute, so do `(a * ·)` and `(b * ·)`).

A hom is a semiconjugacy: `MonoidHom.map_mul` says `f` semiconjugates `(a * ·)` to
`(f a * ·)`. -/

universe u v w

namespace My

namespace Function

variable {α : Sort u} {β : Sort v} {γ : Sort w}

def Semiconj (f : α → β) (ga : α → α) (gb : β → β) : Prop :=
  ∀ x, f (ga x) = gb (f x)

theorem semiconj_iff_comp_eq {f : α → β} {ga : α → α} {gb : β → β} :
    Semiconj f ga gb ↔ f ∘ ga = gb ∘ f :=
  sorry

namespace Semiconj

variable {f fab : α → β} {fbc : β → γ} {ga ga' : α → α} {gb gb' : β → β} {gc : γ → γ}

protected theorem eq (h : Semiconj f ga gb) (x : α) : f (ga x) = gb (f x) :=
  sorry

-- `f` turns `ga` into `gb` and `ga'` into `gb'`, so it turns `ga ∘ ga'` into `gb ∘ gb'`
theorem comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') :
    Semiconj f (ga ∘ ga') (gb ∘ gb') :=
  sorry

-- two squares side by side make one
protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
    Semiconj (fbc ∘ fab) ga gc :=
  sorry

theorem comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) :
    Semiconj (fbc ∘ fab) ga gc :=
  sorry

theorem id_right : Semiconj f id id :=
  sorry

theorem id_left : Semiconj id ga ga :=
  sorry

-- inverses of `ga`, `gb` are semiconjugated too
theorem inverses_right (h : Semiconj f ga gb) (ha : Function.RightInverse ga' ga)
    (hb : Function.LeftInverse gb' gb) : Semiconj f ga' gb' :=
  sorry

-- an inverse of `f` semiconjugates the other way
theorem inverse_left {f' : β → α} (h : Semiconj f ga gb) (hf₁ : Function.LeftInverse f' f)
    (hf₂ : Function.RightInverse f' f) : Semiconj f' gb ga :=
  sorry

end Semiconj

protected def Commute (f g : α → α) : Prop :=
  Semiconj f g g

theorem Semiconj.commute {f g : α → α} (h : Semiconj f g g) : Function.Commute f g :=
  sorry

namespace Commute

variable {f f' g g' : α → α}

theorem semiconj (h : Function.Commute f g) : Semiconj f g g :=
  sorry

theorem refl (f : α → α) : Function.Commute f f :=
  sorry

theorem symm (h : Function.Commute f g) : Function.Commute g f :=
  sorry

theorem comp_right (h : Function.Commute f g) (h' : Function.Commute f g') :
    Function.Commute f (g ∘ g') :=
  sorry

theorem comp_left (h : Function.Commute f g) (h' : Function.Commute f' g) :
    Function.Commute (f ∘ f') g :=
  sorry

theorem id_right : Function.Commute f id :=
  sorry

theorem id_left : Function.Commute id f :=
  sorry

end Commute

end Function

end My
