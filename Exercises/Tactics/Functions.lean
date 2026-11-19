/-! # Functions: extensionality, cases, and the diagonal

`funext`, `congrFun`, `obtain ⟨x, rfl⟩` (substitute on the spot), `injection`, `nomatch`,
`cases h : e` (case on a value and remember it), `<;>` (run a tactic on every goal). -/

namespace Exercises.Functions

variable {α β γ : Type}

-- `funext n` reduces an equation between functions to one between values
theorem add_zero_fun : (λ n : Nat => n + 0) = (λ n => n) := by
  funext x
  rfl

-- injective functions cancel on the left: `funext x`, `apply hf`, then `exact congrFun h x`
theorem injective_cancel {f : β → γ} (hf : Function.Injective f) {g₁ g₂ : α → β}
    (h : f ∘ g₁ = f ∘ g₂) : g₁ = g₂ := by
  funext x
  apply hf
  exact congrFun h x

-- surjective functions cancel on the right: `obtain ⟨x, rfl⟩ := hf y`
theorem surjective_cancel {f : α → β} (hf : Function.Surjective f) {g₁ g₂ : β → γ}
    (h : g₁ ∘ f = g₂ ∘ f) : g₁ = g₂ := by
  funext y
  obtain ⟨x, hx⟩ := hf y
  rw [← hx]
  exact congrFun h x

theorem succ_injective : Function.Injective Nat.succ :=
  sorry

-- nothing maps to 0: `nomatch` on an impossible equation (or `omega`)
theorem succ_not_surjective : ¬Function.Surjective Nat.succ :=
  sorry

-- a classic: case on `b`, on `f true`, on `f false` (`cases h : f true` keeps `h : f true = _`),
-- chain them with `<;>`, finish every goal with `simp [h₁, h₂]`
theorem bool_thrice (f : Bool → Bool) (b : Bool) : f (f (f b)) = f b :=
  sorry

-- Cantor: no surjection from α onto its predicates. Choose well which predicate to ask
-- surjectivity for, then evaluate at the point you get back (`congrFun`). `Eq.mp` / `Eq.mpr`
-- move a proof across an equation between propositions.
theorem cantor (f : α → (α → Prop)) : ¬Function.Surjective f :=
  sorry

-- Lawvere's fixed-point theorem: Cantor without `¬`. Same diagonal trick, with `g` in place
-- of `¬`. (Cantor is the case `B = Prop`, `g = Not`, which has no fixed point.)
theorem lawvere {A B : Type} (e : A → (A → B)) (he : Function.Surjective e) (g : B → B) :
    ∃ b, g b = b :=
  sorry

end Exercises.Functions
