import Base.Logic.Function
import Lean.Meta.CoeAttr
import Lean.Elab.Command

/-! # Quotients

Mathlib: `Mathlib/Data/Quot.lean`.

A `Setoid α` is a relation `r` on `α` with a proof `iseqv` that it is an equivalence relation.
`Quotient s` is the type of its classes: every element is `⟦a⟧` (`Quotient.mk s a`) for some
`a : α`, and `⟦a⟧ = ⟦b⟧` exactly when `a ≈ b`. Both `G ⧸ H` and `ConjClasses G` are built this
way.

Core already has the primitives; `#print` them before starting:
- `Quotient.mk s a`, the class of `a`;
- `Quotient.sound : a ≈ b → ⟦a⟧ = ⟦b⟧` and `Quotient.exact : ⟦a⟧ = ⟦b⟧ → a ≈ b`;
- `Quotient.lift f h`: a function on classes, from `f` on representatives and a proof `h`
  that `f` doesn't depend on the choice; `Quotient.lift₂` for two arguments;
- `Quotient.ind`, `Quotient.inductionOn`, `Quotient.inductionOn₂`: to prove something for every
  class, prove it for every `⟦a⟧`;
- `Quotient.exists_rep : ∃ a, ⟦a⟧ = q`.

The lemmas here are `My.Quotient.eq` etc. Inside `namespace My`, `Quotient.eq` names this one,
but dot notation on `q : Quotient s` looks in core's namespace: write `Quotient.out q`, not
`q.out`. -/

universe u v w

namespace My

variable {α : Sort u} {β : Sort v}

/-! ### Notation -/

-- `s x y` for `s.r x y`. Registered by hand, as in Mathlib: a plain `attribute [coe]` guesses
-- the wrong argument as the one being coerced (goals then print `↑x y`); here it is the
-- setoid, argument 1 of `@Setoid.r α s` (`numArgs := 2`: `α` and `s`). This is the only reason
-- the file imports Lean's metaprogramming library.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``Setoid.r
    (some { numArgs := 2, coercee := 1, type := .coeFun })

instance {α : Sort u} : CoeFun (Setoid α) (λ _ => α → α → Prop) :=
  ⟨@Setoid.r _⟩

/-- `⟦a⟧`: the class of `a`, for the setoid Lean infers from the expected type. -/
notation:arg "⟦" a "⟧" => Quotient.mk _ a

namespace Quotient

variable {sa : Setoid α} {sb : Setoid β}

/-! ### Equality and induction -/

-- the two directions `Quotient.exact` and `Quotient.sound` as one iff
theorem eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ r x y :=
  sorry

theorem «forall» {p : Quotient sa → Prop} : (∀ a, p a) ↔ ∀ a : α, p ⟦a⟧ :=
  sorry

theorem «exists» {p : Quotient sa → Prop} : (∃ a, p a) ↔ ∃ a : α, p ⟦a⟧ :=
  sorry

-- every class has a representative
theorem mk_surjective : Function.Surjective (Quotient.mk sa) :=
  sorry

/-! ### Lifting functions -/

-- `lift` computes on classes the way `f` does on representatives
theorem lift_mk (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk sa x) = f x :=
  sorry

theorem lift_comp_mk (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) :
    Quotient.lift f h ∘ Quotient.mk sa = f :=
  sorry

/-- A map between quotients, from a map `f` that sends related elements to related elements. -/
protected def map (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) : Quotient sa → Quotient sb :=
  sorry

theorem map_mk (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  sorry

/-- The same for two arguments: how a binary operation (e.g. `*` on `G ⧸ N`) is defined on
classes. -/
protected def map₂ {γ : Sort w} {sc : Setoid γ} (f : α → β → γ)
    (h : ∀ ⦃a₁ a₂⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂⦄, b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) :
    Quotient sa → Quotient sb → Quotient sc :=
  sorry

theorem map₂_mk {γ : Sort w} {sc : Setoid γ} (f : α → β → γ)
    (h : ∀ ⦃a₁ a₂⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂⦄, b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) (x : α) (y : β) :
    Quotient.map₂ f h (⟦x⟧ : Quotient sa) (⟦y⟧ : Quotient sb) = (⟦f x y⟧ : Quotient sc) :=
  sorry

/-! ### A chosen representative

`Quotient.out q` picks some `a` with `⟦a⟧ = q`, by choice: noncomputable. -/

noncomputable def out {s : Setoid α} : Quotient s → α :=
  sorry

theorem out_eq {s : Setoid α} (q : Quotient s) : ⟦Quotient.out q⟧ = q :=
  sorry

-- the chosen representative of `⟦a⟧` is related to `a`, not necessarily `a` itself
theorem mk_out {s : Setoid α} (a : α) : s (Quotient.out (⟦a⟧ : Quotient s)) a :=
  sorry

theorem mk_eq_iff_out {s : Setoid α} {x : α} {y : Quotient s} : ⟦x⟧ = y ↔ x ≈ Quotient.out y :=
  sorry

theorem eq_mk_iff_out {s : Setoid α} {x : Quotient s} {y : α} : x = ⟦y⟧ ↔ Quotient.out x ≈ y :=
  sorry

theorem out_equiv_out {s : Setoid α} {x y : Quotient s} : Quotient.out x ≈ Quotient.out y ↔ x = y :=
  sorry

theorem out_injective {s : Setoid α} : Function.Injective (@Quotient.out α s) :=
  sorry

theorem out_inj {s : Setoid α} {x y : Quotient s} : Quotient.out x = Quotient.out y ↔ x = y :=
  sorry

end Quotient

end My
