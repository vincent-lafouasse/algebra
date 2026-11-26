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

Naming, in this library: `a b : α` are elements (representatives), `q q₁ q₂` classes, and
`qa` the class of a given `a` (`hqa : ⟦a⟧ = qa`). Mathlib is less consistent (`x`, `y`, `a` for
classes too), so named arguments can differ from Mathlib's.

The lemmas here are `My.Quotient.eq` etc. Inside `namespace My`, `Quotient.eq` names this one,
but dot notation on `q : Quotient s` looks in core's namespace: write `Quotient.out q`, not
`q.out`. -/

universe u v w

namespace My

variable {α : Sort u} {β : Sort v}

/-! ### Notation -/

-- `s x y` for `s.r x y`; goals print it `↑s x y`, so you can see a setoid is being used as a
-- relation. Registered by hand: `Setoid` is a class, so in `@Setoid.r α s x y` the setoid `s`
-- is instance-implicit, and a plain `attribute [coe]` takes the first explicit argument (`x`)
-- as the one coerced, printing `↑x y`. Here it is argument 1 (`numArgs := 2`: `α` and `s`).
-- Mathlib registers it as `.coeFun`, which prints `s x y` with no arrow (not in Mathlib: `.coe`,
-- for the arrow). This is the only reason the file imports Lean's metaprogramming library.
run_cmd
  Lean.Elab.Command.liftTermElabM do
      Lean.Meta.registerCoercion ``Setoid.r (some { numArgs := 2, coercee := 1, type := .coe })

instance {α : Sort u} : CoeFun (Setoid α) (λ _ => α → α → Prop) :=
  ⟨@Setoid.r _⟩

/-- `⟦a⟧`: the class of `a`, for the setoid Lean infers from the expected type. -/
notation:arg "⟦" a "⟧" => Quotient.mk _ a

namespace Quotient

variable {sa : Setoid α} {sb : Setoid β}

/-! ### Equality and induction -/

theorem eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ r x y :=
  Iff.intro Quotient.exact Quotient.sound

theorem «forall» {p : Quotient sa → Prop} : (∀ q, p q) ↔ ∀ a : α, p ⟦a⟧ := by
  apply Iff.intro
  · intro h a
    let qa : Quotient sa := Quotient.mk sa a
    exact h qa
  · intro h q
    let ⟨(a : α), ha⟩ : ∃ a, ⟦a⟧ = q := Quotient.exists_rep q
    subst ha
    exact h a

theorem «exists» {p : Quotient sa → Prop} : (∃ q, p q) ↔ ∃ a : α, p ⟦a⟧ := by
  apply Iff.intro
  · intro ⟨q, hq⟩
    let ⟨a, ha⟩ := Quotient.exists_rep q
    subst ha
    exact Exists.intro a hq
  · intro ⟨a, ha⟩
    let qa : Quotient sa := Quotient.mk sa a
    exact Exists.intro qa ha

-- every class has a representative
theorem mk_surjective : Function.Surjective (Quotient.mk sa) :=
  Quotient.exists_rep

/-! ### Lifting functions -/

-- `lift` computes on classes the way `f` does on representatives
theorem lift_mk (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk sa x) = f x :=
  rfl

theorem lift_comp_mk (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) :
    Quotient.lift f h ∘ Quotient.mk sa = f :=
  funext λ _ => rfl

/-- A map between quotients, from a map `f` that sends related elements to related elements. -/
protected def map (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) : Quotient sa → Quotient sb := by
  intro (q : Quotient sa)
  let g : α → Quotient sb :=
    λ a => Quotient.mk sb (f a)
  have hg : ∀ ⦃a b : α⦄, a ≈ b → g a = g b :=
    λ _ _ hab => Quotient.sound (h hab)
  exact Quotient.lift g hg q

theorem map_mk (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  rfl

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

noncomputable def out {s : Setoid α} : Quotient s → α := λ q =>
  Classical.choose (Quotient.exists_rep q)

theorem out_eq {s : Setoid α} (q : Quotient s) : ⟦Quotient.out q⟧ = q :=
  Classical.choose_spec (Quotient.exists_rep q)

-- the chosen representative of `⟦a⟧` is related to `a`, not necessarily `a` itself
theorem mk_out {s : Setoid α} (a : α) : s (Quotient.out (⟦a⟧ : Quotient s)) a :=
  Quotient.exact (out_eq (Quotient.mk s a))

theorem mk_eq_iff_out {s : Setoid α} {a : α} {q : Quotient s} : ⟦a⟧ = q ↔ a ≈ Quotient.out q := by
  rw [← out_eq q]
  rw [eq]
  rw [out_eq q]

theorem eq_mk_iff_out {s : Setoid α} {q : Quotient s} {a : α} : q = ⟦a⟧ ↔ Quotient.out q ≈ a :=
  sorry

theorem out_equiv_out {s : Setoid α} {q₁ q₂ : Quotient s} :
    Quotient.out q₁ ≈ Quotient.out q₂ ↔ q₁ = q₂ :=
  sorry

theorem out_injective {s : Setoid α} : Function.Injective (@Quotient.out α s) :=
  sorry

theorem out_inj {s : Setoid α} {q₁ q₂ : Quotient s} : Quotient.out q₁ = Quotient.out q₂ ↔ q₁ = q₂ :=
  sorry

end Quotient

end My
