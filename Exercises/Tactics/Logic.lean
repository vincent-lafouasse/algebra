/-! # Logic: the core tactics

`intro`, `exact`, `apply`, `constructor`, `obtain` / `rcases`, `left` / `right`, `exfalso`,
`specialize`, `by_cases`, `Classical.byContradiction`.

Reminder: `¬p` is `p → False`, so you can `intro` a negation. -/

namespace Exercises.Logic

variable (p q r : Prop)

-- `intro` the hypothesis, `obtain ⟨hp, hq⟩ := h` to split an `∧`, `exact ⟨_, _⟩` to build one
theorem and_swap : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.2, h.1⟩

-- `rcases h with hp | hq` splits an `∨` into two goals; `left` / `right` pick a side
theorem or_swap : p ∨ q → q ∨ p :=
  sorry

-- `apply` works backwards: to prove `r`, it suffices to prove the premise of `q → r`
theorem imp_trans : (p → q) → (q → r) → p → r :=
  sorry

-- `¬¬p` is `(p → False) → False`: two `intro`s
theorem not_not_intro : p → ¬¬p :=
  sorry

theorem contrapositive : (p → q) → ¬q → ¬p :=
  sorry

-- `exfalso` replaces any goal by `False`; also try `absurd` and `contradiction`
theorem from_contradiction : p ∧ ¬p → q :=
  sorry

-- rcases patterns nest: `rcases h with ⟨hp, hq | hr⟩`
theorem and_or_distrib : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  sorry

-- De Morgan, the constructive half
theorem not_or_iff : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  sorry

/-! ## Classical logic -/

-- needs excluded middle: `Classical.byContradiction`
theorem not_not_elim : ¬¬p → p :=
  sorry

-- De Morgan, the classical half: `by_cases hp : p` gives one goal with `hp : p`,
-- one with `hp : ¬p`. Only one direction needs it.
theorem not_and_iff_or_not : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  sorry

/-! ## Quantifiers -/

variable {α : Type} (P Q : α → Prop)

-- `obtain ⟨x, hx⟩ := h` to use an `∃`; `exact ⟨x, _⟩` to prove one
theorem exists_and : (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) :=
  sorry

-- a `∀` is a function: apply it to a point with `h x`
theorem forall_and_iff : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
  sorry

theorem not_exists_iff : ¬(∃ x, P x) ↔ ∀ x, ¬P x :=
  sorry

-- the classical twin: `Classical.byContradiction`, then use `not_exists_iff`'s idea
theorem not_forall_iff : ¬(∀ x, P x) ↔ ∃ x, ¬P x :=
  sorry

-- Russell's barber: `specialize hb b` asks the barber about himself
theorem barber (shaves : α → α → Prop) : ¬∃ b : α, ∀ x, shaves b x ↔ ¬shaves x x :=
  sorry

-- the drinker's paradox: in a nonempty pub, someone is such that if they drink, everyone does.
-- `by_cases` on whether everyone drinks; `obtain ⟨a⟩ := ‹Nonempty α›` gets you a person,
-- and `not_forall_iff` (above) turns "not everyone drinks" into a non-drinker
theorem drinker [Nonempty α] (drinks : α → Prop) : ∃ x, drinks x → ∀ y, drinks y :=
  sorry

end Exercises.Logic
