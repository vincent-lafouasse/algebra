import Algebra.GroupTheory.FreeGroup.Basic

/-! # Reduced words

Mathlib: `Mathlib/GroupTheory/FreeGroup/Reduce.lean`.

`reduce L` cancels adjacent pairs until none are left. Every element of the free group has
exactly one fully reduced word (`toWord`), so `FreeGroup α` could also have been defined as
"reduced words, multiplied by concatenating then reducing". That gives decidable equality, and
a second proof that `of` is injective.

`reduce` is defined by recursion on the word (Mathlib: a fold that cancels against the head of
what is already reduced). The key facts are `reduce.red` (it is a reduction) and `reduce.min`
(nothing reduces further). -/

universe u

namespace My

namespace FreeGroup

variable {α : Type u} [DecidableEq α] {L L₁ L₂ : List (α × Bool)}

-- explicit `[DecidableEq α]`: with a `sorry` body, the `variable` would be dropped
def reduce {α : Type u} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  sorry

theorem reduce.red : Red L (reduce L) :=
  sorry

-- a reduced word reduces only to itself
theorem reduce.min (H : Red (reduce L₁) L₂) : reduce L₁ = L₂ :=
  sorry

theorem reduce.Step.eq (H : Red.Step L₁ L₂) : reduce L₁ = reduce L₂ :=
  sorry

theorem reduce.eq_of_red (H : Red L₁ L₂) : reduce L₁ = reduce L₂ :=
  sorry

theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
  sorry

theorem reduce.self : mk (reduce L) = mk L :=
  sorry

-- the reduced word of an element
def toWord {α : Type u} [DecidableEq α] : FreeGroup α → List (α × Bool) :=
  sorry

theorem mk_toWord {x : FreeGroup α} : mk (toWord x) = x :=
  sorry

theorem toWord_injective : Function.Injective (toWord : FreeGroup α → List (α × Bool)) :=
  sorry

theorem toWord_mk : toWord (mk L₁) = reduce L₁ :=
  sorry

theorem reduce_toWord (x : FreeGroup α) : reduce (toWord x) = toWord x :=
  sorry

end FreeGroup

end My
