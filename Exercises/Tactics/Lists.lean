/-! # Lists: structural induction and `simp`

`induction l with | nil => _ | cons x xs ih => _`, `simp [defs, ih]`, `simp only`, `simp?`
(prints the lemmas `simp` used, so you can turn a `simp` into a `simp only`), `exact?`. -/

namespace Exercises.Lists

variable {α β γ : Type}

def rev : List α → List α
  | [] => []
  | x :: xs => rev xs ++ [x]

-- `simp [rev, ih]` unfolds `rev` one step and uses the induction hypothesis
theorem length_rev (l : List α) : (rev l).length = l.length :=
  sorry

-- you'll need associativity of `++`: find its name with `exact?` or `simp?`
theorem rev_append (l₁ l₂ : List α) : rev (l₁ ++ l₂) = rev l₂ ++ rev l₁ :=
  sorry

-- reuse the previous theorem
theorem rev_rev (l : List α) : rev (rev l) = l :=
  sorry

-- core's `List.map`; `simp only [List.map, Function.comp]` unfolds one step
theorem map_map' (f : α → β) (g : β → γ) (l : List α) :
    (l.map f).map g = l.map (g ∘ f) :=
  sorry

theorem rev_map (f : α → β) (l : List α) : rev (l.map f) = (rev l).map f :=
  sorry

end Exercises.Lists
