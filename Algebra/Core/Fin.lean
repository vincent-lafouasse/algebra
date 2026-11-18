import Algebra.Core.Equiv

/-! # Counting with `Fin`

"`α` has `n` elements" means `α ≃ Fin n`. No cardinalities, only equivalences: to count,
build an equivalence and compose. `omega` handles most of the index arithmetic
(`Fin n` is a `Nat` `val` with a proof `isLt : val < n`; `Fin.ext` compares vals).

This is the kit for Lagrange: `G ≃ (G / H) × H`, then `Fin a × Fin b ≃ Fin (a * b)`. -/

universe u v

namespace My

/-! ### Arithmetic as equivalences -/

-- left block, then right block: inl i ↦ i, inr j ↦ a + j
def finSum (a b : Nat) : Fin a ⊕ Fin b ≃ Fin (a + b) :=
  sorry

-- row-major order: (i, j) ↦ i * b + j; back with `/ b` and `% b`
def finProd (a b : Nat) : Fin a × Fin b ≃ Fin (a * b) :=
  sorry

-- what the two equivalences compute, on `val`s (these pin down the formulas above)
theorem finSum_inl (a b : Nat) (i : Fin a) : (finSum a b (Sum.inl i)).val = i.val :=
  sorry

theorem finSum_inr (a b : Nat) (j : Fin b) : (finSum a b (Sum.inr j)).val = a + j.val :=
  sorry

theorem finProd_apply (a b : Nat) (i : Fin a) (j : Fin b) :
    (finProd a b (i, j)).val = i.val * b + j.val :=
  sorry

/-! ### Pigeonhole: the only fact about numbers we need -/

-- induction on n; the step removes one point from the target (the hard part:
-- build `Fin n → Fin m'` from `Fin (n+1) → Fin (m'+1)` by skipping the image of the last point)
theorem le_of_injective {n m : Nat} (f : Fin n → Fin m) (hf : Function.Injective f) : n ≤ m :=
  sorry

theorem eq_of_equiv {n m : Nat} (e : Fin n ≃ Fin m) : n = m :=
  sorry

/-! ### Cardinality, without a `card` function -/

-- α has exactly n elements
def HasCard (α : Type u) (n : Nat) : Prop := Nonempty (α ≃ Fin n)

theorem hasCard_iff (α : Type u) (n : Nat) : HasCard α n ↔ Nonempty (α ≃ Fin n) :=
  sorry

theorem HasCard.unique {α : Type u} {n m : Nat} (h : HasCard α n) (h' : HasCard α m) : n = m :=
  sorry

theorem HasCard.congr {α : Type u} {β : Type v} {n : Nat} (e : α ≃ β) (h : HasCard α n) :
    HasCard β n :=
  sorry

theorem HasCard.fin (n : Nat) : HasCard (Fin n) n :=
  sorry

theorem HasCard.sum {α : Type u} {β : Type v} {a b : Nat} (ha : HasCard α a) (hb : HasCard β b) :
    HasCard (α ⊕ β) (a + b) :=
  sorry

theorem HasCard.prod {α : Type u} {β : Type v} {a b : Nat} (ha : HasCard α a) (hb : HasCard β b) :
    HasCard (α × β) (a * b) :=
  sorry

end My
