import Base.Data.Set
import Base.Order.Defs.PartialOrder

/-! # Upper and lower bounds

Mathlib: `Mathlib/Order/Bounds/Defs.lean` (the definitions), `Mathlib/Order/Bounds/Basic.lean`
(`mem_upperBounds`, `bddAbove_def`).

Mathlib writes each definition once and gets the dual from `@[to_dual]`; here both are spelled
out. Zorn's lemma asks for chains to be `BddAbove`; least upper bounds are what `sSup` is, in a
complete lattice.

The `_def` lemmas are the interface (the definitions stay opaque). Some are not in Mathlib,
where these definitions unfold by `Iff.rfl`: here, `mem_lowerBounds`, `bddBelow_def`. -/

universe u

namespace My

variable {α : Type u} [Preorder α] {s : Set α} {a : α}

def upperBounds (s : Set α) : Set α :=
  sorry

def lowerBounds (s : Set α) : Set α :=
  sorry

theorem mem_upperBounds : a ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ a :=
  sorry

theorem mem_lowerBounds : a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x :=
  sorry

def BddAbove (s : Set α) : Prop :=
  sorry

def BddBelow (s : Set α) : Prop :=
  sorry

theorem bddAbove_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  sorry

theorem bddBelow_def : BddBelow s ↔ ∃ x, ∀ y ∈ s, x ≤ y :=
  sorry

-- `a` is in `s` and below everything in `s`
def IsLeast (s : Set α) (a : α) : Prop :=
  sorry

def IsGreatest (s : Set α) (a : α) : Prop :=
  sorry

-- the least upper bound
def IsLUB (s : Set α) : α → Prop :=
  sorry

def IsGLB (s : Set α) : α → Prop :=
  sorry

end My
