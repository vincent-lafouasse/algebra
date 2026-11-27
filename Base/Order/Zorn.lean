import Base.Order.Bounds.Defs
import Base.Order.Max

/-! # Zorn's lemma

Mathlib: `Mathlib/Order/Preorder/Chain.lean` (`IsChain`), `Mathlib/Order/Zorn.lean`.

If every chain has an upper bound, there is a maximal element. It is proved from
`Classical.choice`, and it is what makes infinite objects exist: a basis of every vector space,
a maximal ideal in every nonzero ring (Krull), an algebraic closure of every field.

Mathlib proves it through `maxChain` (a maximal chain, built by transfinite iteration of
"add one more element", from `Classical.choice`), then `exists_maximal_of_chains_bounded`; the
versions below are corollaries.

`isChain_def` is not in Mathlib, where `IsChain` unfolds by `Iff.rfl`. -/

universe u

namespace My

variable {α : Type u}

/-- A chain: any two distinct elements are comparable. -/
def IsChain (r : α → α → Prop) (s : Set α) : Prop :=
  sorry

theorem isChain_def {r : α → α → Prop} {s : Set α} :
    IsChain r s ↔ s.Pairwise λ x y => r x y ∨ r y x :=
  sorry

theorem IsChain.mono {r : α → α → Prop} {s t : Set α} (h : s ⊆ t) (ht : IsChain r t) :
    IsChain r s :=
  sorry

-- the general form, for any transitive relation `≺`
theorem exists_maximal_of_chains_bounded {r : α → α → Prop}
    (h : ∀ c, IsChain r c → ∃ ub, ∀ a ∈ c, r a ub) (trans : ∀ {a b c}, r a b → r b c → r a c) :
    ∃ m, ∀ a, r m a → r a m :=
  sorry

variable [Preorder α]

theorem zorn_le (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : α, IsMax m :=
  sorry

theorem zorn_le_nonempty [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, IsMax m :=
  sorry

-- inside a subset `s`: the form used for ideals and bases
theorem zorn_le₀ (s : Set α) (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m, Maximal (· ∈ s) m :=
  sorry

-- for families of sets, ordered by inclusion
theorem zorn_subset {β : Type u} (S : Set (Set β))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) : ∃ m, Maximal (· ∈ S) m :=
  sorry

end My
