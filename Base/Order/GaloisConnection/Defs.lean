import Base.Order.Monotone.Defs
import Base.Logic.Function

/-! # Galois connections

Mathlib: `Mathlib/Order/GaloisConnection/Defs.lean`.

`GaloisConnection l u`: `l a ≤ b ↔ a ≤ u b`. `l` is the left adjoint, `u` the right adjoint.
Examples: image and preimage of sets (`Set.image_subset_iff`), `map f` and `comap f` of
subgroups (`Subgroup.gc_map_comap`), `closure` and the carrier of a subgroup.

Everything follows from the one equivalence, at `a := u b` or `b := l a` and `le_refl`:
- `le_u_l : a ≤ u (l a)` and `l_u_le : l (u b) ≤ b`;
- `monotone_l`, `monotone_u`;
- in a partial order, `u (l (u b)) = u b` and `l (u (l a)) = l a`.

A Galois *insertion* is a connection where `l ∘ u` is the identity: `β` sits inside `α` as the
"closed" elements. `closure` and the carrier make `Subgroup G` one inside `Set G`
(`Subgroup.gi`), and that alone builds the complete lattice of subgroups in Mathlib. The
`choice` field lets `l` be computed on elements already known to be closed. -/

universe u v w

namespace My

variable {α : Type u} {β : Type v} {γ : Type w}

def GaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) : Prop :=
  ∀ a b, l a ≤ b ↔ a ≤ u b

namespace GaloisConnection

section

variable [Preorder α] [Preorder β] {l : α → β} {u : β → α}

-- a pair of monotone maps with the two inequalities is a Galois connection
theorem monotone_intro (hu : Monotone u) (hl : Monotone l) (h_u_l : ∀ a, a ≤ u (l a))
    (h_l_u : ∀ a, l (u a) ≤ a) : GaloisConnection l u :=
  sorry

variable (gc : GaloisConnection l u)

include gc

theorem le_iff_le {a : α} {b : β} : l a ≤ b ↔ a ≤ u b :=
  sorry

theorem l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
  sorry

theorem le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
  sorry

-- the unit
theorem le_u_l (a : α) : a ≤ u (l a) :=
  sorry

-- the counit
theorem l_u_le (b : β) : l (u b) ≤ b :=
  sorry

theorem monotone_u : Monotone u :=
  sorry

theorem monotone_l : Monotone l :=
  sorry

end

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

include gc

theorem u_l_u_eq_u (b : β) : u (l (u b)) = u b :=
  sorry

theorem l_u_l_eq_l (a : α) : l (u (l a)) = l a :=
  sorry

end PartialOrder

/-! ### Constructions -/

protected theorem id [Preorder α] : GaloisConnection (id : α → α) (id : α → α) :=
  sorry

-- adjoints compose (in opposite orders)
protected theorem compose [Preorder α] [Preorder β] [Preorder γ] {l1 : α → β} {u1 : β → α}
    {l2 : β → γ} {u2 : γ → β} (gc1 : GaloisConnection l1 u1) (gc2 : GaloisConnection l2 u2) :
    GaloisConnection (l2 ∘ l1) (u1 ∘ u2) :=
  sorry

end GaloisConnection

/-! ### Galois insertions -/

structure GaloisInsertion [Preorder α] [Preorder β] (l : α → β) (u : β → α) where
  choice : ∀ x : α, u (l x) ≤ x → β
  gc : GaloisConnection l u
  le_l_u : ∀ x, x ≤ l (u x)
  choice_eq : ∀ a h, choice a h = l a

-- a connection with `b ≤ l (u b)` is an insertion (`choice` is just `l`)
def GaloisConnection.toGaloisInsertion [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) (h : ∀ b, b ≤ l (u b)) : GaloisInsertion l u :=
  sorry

namespace GaloisInsertion

variable [Preorder α] [PartialOrder β] {l : α → β} {u : β → α}

theorem l_u_eq (gi : GaloisInsertion l u) (b : β) : l (u b) = b :=
  sorry

theorem leftInverse_l_u (gi : GaloisInsertion l u) : Function.LeftInverse l u :=
  sorry

theorem l_surjective (gi : GaloisInsertion l u) : Function.Surjective l :=
  sorry

theorem u_injective (gi : GaloisInsertion l u) : Function.Injective u :=
  sorry

theorem u_le_u_iff (gi : GaloisInsertion l u) {a b : β} : u a ≤ u b ↔ a ≤ b :=
  sorry

end GaloisInsertion

end My
