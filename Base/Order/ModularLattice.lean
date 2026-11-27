import Base.Order.Lattice
import Base.Order.Hom.Basic

/-! # Modular lattices and the diamond isomorphism

Mathlib: `Mathlib/Order/ModularLattice.lean`.

A lattice is modular when `x ≤ z` gives `(x ⊔ y) ⊓ z = x ⊔ (y ⊓ z)`: a weakened
distributivity. Distributive lattices are modular. The normal subgroups of a group form a
modular lattice (all subgroups don't, in general).

The *diamond isomorphism* is the second isomorphism theorem with the algebra taken out: the
intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` are isomorphic as orders, by `x ↦ x ⊔ b` and
`y ↦ a ⊓ y`. For subgroups, with `N` normal: the subgroups between `H ⊓ N` and `H`
correspond to those between `N` and `H ⊔ N`, which is what `H ⧸ (H ⊓ N) ≃* (H ⊔ N) ⧸ N`
says about subgroups. -/

universe u

namespace My

class IsModularLattice (α : Type u) [Lattice α] : Prop where
  sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z

variable {α : Type u} [Lattice α] [IsModularLattice α]

theorem sup_inf_le_assoc_of_le {x z : α} (y : α) : x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z :=
  sorry

theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  sorry

-- the dual form (Mathlib has only the inequality)
theorem inf_sup_le_assoc_of_le {x z : α} (y : α) : z ≤ x → x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ z :=
  sorry

-- the diamond isomorphism
def infIccOrderIsoIccSup (a b : α) : Set.Icc (a ⊓ b) a ≃o Set.Icc b (a ⊔ b) :=
  sorry

-- (anonymous in Mathlib)
instance (priority := 100) DistribLattice.isModularLattice {β : Type u} [DistribLattice β] :
    IsModularLattice β :=
  sorry

end My
