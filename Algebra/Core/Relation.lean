universe u

namespace Algebra

variable {α : Sort u} {r : α → α → Prop}

-- core Lean already has `Equivalence r` (refl, symm, trans) and `Setoid α`;
-- `Quotient` needs core's `Setoid`, so we only add theorems here

-- the class of `a`: everything related to `a`
def eqvClass (r : α → α → Prop) (a : α) : α → Prop := λ x => r a x

theorem mem_eqvClass_self (h : Equivalence r) (a : α) : eqvClass r a a := h.refl a

theorem eqvClass_eq_iff (h : Equivalence r) (a b : α) :
    eqvClass r a = eqvClass r b ↔ r a b := by
  constructor
  · intro e
    have hb := congrFun e b
    show eqvClass r a b
    rw [hb]
    exact h.refl b
  · intro hab
    funext x
    apply propext
    constructor
    · intro e
      exact h.trans (h.symm hab) e
    · intro e
      exact h.trans hab e

-- two classes that share an element are equal → classes partition α
theorem eqvClass_eq_of_mem (h : Equivalence r) {a b x : α}
    (ha : eqvClass r a x) (hb : eqvClass r b x) : eqvClass r a = eqvClass r b := by
  rw [eqvClass_eq_iff h]
  exact h.trans ha (h.symm hb)

-- a partition of α: a collection of blocks (predicates on α)
structure Partition (α : Sort u) where
  block : (α → Prop) → Prop                                     -- "B is one of the blocks"
  nonempty : ∀ B, block B → ∃ x, B x                            -- no empty blocks
  cover : ∀ x, ∃ B, block B ∧ B x                               -- every element is in a block
  disjoint : ∀ B C, block B → block C → ∀ x, B x → C x → B = C  -- overlapping blocks are equal

namespace Partition

-- partitions are determined by their blocks (the other fields are proofs)
@[ext]
theorem ext {P Q : Partition α} (h : P.block = Q.block) : P = Q :=
  sorry

-- equivalence relation → partition: the blocks are the classes
def ofEquivalence {r : α → α → Prop} (h : Equivalence r) : Partition α where
  block := λ B => ∃ a, B = eqvClass r a
  nonempty := sorry
  cover := sorry
  disjoint := sorry

-- partition → relation: x ~ y iff they share a block
def rel (P : Partition α) : α → α → Prop := λ x y => ∃ B, P.block B ∧ B x ∧ B y

theorem rel_equivalence (P : Partition α) : Equivalence P.rel :=
  sorry

-- the two constructions are inverse to each other
theorem rel_ofEquivalence {r : α → α → Prop} (h : Equivalence r) :
    (ofEquivalence h).rel = r :=
  sorry

theorem ofEquivalence_rel (P : Partition α) :
    ofEquivalence (rel_equivalence P) = P :=
  sorry

end Partition

end Algebra
