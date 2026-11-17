universe u

namespace Algebra

variable {α : Sort u} {r : α → α → Prop}

-- core Lean already has `Equivalence r` (refl, symm, trans) and `Setoid α`;
-- `Quotient` needs core's `Setoid`, so we only add theorems here

-- the class of `a`: everything related to `a`
def eqvClass (r : α → α → Prop) (a : α) : α → Prop := λ x => r a x

theorem mem_eqvClass_self (h : Equivalence r) (a : α) : eqvClass r a a := h.refl a

theorem eqvClass_eq_iff (h : Equivalence r) (a b : α) :
    eqvClass r a = eqvClass r b ↔ r a b :=
  sorry

-- two classes that share an element are equal → classes partition α
theorem eqvClass_eq_of_mem (h : Equivalence r) {a b x : α}
    (ha : eqvClass r a x) (hb : eqvClass r b x) : eqvClass r a = eqvClass r b :=
  sorry

end Algebra
