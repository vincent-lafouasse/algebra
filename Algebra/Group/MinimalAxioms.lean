import Algebra.Group.Defs

/-! # Minimal axioms for a group

Mathlib: `Mathlib/Algebra/Group/MinimalAxioms.lean`.

`Group` has four axiom fields, but three are enough: one identity law and one inverse law on
the same side, plus associativity. These two constructors build a `Group` from three
equations and prove the missing ones.

They are `abbrev`s, not `instance`s (Mathlib: "reducible non-instances"): you use one by
writing `instance : Group G := Group.ofLeftAxioms h_assoc h_one_mul h_inv_mul`.

Inside the proofs there is no `Group G` yet, so none of `Algebra/Group/Basic.lean` applies:
only the three hypotheses (and `rw`, `calc`, …). -/

universe u

namespace My

/-- A group from associativity, a left identity and a left inverse. The work is `mul_one`;
you will probably want `a * a⁻¹ = 1` on the way (a local `have`). -/
abbrev Group.ofLeftAxioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (one_mul : ∀ a : G, 1 * a = a)
    (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1) : Group G
    where
  mul_assoc := assoc
  one_mul := one_mul
  mul_one := sorry
  inv_mul_cancel := inv_mul_cancel
  mul_inv_cancel := sorry

/-- A group from associativity, a right identity and a right inverse: the mirror image.
The work is `one_mul` and `inv_mul_cancel`; which one comes first? -/
abbrev Group.ofRightAxioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (mul_one : ∀ a : G, a * 1 = a)
    (mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1) : Group G
    where
  mul_assoc := assoc
  one_mul := sorry
  mul_one := mul_one
  inv_mul_cancel := sorry
  mul_inv_cancel := sorry

/- Exercise (no stub): what about a left identity `1 * a = a` with a *right* inverse
`a * a⁻¹ = 1`? Either build `Group.ofMixedAxioms`, or find a type with `*`, `1`, `⁻¹`
satisfying all three equations that is not a group. -/

end My
