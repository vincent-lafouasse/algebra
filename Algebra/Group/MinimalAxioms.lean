import Algebra.Group.Defs

/-! # Minimal axioms for a group

Mathlib: `Mathlib/Algebra/Group/MinimalAxioms.lean`.

`Group` has five axiom fields, but three are enough: one identity law and one inverse law on
the same side, plus associativity. These two constructors build a `Group` from three
equations and prove the two missing ones.

They are `abbrev`s, not `instance`s (Mathlib: "reducible non-instances"): you use one by
writing `instance : Group G := Group.ofLeftAxioms h_assoc h_one_mul h_inv_mul`, after
`Mul G`, `One G` and `Inv G` instances for the operations.

Inside the proofs there is no `Group G` yet, so none of `Algebra/Group/Basic.lean` applies:
only the three hypotheses (and `rw`, `calc`, …). The helper theorems take them as explicit
arguments, since their conclusions don't mention them and Lean could not infer them.

Mathlib proves everything inside the two `abbrev`s with local `have`s; the helpers in the
`Group` namespace here are not in Mathlib. -/

universe u

namespace My

namespace Group

/-! ### From the left axioms -/

-- (not in Mathlib) `e * e = e ↔ e = 1`, from the left axioms only
theorem idem_el_iff_eq_one_of_left_axioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (one_mul : ∀ a : G, 1 * a = a)
    (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1) (e : G) : e * e = e ↔ e = 1 := by
  apply Iff.intro
  · intro h
    replace h := congrArg (e⁻¹ * ·) h
    rw [← assoc] at h
    rw [inv_mul_cancel] at h
    rw [one_mul] at h
    exact h
  · intro h
    subst h
    rw [one_mul]

-- (not in Mathlib) the right-hand laws from the left axioms: the inverse law first, since the
-- identity law uses it
theorem right_laws_of_left_axioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (one_mul : ∀ a : G, 1 * a = a)
    (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1) :
    (∀ (a : G), a * a⁻¹ = 1) ∧ (∀ (a : G), a * 1 = a) := by
  have mul_inv_cancel : ∀ (a : G), a * a⁻¹ = 1 := by
    intro a
    rw [← idem_el_iff_eq_one_of_left_axioms assoc one_mul inv_mul_cancel]
    calc
      (a * a⁻¹) * (a * a⁻¹)
      _ = a * (a⁻¹ * a * a⁻¹) := by simp only [assoc]
      _ = a * (1 * a⁻¹) := by rw [inv_mul_cancel]
      _ = a * a⁻¹ := by rw [one_mul]
  have mul_one : ∀ (a : G), a * 1 = a := λ a =>
    calc
      a * 1
      _ = a * (a⁻¹ * a) := by rw [← inv_mul_cancel a]
      _ = (a * a⁻¹) * a := by rw [assoc]
      _ = 1 * a := by rw [mul_inv_cancel]
      _ = a := by rw [one_mul]
  exact And.intro mul_inv_cancel mul_one

/-! ### From the right axioms: the mirror image -/

-- (not in Mathlib) `e * e = e ↔ e = 1`, from the right axioms only
theorem idem_el_iff_eq_one_of_right_axioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (mul_one : ∀ a : G, a * 1 = a)
    (mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1) (e : G) : e * e = e ↔ e = 1 := by
  apply Iff.intro
  · intro h
    replace h := congrArg (· * e⁻¹) h
    rw [assoc] at h
    rw [mul_inv_cancel] at h
    rw [mul_one] at h
    exact h
  · intro h
    subst h
    rw [mul_one]

-- (not in Mathlib) the left-hand laws from the right axioms: again the inverse law first
theorem left_laws_of_right_axioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (mul_one : ∀ a : G, a * 1 = a)
    (mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1) :
    (∀ (a : G), a⁻¹ * a = 1) ∧ (∀ (a : G), 1 * a = a) := by
  have inv_mul_cancel : ∀ (a : G), a⁻¹ * a = 1 := by
    intro a
    rw [← idem_el_iff_eq_one_of_right_axioms assoc mul_one mul_inv_cancel]
    calc
      (a⁻¹ * a) * (a⁻¹ * a)
      _ = a⁻¹ * (a * a⁻¹) * a := by simp only [assoc]
      _ = a⁻¹ * 1 * a := by rw [mul_inv_cancel]
      _ = a⁻¹ * a := by rw [mul_one]
  have one_mul : ∀ (a : G), 1 * a = a := λ a =>
    calc
      1 * a
      _ = (a * a⁻¹) * a := by rw [← mul_inv_cancel a]
      _ = a * (a⁻¹ * a) := by rw [assoc]
      _ = a * 1 := by rw [inv_mul_cancel]
      _ = a := by rw [mul_one]
  exact And.intro inv_mul_cancel one_mul

end Group

/-! ### The constructors -/

/-- A group from associativity, a left identity and a left inverse. `mul_one` and
`mul_inv_cancel` come from `Group.right_laws_of_left_axioms`. -/
abbrev Group.ofLeftAxioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (one_mul : ∀ a : G, 1 * a = a)
    (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1) : Group G
    where
  mul_assoc := assoc
  one_mul := one_mul
  mul_one := And.right (Group.right_laws_of_left_axioms assoc one_mul inv_mul_cancel)
  inv_mul_cancel := inv_mul_cancel
  mul_inv_cancel := And.left (Group.right_laws_of_left_axioms assoc one_mul inv_mul_cancel)

/-- A group from associativity, a right identity and a right inverse: the mirror image.
`one_mul` and `inv_mul_cancel` come from `Group.left_laws_of_right_axioms`. -/
abbrev Group.ofRightAxioms {G : Type u} [Mul G] [Inv G] [One G]
    (assoc : ∀ a b c : G, (a * b) * c = a * (b * c)) (mul_one : ∀ a : G, a * 1 = a)
    (mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1) : Group G
    where
  mul_assoc := assoc
  one_mul := And.right (Group.left_laws_of_right_axioms assoc mul_one mul_inv_cancel)
  mul_one := mul_one
  inv_mul_cancel := And.left (Group.left_laws_of_right_axioms assoc mul_one mul_inv_cancel)
  mul_inv_cancel := mul_inv_cancel

/- Exercise (no stub): what about a left identity `1 * a = a` with a *right* inverse
`a * a⁻¹ = 1`? Either build `Group.ofMixedAxioms`, or find a type with `*`, `1`, `⁻¹`
satisfying all three equations that is not a group. -/

end My
