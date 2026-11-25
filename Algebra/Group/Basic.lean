import Algebra.Group.Defs

/-! # Basic group lemmas

Mathlib: `Mathlib/Algebra/Group/Defs.lean`, `Mathlib/Algebra/Group/Basic.lean`.

Naming: the conclusion comes first, then `of`, then the hypotheses
(`eq_inv_of_mul_eq_one_left : a * b = 1 → a = b⁻¹`). -/

universe u

namespace My

variable {G : Type u} [Group G] {a b c : G}

/-! ### The right-hand axioms

Only `one_mul` and `inv_mul_cancel` are given: prove the right-hand versions from them.
`mul_inv_cancel` comes first (`mul_one` needs it). -/

/-- a special case of mul_eq_left : a * b = a ↔ b = 1
but mul_eq_left needs mul_one (not in Mathlib) --/
theorem idem_el_iff_eq_one (e : G) : e * e = e ↔ e = 1 := by
  apply Iff.intro
  · intro h
    replace h := congrArg (e⁻¹ * .) h
    rw [← mul_assoc] at h
    rw [inv_mul_cancel] at h
    rw [one_mul] at h
    exact h
  · intro h
    subst h
    rw [one_mul]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← idem_el_iff_eq_one]
  calc
    (a * a⁻¹) * (a * a⁻¹)
    _ = a * (a⁻¹ * a * a⁻¹) := by simp only [mul_assoc]
    _ = a * (1 * a⁻¹) := by rw [inv_mul_cancel]
    _ = a * a⁻¹ := by rw [one_mul]

theorem mul_one (a : G) : a * 1 = a :=
  calc
    a * 1
    _ = a * (a⁻¹ * a) := by rw [← inv_mul_cancel a]
    _ = (a * a⁻¹) * a := by rw [mul_assoc]
    _ = 1 * a := by rw [mul_inv_cancel]
    _ = a := by rw [one_mul]

/-! ### Cancelling a factor and its inverse -/

theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc]
  rw [inv_mul_cancel, one_mul]

theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]
  rw [mul_inv_cancel, one_mul]

theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc]
  rw [mul_inv_cancel, mul_one]

theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc]
  rw [inv_mul_cancel, mul_one]

/-! ### Cancellation -/

theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  replace h := congrArg (a⁻¹ * ·) h
  rw [inv_mul_cancel_left, inv_mul_cancel_left] at h
  exact h

theorem mul_right_cancel (h : a * b = c * b) : a = c := by
  replace h := congrArg (· * b⁻¹) h
  rw [mul_inv_cancel_right, mul_inv_cancel_right] at h
  exact h

theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg (a * ·)⟩

theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congrArg (· * a)⟩

-- the same statements with `a` explicit (Mathlib keeps both)
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  mul_left_cancel_iff

theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  mul_right_cancel_iff

-- `(a * ·)` is `fun x => a * x`: left multiplication by `a`
theorem mul_right_injective (a : G) : Function.Injective (a * ·) := by
  intro x y he
  rw [← mul_right_inj a]
  exact he

theorem mul_left_injective (a : G) : Function.Injective (· * a) := by
  intro x y he
  rw [← mul_left_inj a]
  exact he

theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  Function.Injective.ne_iff (mul_right_injective a)

theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  Function.Injective.ne_iff (mul_left_injective a)

/-! ### Inverses -/

-- an element with a right inverse: that inverse is the inverse
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← inv_mul_cancel b] at h
  exact mul_right_cancel h

theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ := by
  rw [← mul_inv_cancel a] at h
  exact mul_left_cancel h

theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a :=
  Eq.symm (eq_inv_of_mul_eq_one_left h)

theorem inv_eq_of_mul_eq_one_right (h : a * b = 1) : a⁻¹ = b :=
  Eq.symm (eq_inv_of_mul_eq_one_right h)

theorem inv_inv (a : G) : a⁻¹⁻¹ = a := by
  apply inv_eq_of_mul_eq_one_left
  exact mul_inv_cancel a

-- `a * b = 1` four ways: solve for `a` or for `b`, inverse on either side of the `=`
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ := by
  refine ⟨eq_inv_of_mul_eq_one_left, ?_⟩
  intro h
  rw [h]
  exact inv_mul_cancel b

theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  refine ⟨inv_eq_of_mul_eq_one_right, ?_⟩
  intro h
  rw [← h]
  exact mul_inv_cancel a

-- variants with the equality swapped
theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq]
  rw [eq_comm]

theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv]
  rw [eq_comm]

-- the same, read from the other side (handy for `rw` on a goal `a = b⁻¹`)
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  Iff.symm mul_eq_one_iff_eq_inv

theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  Iff.symm mul_eq_one_iff_inv_eq

theorem inv_one : (1 : G)⁻¹ = 1 :=
  inv_eq_of_mul_eq_one_right (one_mul 1)

theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [inv_eq_iff_mul_eq_one, mul_one]

-- the inverse of a product reverses the order
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  calc
    b⁻¹ * a⁻¹ * (a * b)
    _ = b⁻¹ * (a⁻¹ * a) * b := by simp only [mul_assoc]
    _ = b⁻¹ * b := by rw [inv_mul_cancel, mul_one]
    _ = 1 := by rw [inv_mul_cancel]

theorem inv_injective : Function.Injective (Inv.inv : G → G) := by
  intro a b he
  replace he := congrArg Inv.inv he
  rw [inv_inv, inv_inv] at he
  exact he

theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  Function.Injective.eq_iff inv_injective

theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by
  rw [mul_eq_one_iff_inv_eq]
  exact inv_inj

theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by
  rw [mul_eq_one_iff_eq_inv]
  exact inv_inj

-- a conjugate of b is trivial only if b is
theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one]
  conv =>
    rhs; rw [← mul_right_inj a]
  rw [mul_one]

/-! ### Moving a factor across an equation -/

theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b := by
  rw [← mul_left_inj c]
  rw [inv_mul_cancel_right]

theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 h

theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c := by
  rw [← mul_right_inj b]
  rw [mul_inv_cancel_left]

theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c :=
  eq_inv_mul_iff_mul_eq.2 h

theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b := by
  rw [← mul_left_inj b]
  rw [inv_mul_cancel_right]

theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c :=
  mul_inv_eq_iff_eq_mul.2 h

theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c := by
  rw [← mul_right_inj a]
  rw [mul_inv_cancel_left]

theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c :=
  inv_mul_eq_iff_eq_mul.2 h

/-! ### Commutative groups -/

section CommGroup

variable {G : Type u} [CommGroup G]

theorem inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b :=
  calc
    a⁻¹ * b * a
    _ = b * a⁻¹ * a := by rw [mul_comm a⁻¹ b]
    _ = b := by rw [inv_mul_cancel_right]

theorem mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by
  conv =>
    lhs; left; rw [← inv_inv a]
  exact inv_mul_cancel_comm a⁻¹ b

theorem inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc]
  rw [inv_mul_cancel_comm]

theorem mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc]
  rw [mul_inv_cancel_comm]

theorem mul_inv (a b : G) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev]
  exact mul_comm b⁻¹ a⁻¹

end CommGroup

end My
