import Algebra.Group.Defs
import Base.Logic.Function

/-! # Basic group lemmas

Mathlib: `Mathlib/Algebra/Group/Defs.lean`, `Mathlib/Algebra/Group/Basic.lean`.

Naming: the conclusion comes first, then `of`, then the hypotheses
(`eq_inv_of_mul_eq_one_left : a * b = 1 → a = b⁻¹`). -/

universe u

namespace My

variable {G : Type u} [Group G] {a b c : G}

/-- the special case `a = b` of `mul_eq_left : a * b = a ↔ b = 1` (Mathlib:
`IsIdempotentElem.iff_eq_one`, stated through a predicate). Proved from the left axioms only. --/
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

-- the same cancellation in the middle of a product
theorem mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻¹ * c) = a * c :=
  calc
    a * b * (b⁻¹ * c)
    _ = a * (b * (b⁻¹ * c)) := by simp only [mul_assoc]
    _ = a * c := by rw [mul_inv_cancel_left]

theorem mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (b * c) = a * c :=
  calc
    a * b⁻¹ * (b * c)
    _ = a * (b⁻¹ * (b * c)) := by simp only [mul_assoc]
    _ = a * c := by rw [inv_mul_cancel_left]

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

-- `(a * ·)` is `λ x => a * x`: left multiplication by `a`
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

-- every `x` is `a * _` and `_ * a`: name the `_`
theorem mul_left_surjective (a : G) : Function.Surjective (a * ·) := by
  intro y
  exists a⁻¹ * y
  show a * (a⁻¹ * y) = y
  exact mul_inv_cancel_left a y

theorem mul_right_surjective (a : G) : Function.Surjective (· * a) := by
  intro y
  exists y * a⁻¹
  show (y * a⁻¹) * a = y
  exact inv_mul_cancel_right y a

-- multiplying by `y`, then by `x`, is multiplying by `x * y` (on the right: by `y * x`)
theorem comp_mul_left (x y : G) : (x * ·) ∘ (y * ·) = (x * y * ·) :=
  sorry

theorem comp_mul_right (x y : G) : (· * x) ∘ (· * y) = (· * (y * x)) :=
  sorry

theorem one_mul_eq_id : ((1 : G) * ·) = id :=
  sorry

theorem mul_one_eq_id : (· * (1 : G)) = id :=
  sorry

/-! ### A product equal to one of its factors

The other factor is `1`. Mathlib also states each one flipped (`left_eq_mul`) and negated
(`mul_ne_left`): same content, but `rw` needs the goal's exact shape. -/

theorem mul_eq_left : a * b = a ↔ b = 1 :=
  sorry

theorem left_eq_mul : a = a * b ↔ b = 1 :=
  sorry

theorem mul_ne_left : a * b ≠ a ↔ b ≠ 1 :=
  sorry

theorem left_ne_mul : a ≠ a * b ↔ b ≠ 1 :=
  sorry

theorem mul_eq_right : a * b = b ↔ a = 1 :=
  sorry

theorem right_eq_mul : b = a * b ↔ a = 1 :=
  sorry

theorem mul_ne_right : a * b ≠ b ↔ a ≠ 1 :=
  sorry

theorem right_ne_mul : b ≠ a * b ↔ a ≠ 1 :=
  sorry

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

-- `inv_inv` says exactly this; Mathlib then gets `inv_injective`, `inv_surjective`, … from it
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  sorry

-- two right inverses of `x` are equal (Mathlib: for commutative monoids, where one-sided is enough)
theorem inv_unique {x y z : G} (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  sorry

-- if `a * b = 1`, one factor is trivial exactly when the other is
theorem eq_one_iff_eq_one_of_mul_eq_one (h : a * b = 1) : a = 1 ↔ b = 1 :=
  sorry

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

theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  sorry

theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  sorry

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

theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  sorry

theorem inv_bijective : Function.Bijective (Inv.inv : G → G) :=
  sorry

-- `⁻¹` moves across `=`
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  sorry

section

variable (G)

theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  sorry

theorem leftInverse_inv : Function.LeftInverse (λ a : G => a⁻¹) λ a => a⁻¹ :=
  sorry

theorem rightInverse_inv : Function.RightInverse (λ a : G => a⁻¹) λ a => a⁻¹ :=
  sorry

end

theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by
  rw [mul_eq_one_iff_inv_eq]
  exact inv_inj

theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by
  rw [mul_eq_one_iff_eq_inv]
  exact inv_inj

-- the `→` halves, for when you have the hypothesis in hand
theorem eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b :=
  sorry

theorem eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b :=
  sorry

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

-- the same four moves, the other way: an inverse in the hypothesis, none in the conclusion
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c :=
  sorry

theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c :=
  sorry

theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c :=
  sorry

theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c :=
  sorry

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

-- rearranging products (Mathlib: for any commutative semigroup)
theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) :=
  sorry

theorem mul_right_comm (a b c : G) : a * b * c = a * c * b :=
  sorry

theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) :=
  sorry

theorem mul_mul_mul_comm' (a b c d : G) : a * b * c * d = a * c * b * d :=
  sorry

theorem mul_rotate (a b c : G) : a * b * c = b * c * a :=
  sorry

theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) :=
  sorry

-- `a b⁻¹ = c d⁻¹` is "cross-multiplying" (Mathlib states it via `a / b = c / d`)
theorem mul_inv_eq_mul_inv_iff_mul_eq_mul {a b c d : G} : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  sorry

theorem inv_mul_eq_inv_mul_iff_mul_eq_mul {a b c d : G} : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b :=
  sorry

end CommGroup

end My
