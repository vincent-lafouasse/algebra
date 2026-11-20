universe u

namespace My

class Group (G : Type u) extends Mul G, Inv G where
  one : G
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, one * a = a
  inv_mul_cancel : ∀ a : G, inv a * a = one

namespace Group

variable {G : Type u} [Group G]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = one :=
  calc a * a⁻¹
   _ = one * (a * a⁻¹)           := by rw [one_mul]
   _ = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [← inv_mul_cancel a⁻¹]
   _ = a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)) := by rw [mul_assoc]
   _ = a⁻¹⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [mul_assoc]
   _ = a⁻¹⁻¹ * (one * a⁻¹)       := by rw [inv_mul_cancel]
   _ = a⁻¹⁻¹ * a⁻¹               := by rw [one_mul]
   _ = one                       := by rw [← inv_mul_cancel a⁻¹]

theorem mul_one (a : G) : a * one = a :=
  calc a * one
   _ = a * (a⁻¹ * a) := by rw [← inv_mul_cancel]
   _ = (a * a⁻¹) * a := by rw [← mul_assoc]
   _ = one * a       := by rw [← mul_inv_cancel]
   _ = a             := by rw [one_mul]

theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc]
  rw [inv_mul_cancel]
  rw [one_mul]

theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]

theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc]
  rw [mul_inv_cancel]
  rw [mul_one]

theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc]
  rw [inv_mul_cancel]
  rw [mul_one]

-- moving a factor across an equation

theorem eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ := by
  rw [← h, mul_inv_cancel_right]

theorem eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c := by
  rw [← h, inv_mul_cancel_left]

theorem mul_inv_eq_of_eq_mul {a b c : G} (h : a = c * b) : a * b⁻¹ = c := by
  rw [h, mul_inv_cancel_right]

theorem inv_mul_eq_of_eq_mul {a b c : G} (h : b = a * c) : a⁻¹ * b = c := by
  rw [h, inv_mul_cancel_left]

-- the same, as iffs (usable in `rw`)

theorem eq_mul_inv_iff_mul_eq (a b c : G) : a = b * c⁻¹ ↔ a * c = b := by
  constructor
  · intro h
    rw [h, inv_mul_cancel_right]
  · exact eq_mul_inv_of_mul_eq

theorem eq_inv_mul_iff_mul_eq (a b c : G) : a = b⁻¹ * c ↔ b * a = c := by
  constructor
  · intro h
    rw [h, mul_inv_cancel_left]
  · exact eq_inv_mul_of_mul_eq

theorem mul_inv_eq_iff_eq_mul (a b c : G) : a * b⁻¹ = c ↔ a = c * b := by
  constructor
  · intro h
    rw [← h, inv_mul_cancel_right]
  · exact mul_inv_eq_of_eq_mul

theorem inv_mul_eq_iff_eq_mul (a b c : G) : a⁻¹ * b = c ↔ b = a * c := by
  constructor
  · intro h
    rw [← h, mul_inv_cancel_left]
  · exact inv_mul_eq_of_eq_mul

theorem left_one_unique {e : G} (h : ∀ a : G, e * a = a) : e = one :=
  calc e
   _ = e * one := by rw [mul_one e]
   _ = one     := by rw [h]

theorem right_one_unique {e : G} (h : ∀ a : G, a * e = a) : e = one :=
  calc e
   _ = one * e := by rw [one_mul e]
   _ = one     := by rw [h]

-- redundant and trivial but satisfying to state
theorem one_unique {e : G} (h : ∀ a : G, a * e = a ∧ e * a = a) : e = one :=
  left_one_unique (fun a => (h a).2)

theorem left_inv_unique {a b : G} (h : b * a = one) : b = a⁻¹ :=
  calc b
   _ = (b * a) * a⁻¹   := by rw [mul_inv_cancel_right]
   _ = one * a⁻¹       := by rw [h]
   _ = a⁻¹             := by rw [one_mul]

protected theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  (left_inv_unique (mul_inv_cancel a)).symm

theorem right_inv_unique {a b : G} (h : a * b = one) : b = a⁻¹ :=
  have h' : a = b⁻¹ := left_inv_unique h
  calc b
   _ = b⁻¹⁻¹ := by rw [Group.inv_inv]
   _ = a⁻¹   := by rw [h']

-- redundant and trivial but satisfying to state
theorem inv_unique {a b : G} (h : b * a = one ∧ a * b = one) : b = a⁻¹ :=
  left_inv_unique h.1

theorem inv_prod (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  -- tiny lemma: (b⁻¹ * a⁻¹) is the left inverse of (a * b)
  have h : (b⁻¹ * a⁻¹) * (a * b) = one :=
    calc (b⁻¹ * a⁻¹) * (a * b)
     _ = b⁻¹ * (a⁻¹ * (a * b)) := by rw [mul_assoc]
     _ = b⁻¹ * b               := by rw [inv_mul_cancel_left]
     _ = one                   := by rw [inv_mul_cancel]
  (left_inv_unique h).symm

theorem mul_right_cancel {a b x : G} (h : a * x = b * x) : a = b :=
  calc a
   _ = (a * x) * x⁻¹ := by rw [mul_inv_cancel_right]
   _ = (b * x) * x⁻¹ := by rw [h]
   _ = b             := by rw [mul_inv_cancel_right]

theorem mul_left_cancel {a b x : G} (h : x * a = x * b) : a = b :=
  calc a
   _ = x⁻¹ * (x * a) := by rw [inv_mul_cancel_left]
   _ = x⁻¹ * (x * b) := by rw [h]
   _ = b             := by rw [inv_mul_cancel_left]

theorem inv_one : (one : G)⁻¹ = one :=
  have h := one_mul (one : G)
  (left_inv_unique h).symm

theorem inv_injective {a b : G} (h : a⁻¹ = b⁻¹) : a = b :=
  calc a
   _ = a⁻¹⁻¹ := by rw [Group.inv_inv]
   _ = b⁻¹⁻¹ := by rw [h]
   _ = b     := by rw [Group.inv_inv]

theorem inv_inj (a b : G) : a⁻¹ = b⁻¹ ↔ a = b := by
  constructor
  · intro h
    exact inv_injective h
  · intro h
    rw [h]

theorem mul_inv_eq_one (a b : G) : a * b⁻¹ = one ↔ a = b := by
  rw [← eq_mul_inv_iff_mul_eq]
  rw [Group.inv_inv]
  rw [one_mul]

theorem inv_mul_eq_one (a b : G) : a⁻¹ * b = one ↔ a = b := by
  rw [← eq_mul_inv_iff_mul_eq]
  rw [one_mul]
  rw [inv_inj]

/-! ### Cancellation as `_iff` and as injectivity -/

theorem mul_left_cancel_iff {a b c : G} : a * b = a * c ↔ b = c :=
  sorry

theorem mul_right_cancel_iff {a b c : G} : b * a = c * a ↔ b = c :=
  sorry

-- same statement as `mul_left_cancel_iff`, with `a` explicit (Mathlib keeps both)
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  sorry

theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  sorry

-- `(a * ·)` is `λ x => a * x`: left multiplication by `a`
theorem mul_right_injective (a : G) : Function.Injective (a * ·) :=
  sorry

theorem mul_left_injective (a : G) : Function.Injective (· * a) :=
  sorry

theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  sorry

theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  sorry

end Group
end My
