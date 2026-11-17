universe u

namespace Algebra

class Group (G : Type u) extends Mul G where
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, one * a = a
  inv_mul_cancel : ∀ a : G, inv a * a = one

namespace Group

scoped postfix:max "⁻¹" => Group.inv

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

theorem left_one_unique (e : G) (h : ∀ a : G, e * a = a) : e = one :=
  calc e
   _ = e * one := by rw [mul_one e]
   _ = one     := by rw [h]

theorem right_one_unique (e : G) (h : ∀ a : G, a * e = a) : e = one :=
  calc e
   _ = one * e := by rw [one_mul e]
   _ = one     := by rw [h]

-- redundant and trivial but satisfying to state
theorem one_unique (e : G) (h : ∀ a : G, a * e = a ∧ e * a = a) : e = one :=
  left_one_unique e (fun a => (h a).2)

theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  calc a⁻¹⁻¹
   _ = a⁻¹⁻¹ * one       := by rw [mul_one]
   _ = a⁻¹⁻¹ * (a⁻¹ * a) := by rw [← inv_mul_cancel]
   _ = (a⁻¹⁻¹ * a⁻¹) * a := by rw [← mul_assoc]
   _ = one * a           := by rw [inv_mul_cancel a⁻¹]
   _ = a                 := by rw [one_mul]

theorem left_inv_unique (a b : G) (h : b * a = one) : b = a⁻¹ :=
  calc b
   _ = b * one         := by rw [mul_one]
   _ = b * (a * a⁻¹)   := by rw [mul_inv_cancel]
   _ = (b * a) * a⁻¹   := by rw [mul_assoc]
   _ = one * a⁻¹       := by rw [h]
   _ = a⁻¹             := by rw [one_mul]

theorem right_inv_unique (a b : G) (h : a * b = one) : b = a⁻¹ :=
  have h' : a = b⁻¹ := left_inv_unique b a h
  calc b
   _ = b⁻¹⁻¹ := by rw [inv_inv]
   _ = a⁻¹   := by rw [h']

-- redundant and trivial but satisfying to state
theorem inv_unique (a b : G) (h : b * a = one ∧ a * b = one) : b = a⁻¹ :=
  left_inv_unique a b h.1

theorem inv_prod (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  -- tiny lemma: (b⁻¹ * a⁻¹) is the left inverse of (a * b)
  have h : (b⁻¹ * a⁻¹) * (a * b) = one :=
    calc (b⁻¹ * a⁻¹) * (a * b)
     _ = b⁻¹ * (a⁻¹ * (a * b)) := by rw [mul_assoc]
     _ = b⁻¹ * ((a⁻¹ * a) * b) := by rw [mul_assoc a⁻¹ a b]
     _ = b⁻¹ * (one * b)       := by rw [inv_mul_cancel]
     _ = b⁻¹ * b               := by rw [one_mul]
     _ = one                   := by rw [inv_mul_cancel]
  (left_inv_unique (a * b) (b⁻¹ * a⁻¹) h).symm

theorem mul_right_cancel (a b x : G) (h : a * x = b * x) : a = b :=
  calc a
   _ = a * one       := by rw [mul_one]
   _ = a * (x * x⁻¹) := by rw [mul_inv_cancel]
   _ = (a * x) * x⁻¹ := by rw [mul_assoc]
   _ = (b * x) * x⁻¹ := by rw [h]
   _ = b * (x * x⁻¹) := by rw [mul_assoc]
   _ = b             := by rw [mul_inv_cancel, mul_one]


theorem mul_left_cancel (a b x : G) (h : x * a = x * b) : a = b :=
  calc a
   _ = one * a       := by rw [one_mul]
   _ = (x⁻¹ * x) * a := by rw [inv_mul_cancel]
   _ = x⁻¹ * (x * a) := by rw [mul_assoc]
   _ = x⁻¹ * (x * b) := by rw [h]
   _ = (x⁻¹ * x) * b := by rw [mul_assoc]
   _ = b             := by rw [inv_mul_cancel, one_mul]

theorem inv_one : (one : G)⁻¹ = one :=
  have h := one_mul (one : G)
  (left_inv_unique one one h).symm

theorem inv_injective (a b : G) (h : a⁻¹ = b⁻¹) : a = b :=
  calc a
   _ = a⁻¹⁻¹ := by rw [inv_inv]
   _ = b⁻¹⁻¹ := by rw [h]
   _ = b     := by rw [inv_inv]

theorem mul_inv_eq_one (a b : G) : a * b⁻¹ = one ↔ a = b := by
  constructor
  · intro h
    have h' := left_inv_unique b⁻¹ a h
    rw [inv_inv] at h'
    exact h'
  · intro h
    have h' := congrArg (· * b⁻¹) h
    rw [mul_inv_cancel] at h'
    exact h'

end Group
end Algebra
