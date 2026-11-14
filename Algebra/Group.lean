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
     = one * (a * a⁻¹)           := by rw [one_mul]
   _ = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [← inv_mul_cancel a⁻¹]
   _ = a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)) := by rw [mul_assoc]
   _ = a⁻¹⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [mul_assoc]
   _ = a⁻¹⁻¹ * (one * a⁻¹)       := by rw [inv_mul_cancel]
   _ = a⁻¹⁻¹ * a⁻¹               := by rw [one_mul]
   _ = one                       := by rw [← inv_mul_cancel a⁻¹]

theorem mul_one (a : G) : a * one = a :=
  calc a * one
     = a * (a⁻¹ * a) := by rw [← inv_mul_cancel]
   _ = (a * a⁻¹) * a := by rw [← mul_assoc]
   _ = one * a       := by rw [← mul_inv_cancel]
   _ = a             := by rw [one_mul]

theorem left_one_unique (e : G) (h : ∀ a : G, e * a = a) : e = one :=
  calc e
     = e * one := by rw [mul_one e]
   _ = one     := by rw [h]

theorem right_one_unique (e : G) (h : ∀ a : G, a * e = a) : e = one :=
  calc e
     = one * e := by rw [one_mul e]
   _ = one     := by rw [h]

-- redudant and trivial but satisfying to state
theorem one_unique (e : G) (h : ∀ a : G, a * e = a ∧ e * a = a) : e = one :=
  left_one_unique e (fun a => (h a).2)

theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  calc a⁻¹⁻¹
     = a⁻¹⁻¹ * one       := by rw [mul_one]
   _ = a⁻¹⁻¹ * (a⁻¹ * a) := by rw [← inv_mul_cancel]
   _ = (a⁻¹⁻¹ * a⁻¹) * a := by rw [← mul_assoc]
   _ = one * a           := by rw [inv_mul_cancel a⁻¹]
   _ = a                 := by rw [one_mul]

theorem left_inv_unique (a b : G) (h : b * a = one) : b = a⁻¹ :=
  calc b
     = b * one         := by rw [mul_one]
   _ = b * (a * a⁻¹)   := by rw [mul_inv_cancel]
   _ = (b * a) * a⁻¹   := by rw [mul_assoc]
   _ = one * a⁻¹       := by rw [h]
   _ = a⁻¹             := by rw [one_mul]

theorem right_inv_unique (a b : G) (h : a * b = one) : b = a⁻¹ :=
  have h' : a = b⁻¹ := left_inv_unique b a h
  calc b
     = b⁻¹⁻¹ := by rw [inv_inv]
   _ = a⁻¹   := by rw [h']

theorem inv_unique (a b : G) (h : b * a = one ∧ a * b = one) : b = a⁻¹ :=
  left_inv_unique a b h.1

theorem inv_prod (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  -- tiny lemma: (b⁻¹ * a⁻¹) is the left inverse of (a * b)
  have h : (b⁻¹ * a⁻¹) * (a * b) = one :=
    calc (b⁻¹ * a⁻¹) * (a * b)
       = b⁻¹ * (a⁻¹ * (a * b)) := by rw [mul_assoc]
     _ = b⁻¹ * ((a⁻¹ * a) * b) := by rw [mul_assoc a⁻¹ a b] 
     _ = b⁻¹ * (one * b)       := by rw [inv_mul_cancel]
     _ = b⁻¹ * b               := by rw [one_mul]
     _ = one                   := by rw [inv_mul_cancel]
  (left_inv_unique (a * b) (b⁻¹ * a⁻¹) h).symm

end Group
end Algebra
