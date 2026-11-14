universe u

namespace Algebra

class Group (G : Type u) extends Mul G where
  one : G
  inv : G -> G
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, one * a = a
  inv_mul_cancel : ∀ a : G, inv a * a = one

namespace Group

postfix:max "⁻¹"=> Group.inv

variable {G : Type u} [Group G]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = one := by
  calc a * a⁻¹
     = one * (a * a⁻¹)           := by rw [one_mul]
   _ = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [← inv_mul_cancel a⁻¹]
   _ = a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)) := by rw [mul_assoc]
   _ = a⁻¹⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [mul_assoc]
   _ = a⁻¹⁻¹ * (one * a⁻¹)       := by rw [inv_mul_cancel]
   _ = a⁻¹⁻¹ * a⁻¹               := by rw [one_mul]
   _ = one                       := by rw [← inv_mul_cancel a⁻¹]

theorem mul_one (a : G) : a * one = a := by
  calc a * one
     = a * (a⁻¹ * a) := by rw [← inv_mul_cancel]
   _ = (a * a⁻¹) * a := by rw [← mul_assoc]
   _ = one * a       := by rw [← mul_inv_cancel]
   _ = a             := by rw [one_mul]

theorem left_one_unique (e : G) (h : ∀ a : G, e * a = a) : e = one := by
  calc e
     = e * one := by rw [mul_one e]
   _ = one     := by rw [h]

theorem right_one_unique (e : G) (h : ∀ a : G, a * e = a) : e = one := by
  calc e
     = one * e := by rw [one_mul e]
   _ = one     := by rw [h]

theorem one_unique (e : G) (h : ∀ a : G, a * e = a ∧ e * a = a) : e = one :=
  left_one_unique e (fun a => (h a).2)

theorem inv_inv (a : G) : a⁻¹⁻¹ = a := by
  calc a⁻¹⁻¹
     = a⁻¹⁻¹ * one       := by rw [mul_one]
   _ = a⁻¹⁻¹ * (a⁻¹ * a) := by rw [← inv_mul_cancel]
   _ = (a⁻¹⁻¹ * a⁻¹) * a := by rw [← mul_assoc]
   _ = one * a           := by rw [inv_mul_cancel a⁻¹]
   _ = a                 := by rw [one_mul]

theorem left_inv_unique (a b : G) (h : b * a = one) : b = a⁻¹ := by
  calc b
     = b * one         := by rw [mul_one]
   _ = b * (a * a⁻¹)   := by rw [mul_inv_cancel]
   _ = (b * a) * a⁻¹   := by rw [mul_assoc]
   _ = one * a⁻¹       := by rw [h]
   _ = a⁻¹             := by rw [one_mul]

theorem right_inv_unique (a b : G) (h : a * b = one) : b = a⁻¹ := by
  calc b
     = b * (a * a⁻¹) := sorry
   _ = (b * a) * a⁻¹ := sorry

theorem inv_unique (a b : G) (h : b * a = one ∧ a * b = one) : b = a⁻¹ :=
  left_inv_unique a b h.1

end Group
end Algebra
