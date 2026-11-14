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

theorem mul_inv_cancel (a : G) : a * a⁻¹ = Group.one := by
  calc a * a⁻¹
     = Group.one * (a * a⁻¹)     := by rw [Group.one_mul]
   _ = (a⁻¹⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [← Group.inv_mul_cancel a⁻¹]
   _ = a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)) := by rw [Group.mul_assoc]
   _ = a⁻¹⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [Group.mul_assoc]
   _ = a⁻¹⁻¹ * (Group.one * a⁻¹) := by rw [Group.inv_mul_cancel]
   _ = a⁻¹⁻¹ * a⁻¹               := by rw [Group.one_mul]
   _ = Group.one                 := by rw [← Group.inv_mul_cancel a⁻¹]

theorem mul_one (a : G) : a * Group.one = a := by
  calc a * Group.one
     = a * (a⁻¹ * a) := by rw [← Group.inv_mul_cancel]
   _ = (a * a⁻¹) * a := by rw [← Group.mul_assoc]
   _ = Group.one * a := by rw [← Group.mul_inv_cancel]
   _ = a             := by rw [Group.one_mul]

theorem left_one_unique (e : G) (h : ∀ a : G, e * a = a) : e = Group.one := by
  calc e
     = e * Group.one := by rw [Group.mul_one e]
   _ = Group.one     := by rw [h]

theorem right_one_unique (e : G) (h : ∀ a : G, a * e = a) : e = Group.one := by
  calc e
     = Group.one * e := by rw [Group.one_mul e]
   _ = Group.one     := by rw [h]

theorem one_unique (e : G) (h : ∀ a : G, a * e = a ∧ e * a = a) : e = Group.one := left_one_unique e (fun a => (h a).2)

theorem left_inv_unique (a b : G) (h : b * a = Group.one) : b = a⁻¹ := by
  calc b
     = b * Group.one   := by rw [mul_one]
   _ = b * (a * a⁻¹)   := by rw [mul_inv_cancel]
   _ = (b * a) * a⁻¹   := by rw [mul_assoc]
   _ = Group.one * a⁻¹ := by rw [h]
   _ = a⁻¹             := by rw [one_mul]

end Group
end Algebra
