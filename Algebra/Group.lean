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

end Group
end Algebra
