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
     = Group.one * a * a⁻¹ := by rw [Group.one_mul]

theorem mul_one (a : G) : a * Group.one = a := by
  sorry

theorem one_unique (e : G) (h : ∀ a : G, e * a = a) : e = Group.one := by
  sorry

end Group
end Algebra
