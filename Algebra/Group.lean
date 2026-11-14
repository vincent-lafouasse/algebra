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

end Group
end Algebra
