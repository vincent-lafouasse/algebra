import Algebra.Hom

universe u v

namespace Algebra

open Group

structure Subgroup (G : Type u) [Group G] where
  mem : G → Prop
  one_mem : mem one
  mul_mem {a b : G} : mem a → mem b → mem (a * b)
  inv_mem {a : G} : mem a → mem a⁻¹

namespace Subgroup

variable {G : Type u} [Group G]

instance : Membership G (Subgroup G) where
  mem S a := S.mem a

theorem mem_iff (S : Subgroup G) (a : G) : a ∈ S ↔ S.mem a := Iff.rfl

theorem ext {S T : Subgroup G} (h : ∀ a, a ∈ S ↔ a ∈ T) : S = T :=
  sorry

def bot (G : Type u) [Group G] : Subgroup G :=   -- just `one`
  sorry

def top (G : Type u) [Group G] : Subgroup G :=   -- everything
  sorry

def inter (S T : Subgroup G) : Subgroup G :=
  sorry

end Subgroup

namespace Hom

variable {G : Type u} {H : Type v} [Group G] [Group H]

def ker (f : Hom G H) : Subgroup G :=
  sorry

def range (f : Hom G H) : Subgroup H :=
  sorry

theorem mem_ker (f : Hom G H) (a : G) : a ∈ ker f ↔ f a = one :=
  sorry

end Hom
end Algebra
