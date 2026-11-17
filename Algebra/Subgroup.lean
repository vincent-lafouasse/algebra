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

@[ext]
theorem ext {S T : Subgroup G} (h : ∀ a, a ∈ S ↔ a ∈ T) : S = T := by
  cases S with
  | mk s _ _ _ =>
    cases T with
    | mk t _ _ _ =>
      have e : s = t := funext (λ a => propext (h a))
      subst e
      rfl

def bot (G : Type u) [Group G] : Subgroup G where
  mem := λ x => x = one
  one_mem := rfl
  mul_mem := by
    intro a b ha hb
    calc a * b
     _ = one * b := by rw [ha]
     _ = b := by rw [one_mul]
     _ = one := by rw [hb]
  inv_mem := by
    intro a ha
    calc a⁻¹
     _ = inv one := by rw [ha]
     _ = one := by rw [inv_one]

def top (G : Type u) [Group G] : Subgroup G where
  mem := λ _ => true
  one_mem := rfl
  mul_mem := by
    intro _ _ _ _
    rfl
  inv_mem := by
    intro _ _
    rfl

def inter (S T : Subgroup G) : Subgroup G where
  mem := λ x => x ∈ S ∧ x ∈ T
  one_mem := ⟨S.one_mem, T.one_mem⟩
  mul_mem := by
    intro _a _b ha hb
    exact ⟨S.mul_mem ha.1 hb.1, T.mul_mem ha.2 hb.2⟩
  inv_mem := by
    intro _a ha
    exact ⟨S.inv_mem ha.1, T.inv_mem ha.2⟩

end Subgroup

namespace Hom

variable {G : Type u} {H : Type v} [Group G] [Group H]

def ker (f : Hom G H) : Subgroup G where
  mem := λ x => f x = one
  one_mem := map_one f
  mul_mem := by
    intro _ _ ha hb
    rw [map_mul]
    rw [ha, hb]
    rw [mul_one]
  inv_mem := by
    intro a ha
    rw [map_inv]
    rw [← inv_one]
    rw [ha]


def range (f : Hom G H) : Subgroup H where
  mem := λ y : H => ∃ x : G, f x = y
  one_mem := ⟨one, map_one f⟩
  mul_mem := by
    intro a b ha hb
    obtain ⟨xa, hxa⟩ := ha
    obtain ⟨xb, hxb⟩ := hb
    exact ⟨xa * xb, by
      rw [map_mul]
      rw [hxa, hxb]
    ⟩
  inv_mem := by
    intro _a ha
    obtain ⟨x, hx⟩ := ha
    exact ⟨x⁻¹, by
      rw [map_inv]
      rw [hx]
    ⟩

theorem mem_ker (f : Hom G H) (a : G) : a ∈ ker f ↔ f a = one :=
  sorry

end Hom
end Algebra
