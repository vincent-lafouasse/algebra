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

def center (G : Type u) [Group G] : Subgroup G where
  mem := λ x => ∀ g : G, g * x = x * g
  one_mem := by
    intro _
    rw [mul_one, one_mul]
  mul_mem := by
    intro a b ha hb g
    calc g * (a * b)
     _ = (g * a) * b := by rw [mul_assoc]
     _ = (a * g) * b := by rw [ha]
     _ = a * (g * b) := by rw [mul_assoc]
     _ = a * (b * g) := by rw [hb]
     _ = (a * b) * g := by rw [mul_assoc]
  inv_mem := by
    intro a ha g
    have h := congrArg inv (ha g⁻¹)
    rw [inv_prod, inv_prod] at h
    rw [inv_inv] at h
    exact h.symm

def bot (G : Type u) [Group G] : Subgroup G where
  mem := λ x => x = one
  one_mem := rfl
  mul_mem := by
    intro a b ha hb
    rw [ha, hb, mul_one]
  inv_mem := by
    intro a ha
    rw [ha, inv_one]

def top (G : Type u) [Group G] : Subgroup G where
  mem := λ _ => True
  one_mem := trivial
  mul_mem := λ _ _ => trivial
  inv_mem := λ _ => trivial

def inter (S T : Subgroup G) : Subgroup G where
  mem := λ x => x ∈ S ∧ x ∈ T
  one_mem := ⟨S.one_mem, T.one_mem⟩
  mul_mem := by
    intro _a _b ha hb
    exact ⟨S.mul_mem ha.1 hb.1, T.mul_mem ha.2 hb.2⟩
  inv_mem := by
    intro _a ha
    exact ⟨S.inv_mem ha.1, T.inv_mem ha.2⟩

theorem mem_center (a : G) : a ∈ center G ↔ ∀ g : G, g * a = a * g := Iff.rfl

theorem mem_bot (a : G) : a ∈ bot G ↔ a = one := Iff.rfl

theorem mem_top (a : G) : a ∈ top G ↔ True := Iff.rfl

theorem mem_inter (S T : Subgroup G) (a : G) : a ∈ inter S T ↔ a ∈ S ∧ a ∈ T := Iff.rfl

end Subgroup

namespace Hom

variable {G : Type u} {H : Type v} [Group G] [Group H]

def ker (f : G →* H) : Subgroup G where
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
    rw [ha]
    rw [inv_one]

def range (f : G →* H) : Subgroup H where
  mem := λ y : H => ∃ x : G, f x = y
  one_mem := ⟨one, map_one f⟩
  mul_mem := by
    intro a b ha hb
    obtain ⟨xa, hxa⟩ := ha
    obtain ⟨xb, hxb⟩ := hb
    refine ⟨xa * xb, ?_⟩
    rw [map_mul, hxa, hxb]
  inv_mem := by
    intro _a ha
    obtain ⟨x, hx⟩ := ha
    refine ⟨x⁻¹, ?_⟩
    rw [map_inv, hx]

theorem mem_ker (f : G →* H) (a : G) : a ∈ ker f ↔ f a = one := Iff.rfl

theorem mem_range (f : G →* H) (b : H) : b ∈ range f ↔ ∃ a : G, f a = b := Iff.rfl

end Hom
end Algebra
