import Algebra.Hom

universe u v

namespace My

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
    have h := congrArg (λ x => x⁻¹) (ha g⁻¹)
    rw [mul_inv_rev, mul_inv_rev] at h
    rw [Group.inv_inv] at h
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

theorem inv_mem_iff (S : Subgroup G) (a : G) : a⁻¹ ∈ S ↔ a ∈ S := by
  constructor
  · intro h
    have h' := S.inv_mem h
    rw [Group.inv_inv] at h'
    exact h'
  · intro h
    exact S.inv_mem h

-- multiplying by a member doesn't change membership
theorem mul_mem_cancel_left {S : Subgroup G} {a b : G} (ha : a ∈ S) : a * b ∈ S ↔ b ∈ S := by
  constructor
  · intro hab
    have ha_inv := S.inv_mem ha
    have h := S.mul_mem ha_inv hab
    rw [Group.inv_mul_cancel_left] at h
    exact h
  · intro hb
    exact S.mul_mem ha hb

theorem mul_mem_cancel_right {S : Subgroup G} {a b : G} (hb : b ∈ S) : a * b ∈ S ↔ a ∈ S := by
  constructor
  · intro hab
    have hb_inv := S.inv_mem hb
    have h := S.mul_mem hab hb_inv
    rw [Group.mul_inv_cancel_right] at h
    exact h
  · intro ha
    exact S.mul_mem ha hb

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

-- image of a subgroup: φ(S)
def map (f : G →* H) (S : Subgroup G) : Subgroup H where
  mem := λ y : H => ∃ x ∈ S, f x = y
  one_mem := by
    refine ⟨one, ?_⟩
    refine ⟨S.one_mem, ?_⟩
    exact map_one f
  mul_mem := by
    intro a b ha hb
    obtain ⟨xa, hxa⟩ := ha
    obtain ⟨xb, hxb⟩ := hb
    refine ⟨xa * xb, ?_⟩
    refine ⟨S.mul_mem hxa.1 hxb.1, ?_⟩
    rw [map_mul]
    rw [hxa.2, hxb.2]
  inv_mem := by
    intro a ha
    obtain ⟨x, hx⟩ := ha
    refine ⟨x⁻¹, ?_⟩
    refine ⟨S.inv_mem hx.1, ?_⟩
    rw [map_inv]
    exact (congrArg (λ x => x⁻¹) hx.2)

-- preimage of a subgroup: φ⁻¹(T)
def comap (f : G →* H) (T : Subgroup H) : Subgroup G where
  mem := λ x : G => (f x) ∈ T
  one_mem := by
    rw [map_one]
    exact T.one_mem
  mul_mem := by
    intro a b ha hb
    rw [map_mul]
    exact T.mul_mem ha hb
  inv_mem := by
    intro a ha
    rw [map_inv]
    exact T.inv_mem ha

theorem mem_map (f : G →* H) (S : Subgroup G) (b : H) :
    b ∈ map f S ↔ ∃ a ∈ S, f a = b := Iff.rfl

theorem mem_comap (f : G →* H) (T : Subgroup H) (a : G) :
    a ∈ comap f T ↔ f a ∈ T := Iff.rfl

theorem ker_eq_comap_bot (f : G →* H) : ker f = comap f (Subgroup.bot H) := by
  ext a
  rw [mem_ker]
  rw [mem_comap]
  rw [Subgroup.mem_bot]

theorem range_eq_map_top (f : G →* H) : range f = map f (Subgroup.top G) := by
  ext a
  rw [mem_range]
  rw [mem_map]
  simp only [Subgroup.mem_top]
  simp only [true_and]

-- injective homs have trivial kernel
theorem ker_eq_bot_of_injective (f : G →* H) (hf : Function.Injective f) :
    ker f = Subgroup.bot G := by
  ext a
  rw [Subgroup.mem_bot]
  rw [mem_ker]
  constructor
  · intro h
    rw [← map_one f] at h
    exact hf h
  · intro h
    rw [h]
    rw [map_one]

-- a trivial kernel forces injectivity
theorem injective_of_ker_eq_bot (f : G →* H) (h : ker f = Subgroup.bot G) :
    Function.Injective f := by
  intro a b hab
  have hk : (b * a⁻¹) ∈ ker f := by
    rw [mem_ker]
    rw [Hom.map_mul_inv]
    rw [hab]
    rw [mul_inv_eq_one]
  rw [h] at hk
  rw [Subgroup.mem_bot] at hk
  rw [mul_inv_eq_one] at hk
  exact hk.symm

theorem injective_iff_ker_eq_bot (f : G →* H) :
    Function.Injective f ↔ ker f = Subgroup.bot G :=
  ⟨ker_eq_bot_of_injective f, injective_of_ker_eq_bot f⟩

end Hom
end My
