import Algebra.Group

universe u v w x

namespace Algebra

open Group

structure Hom (G : Type u) (H : Type v) [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ a b : G, toFun (a * b) = toFun a * toFun b

scoped infixr:25 " →* " => Hom

namespace Hom

variable {G : Type u} {H : Type v} {K : Type w} {L : Type x}
variable [Group G] [Group H] [Group K] [Group L]

instance : CoeFun (G →* H) (fun _ => G → H) where
  coe f := f.toFun

theorem map_one (f : G →* H) : f one = one :=
  have h : f one * f one = one * f one :=
    calc f one * f one
     _ = f (one * one) := by rw [map_mul]
     _ = f one := by rw [one_mul]
     _ = one * f one := by rw [one_mul]
  mul_right_cancel h

theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  have h : f a⁻¹ * f a = one :=
    calc f a⁻¹ * f a
     _ = f (a⁻¹ * a) := by rw [map_mul]
     _ = f one := by rw [inv_mul_cancel]
     _ = one := by rw [map_one]
  left_inv_unique h

-- two homs are equal if they agree everywhere
@[ext]
theorem ext {f g : G →* H} (h : ∀ a, f a = g a) : f = g := by
  cases f with
  | mk f' hf =>
    cases g with
    | mk g' hg =>
      have e : f' = g' := funext h
      subst e
      rfl

def id (G : Type u) [Group G] : G →* G where
  toFun := λ x => x
  map_mul := λ _a _b => rfl

theorem id_apply (x : G) : id G x = x := rfl

def comp (g : H →* K) (f : G →* H) : G →* K where
  toFun := λ x => g (f x)
  map_mul := λ a b =>
    calc g (f (a * b))
     _ = g (f a * f b) := by rw [map_mul]
     _ = g (f a) * g (f b) := by rw [map_mul]

theorem comp_apply (g : H →* K) (f : G →* H) (x : G) : comp g f x = g (f x) := rfl

theorem id_comp (f : G →* H) : comp (id H) f = f :=
  -- pedestrian but clear
  have h : ∀ x : G, comp (id H) f x = f x :=
    λ x =>
      calc comp (id H) f x
       _ = (id H) (f x) := rfl
       _ = f x := rfl
  ext h

theorem comp_id (f : G →* H) : comp f (id G) = f :=
  have h : ∀ x : G, comp f (id G) x = f x :=
    λ _ => rfl
  ext h

theorem comp_assoc (h : K →* L) (g : H →* K) (f : G →* H) :
    comp (comp h g) f = comp h (comp g f) :=
  have h' : ∀ x : G, comp (comp h g) f x = comp h (comp g f) x :=
    λ _ => rfl
  ext h'

theorem map_mul_inv (f : G →* H) (a b : G) : f (a * b⁻¹) = f a * (f b)⁻¹ := by
  rw [map_mul]
  rw [map_inv]

theorem map_conj (f : G →* H) (g n : G) : f (g * n * g⁻¹) = f g * f n * (f g)⁻¹ := by
  rw [map_mul, map_mul]
  rw [map_inv]

-- applying a hom written out as a structure literal
theorem mk_apply (g : G → H) (h : ∀ a b : G, g (a * b) = g a * g b) (x : G) :
    ({ toFun := g, map_mul := h } : G →* H) x = g x := rfl

end Hom
end Algebra
