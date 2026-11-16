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
  sorry

theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  sorry

-- two homs are equal if they agree everywhere
theorem ext {f g : G →* H} (h : ∀ a, f a = g a) : f = g :=
  sorry

def id (G : Type u) [Group G] : G →* G :=
  sorry

def comp (g : H →* K) (f : G →* H) : G →* K :=
  sorry

theorem id_comp (f : G →* H) : comp (id H) f = f :=
  sorry

theorem comp_id (f : G →* H) : comp f (id G) = f :=
  sorry

theorem comp_assoc (h : K →* L) (g : H →* K) (f : G →* H) :
    comp (comp h g) f = comp h (comp g f) :=
  sorry

end Hom
end Algebra
