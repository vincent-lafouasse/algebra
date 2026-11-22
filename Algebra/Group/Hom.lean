import Algebra.Group.Pow

/-! # Homomorphisms `G →* H`

Mathlib: `Mathlib/Algebra/Group/Hom/Defs.lean`.

Mathlib's `MonoidHom` keeps both `map_one'` and `map_mul'` as fields (for monoids, `map_one`
doesn't follow). For groups it does: `MonoidHom.mk'` builds a hom from `map_mul` alone.

Mathlib states `map_one`, `map_mul`, `map_inv`, … once for every kind of hom (through the
class `MonoidHomClass`); here they are `MonoidHom.map_one` etc., and `MulEquiv` has its own. -/

universe u v w x

namespace My

structure MonoidHom (G : Type u) (H : Type v) [Group G] [Group H] where
  toFun : G → H
  map_one' : toFun 1 = 1
  map_mul' : ∀ x y : G, toFun (x * y) = toFun x * toFun y

@[inherit_doc] infixr:25 " →* " => MonoidHom

namespace MonoidHom

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

attribute [coe] MonoidHom.toFun

instance : CoeFun (G →* H) (fun _ => G → H) := ⟨MonoidHom.toFun⟩

theorem ext {f g : G →* H} (h : ∀ x, f x = g x) : f = g := by
  obtain ⟨f, hf, hfmul⟩ := f
  obtain ⟨g, hg, hgmul⟩ := g
  have hfg : f = g := by funext x; exact h x
  subst hfg
  rfl

protected theorem map_one (f : G →* H) : f 1 = 1 :=
  sorry

protected theorem map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
  sorry

protected theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ :=
  sorry

protected theorem map_mul_inv (f : G →* H) (a b : G) : f (a * b⁻¹) = f a * (f b)⁻¹ :=
  sorry

protected theorem map_pow (f : G →* H) (a : G) (n : Nat) : f (a ^ n) = f a ^ n :=
  sorry

protected theorem map_zpow (f : G →* H) (a : G) (k : Int) : f (a ^ k) = f a ^ k :=
  sorry

/-! ### Building homs -/

-- between groups, `map_mul` is enough: `f 1 = f 1 * f 1`, then cancel
def mk' (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) : G →* H where
  toFun := f
  map_one' := sorry
  map_mul' := map_mul

theorem mk'_apply (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) (x : G) :
    mk' f map_mul x = f x :=
  sorry

protected def id (G : Type u) [Group G] : G →* G where
  toFun := id
  map_one' := sorry
  map_mul' := sorry

theorem id_apply (G : Type u) [Group G] (x : G) : MonoidHom.id G x = x :=
  sorry

def comp (g : H →* K) (f : G →* H) : G →* K where
  toFun := g.toFun ∘ f.toFun
  map_one' := sorry
  map_mul' := sorry

theorem comp_apply (g : H →* K) (f : G →* H) (x : G) : g.comp f x = g (f x) :=
  sorry

theorem id_comp (f : G →* H) : (MonoidHom.id H).comp f = f :=
  sorry

theorem comp_id (f : G →* H) : f.comp (MonoidHom.id G) = f :=
  sorry

theorem comp_assoc {L : Type x} [Group L] (f : G →* H) (g : H →* K) (h : K →* L) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  sorry

end MonoidHom
end My
