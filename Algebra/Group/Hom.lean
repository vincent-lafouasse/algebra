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

infixr:25 " →* " => MonoidHom

namespace MonoidHom

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

attribute [coe] MonoidHom.toFun

instance : CoeFun (G →* H) (fun _ => G → H) :=
  ⟨MonoidHom.toFun⟩

theorem ext {f g : G →* H} (h : ∀ x, f x = g x) : f = g := by
  obtain ⟨f, hf, hfmul⟩ := f
  obtain ⟨g, hg, hgmul⟩ := g
  have hfg : f = g := funext h
  subst hfg
  rfl

protected theorem map_one (f : G →* H) : f 1 = 1 :=
  f.map_one'

protected theorem map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
  f.map_mul' a b

protected theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← MonoidHom.map_mul]
  rw [inv_mul_cancel]
  exact MonoidHom.map_one f

protected theorem map_mul_inv (f : G →* H) (a b : G) : f (a * b⁻¹) = f a * (f b)⁻¹ := by
  rw [← MonoidHom.map_inv]
  rw [MonoidHom.map_mul]

protected theorem map_pow (f : G →* H) (a : G) (n : Nat) : f (a ^ n) = f a ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]; exact MonoidHom.map_one f
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rw [MonoidHom.map_mul]
    rw [ih]

protected theorem map_zpow (f : G →* H) (a : G) (k : Int) : f (a ^ k) = f a ^ k := by
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero, zpow_zero]; exact MonoidHom.map_one f
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one]
    rw [MonoidHom.map_mul f]
    rw [ih]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one]
    rw [MonoidHom.map_mul]
    rw [MonoidHom.map_inv]
    rw [ih]

/-! ### Building homs -/

-- between groups, `map_mul` is enough: `f 1 = f 1 * f 1`, then cancel
def mk' (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) : G →* H where
  toFun := f
  map_one' := by
    rw [← idem_el_iff_eq_one]
    rw [← map_mul, mul_one]
  map_mul' := map_mul

-- an equation of functions, not of values (Mathlib's form); `congrFun` it to get `mk' f _ x = f x`
theorem mk'_apply (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) :
    (mk' f map_mul : G → H) = f :=
  rfl

protected def id (G : Type u) [Group G] : G →* G where
  toFun := id
  map_one' := rfl
  map_mul' := λ _ _ => rfl

theorem id_apply (G : Type u) [Group G] (x : G) : MonoidHom.id G x = x :=
  rfl

/-- Composition: `g ∘* f` is `g` after `f`. -/
def comp (g : H →* K) (f : G →* H) : G →* K where
  toFun := g.toFun ∘ f.toFun
  map_one' := by
    rw [Function.comp_apply]
    rw [MonoidHom.map_one f]
    rw [MonoidHom.map_one g]
  map_mul' := by
    intro x y
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply]
    rw [MonoidHom.map_mul f]
    rw [MonoidHom.map_mul g]

-- `g ∘* f` (typed `\o*`) for `g.comp f` (not in Mathlib, which writes `.comp`). Declared
-- after `def comp`, since the name on the right is resolved here.
@[inherit_doc] infixr:90 " ∘* " => MonoidHom.comp

theorem comp_apply (g : H →* K) (f : G →* H) (x : G) : (g ∘* f) x = g (f x) :=
  rfl

theorem id_comp (f : G →* H) : MonoidHom.id H ∘* f = f :=
  rfl

theorem comp_id (f : G →* H) : f ∘* MonoidHom.id G = f :=
  rfl

theorem comp_assoc {L : Type x} [Group L] (f : G →* H) (g : H →* K) (h : K →* L) :
    (h ∘* g) ∘* f = h ∘* (g ∘* f) :=
  rfl

end MonoidHom

end My
