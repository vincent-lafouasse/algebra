import Algebra.Group.Pow

/-! # Homomorphisms `M →* N`

Mathlib: `Mathlib/Algebra/Group/Hom/Defs.lean`.

`M →* N` is a hom of monoids, as in Mathlib (there for any `MulOneClass`). It keeps both
`map_one'` and `map_mul'` as fields: for monoids, `map_one` doesn't follow (the constant map
to `0`, into `{0, 1}` under `*`, respects `*` but sends `1` to `0`). For groups it does:
`MonoidHom.mk'` builds a hom from `map_mul` alone. `map_inv` and `map_zpow` need groups too.

Mathlib states `map_one`, `map_mul`, `map_inv`, … once for every kind of hom (through the
class `MonoidHomClass`); here they are `MonoidHom.map_one` etc., and `MulEquiv` has its own. -/

universe u v w x

namespace My

structure MonoidHom (M : Type u) (N : Type v) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one' : toFun 1 = 1
  map_mul' : ∀ x y : M, toFun (x * y) = toFun x * toFun y

infixr:25 " →* " => MonoidHom

namespace MonoidHom

section Monoid

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

attribute [coe] MonoidHom.toFun

instance : CoeFun (M →* N) (λ _ => M → N) :=
  ⟨MonoidHom.toFun⟩

theorem ext {f g : M →* N} (h : ∀ x, f x = g x) : f = g := by
  obtain ⟨f, hf, hfmul⟩ := f
  obtain ⟨g, hg, hgmul⟩ := g
  have hfg : f = g := funext h
  subst hfg
  rfl

theorem ext_iff {f g : M →* N} : f = g ↔ ∀ x, f x = g x := by
  refine ⟨?_, ext⟩
  intro he
  intro x
  subst he
  rfl

protected theorem map_one (f : M →* N) : f 1 = 1 :=
  f.map_one'

protected theorem map_mul (f : M →* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b

protected theorem map_pow (f : M →* N) (a : M) (n : Nat) : f (a ^ n) = f a ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]; exact MonoidHom.map_one f
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rw [MonoidHom.map_mul]
    rw [ih]

/-! ### Building homs -/

protected def id (M : Type u) [Monoid M] : M →* M where
  toFun := id
  map_one' := rfl
  map_mul' := λ _ _ => rfl

theorem id_apply (M : Type u) [Monoid M] (x : M) : MonoidHom.id M x = x :=
  rfl

/-- Composition: `g ∘* f` is `g` after `f`. -/
def comp (g : N →* P) (f : M →* N) : M →* P where
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
infixr:90 " ∘* " => MonoidHom.comp

theorem comp_apply (g : N →* P) (f : M →* N) (x : M) : (g ∘* f) x = g (f x) :=
  rfl

theorem id_comp (f : M →* N) : MonoidHom.id N ∘* f = f :=
  rfl

theorem comp_id (f : M →* N) : f ∘* MonoidHom.id M = f :=
  rfl

theorem comp_assoc {L : Type x} [Monoid L] (f : M →* N) (g : N →* P) (h : P →* L) :
    (h ∘* g) ∘* f = h ∘* (g ∘* f) :=
  rfl

end Monoid

/-! ### Between groups -/

section Group

variable {G : Type u} {H : Type v} [Group G] [Group H]

protected theorem map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← MonoidHom.map_mul]
  rw [inv_mul_cancel]
  exact MonoidHom.map_one f

protected theorem map_mul_inv (f : G →* H) (a b : G) : f (a * b⁻¹) = f a * (f b)⁻¹ := by
  rw [← MonoidHom.map_inv]
  rw [MonoidHom.map_mul]

protected theorem map_zpow (f : G →* H) (a : G) (k : Int) : f (a ^ k) = f a ^ k := by
  induction k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]
    rw [zpow_natCast, zpow_natCast]
    exact MonoidHom.map_pow f a n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    rw [MonoidHom.map_inv]
    rw [MonoidHom.map_pow]

-- between groups, `map_mul` is enough: `f 1 = f 1 * f 1`, then cancel
def mk' (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) : G →* H where
  toFun := f
  map_one' := by
    rw [← @mul_eq_left H (a := f 1)]
    rw [← map_mul, mul_one]
  map_mul' := map_mul

-- an equation of functions, not of values (Mathlib's form); `congrFun` it to get `mk' f _ x = f x`
theorem mk'_apply (f : G → H) (map_mul : ∀ a b : G, f (a * b) = f a * f b) :
    (mk' f map_mul : G → H) = f :=
  rfl

end Group

end MonoidHom

end My
