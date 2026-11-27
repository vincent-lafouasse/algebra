import Algebra.Group.End
import Algebra.Group.Subgroup.Normal

/-! # Semidirect products `N ⋊[φ] G`

Mathlib: `Mathlib/GroupTheory/SemidirectProduct.lean`.

Pairs `(n, g)` like `N × G`, but `G` acts on `N` along the way: given `φ : G →* MulAut N`,
`(n₁, g₁) * (n₂, g₂) = (n₁ * φ g₁ n₂, g₁ * g₂)`. With `φ = 1` it is the direct product.

Inside `N ⋊[φ] G`, `N` (as `inl`) is normal, `G` (as `inr`) is a complement, and conjugating
`inl n` by `inr g` gives `inl (φ g n)`: the action becomes conjugation (`inl_aut`). Conversely,
a group with a normal subgroup `N` and a complement `G` is `N ⋊[conj] G`.

Examples, once `ℤ/n` exists: the dihedral group `ℤ/n ⋊ ℤ/2` (`φ` = negation); `ℤ ⋊ ℤ/2`, the
infinite dihedral group. -/

universe u v w

namespace My

structure SemidirectProduct (N : Type u) (G : Type v) [Group N] [Group G] (φ : G →* MulAut N) where
  left : N
  right : G

notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ

namespace SemidirectProduct

variable {N : Type u} {G : Type v} {H : Type w} [Group N] [Group G] [Group H]
variable {φ : G →* MulAut N}

theorem ext {a b : N ⋊[φ] G} (h₁ : a.left = b.left) (h₂ : a.right = b.right) : a = b :=
  sorry

instance : Mul (N ⋊[φ] G) :=
  sorry

instance : One (N ⋊[φ] G) :=
  sorry

instance : Inv (N ⋊[φ] G) :=
  sorry

instance : Group (N ⋊[φ] G) :=
  sorry

theorem mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left :=
  sorry

theorem mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right :=
  sorry

theorem one_left : (1 : N ⋊[φ] G).left = 1 :=
  sorry

theorem one_right : (1 : N ⋊[φ] G).right = 1 :=
  sorry

theorem inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ a.right⁻¹ a.left⁻¹ :=
  sorry

theorem inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹ :=
  sorry

/-! ### The two inclusions and the projection -/

def inl : N →* N ⋊[φ] G :=
  sorry

def inr : G →* N ⋊[φ] G :=
  sorry

theorem left_inl (n : N) : (inl n : N ⋊[φ] G).left = n :=
  sorry

theorem right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 :=
  sorry

theorem left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 :=
  sorry

theorem right_inr (g : G) : (inr g : N ⋊[φ] G).right = g :=
  sorry

theorem inl_injective : Function.Injective (inl : N → N ⋊[φ] G) :=
  sorry

theorem inr_injective : Function.Injective (inr : G → N ⋊[φ] G) :=
  sorry

-- the action of `G` on `N` becomes conjugation inside the product
theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹ :=
  sorry

-- every element is `n * g`, uniquely
theorem inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x :=
  sorry

def rightHom : N ⋊[φ] G →* G :=
  sorry

theorem rightHom_eq_right : (rightHom : N ⋊[φ] G → G) = right :=
  sorry

theorem rightHom_surjective : Function.Surjective (rightHom : N ⋊[φ] G → G) :=
  sorry

-- `N` is the kernel of the projection, hence normal
theorem range_inl_eq_ker_rightHom : (inl : N →* N ⋊[φ] G).range = rightHom.ker :=
  sorry

/-! ### The universal property -/

-- a hom out of `N ⋊[φ] G` is a hom out of `N` and one out of `G`, compatible with `φ`
-- (explicit binders: with a `sorry` body, `variable`s would be dropped from the signature)
def lift (fn : N →* H) (fg : G →* H)
    (h : ∀ g, fn ∘* MulEquiv.toMonoidHom (φ g) = MulEquiv.toMonoidHom (MulAut.conj (fg g)) ∘* fn) :
    N ⋊[φ] G →* H :=
  sorry

variable (fn : N →* H) (fg : G →* H)
  (h : ∀ g, fn ∘* MulEquiv.toMonoidHom (φ g) = MulEquiv.toMonoidHom (MulAut.conj (fg g)) ∘* fn)

theorem lift_inl (n : N) : lift fn fg h (inl n) = fn n :=
  sorry

theorem lift_inr (g : G) : lift fn fg h (inr g) = fg g :=
  sorry

theorem hom_ext {f g : N ⋊[φ] G →* H} (hl : f ∘* inl = g ∘* inl) (hr : f ∘* inr = g ∘* inr) :
    f = g :=
  sorry

end SemidirectProduct

end My
