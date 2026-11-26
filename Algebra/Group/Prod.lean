import Algebra.Group.End
import Algebra.Group.Commute

/-! # Products of groups

Mathlib: `Mathlib/Algebra/Notation/Prod.lean` (the operations), `Mathlib/Algebra/Group/Prod.lean`
(the group, the homs).

`G × H` is a group componentwise: `(a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂)`. It comes with
four homs: the projections `fst`, `snd` and the inclusions `inl a = (a, 1)`, `inr b = (1, b)`.
Its universal property: a hom into `N × P` is the same as a pair of homs into `N` and `P`
(`MonoidHom.prod`, `fst_comp_prod`, `snd_comp_prod`, `prod_unique`). -/

universe u v w

namespace My

namespace Prod

variable {G : Type u} {H : Type v} [Group G] [Group H]

instance : Mul (G × H) :=
  sorry

instance : One (G × H) :=
  sorry

instance : Inv (G × H) :=
  sorry

instance instGroup : Group (G × H) :=
  sorry

theorem fst_mul (p q : G × H) : (p * q).1 = p.1 * q.1 :=
  sorry

theorem snd_mul (p q : G × H) : (p * q).2 = p.2 * q.2 :=
  sorry

theorem mk_mul_mk (a₁ a₂ : G) (b₁ b₂ : H) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) :=
  sorry

theorem fst_one : (1 : G × H).1 = 1 :=
  sorry

theorem snd_one : (1 : G × H).2 = 1 :=
  sorry

theorem one_eq_mk : (1 : G × H) = (1, 1) :=
  sorry

theorem fst_inv (p : G × H) : p⁻¹.1 = p.1⁻¹ :=
  sorry

theorem snd_inv (p : G × H) : p⁻¹.2 = p.2⁻¹ :=
  sorry

theorem inv_mk (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  sorry

theorem swap_mul (p q : G × H) : (p * q).swap = p.swap * q.swap :=
  sorry

end Prod

namespace MonoidHom

variable (M : Type u) (N : Type v) [Group M] [Group N]

def fst : M × N →* M :=
  sorry

def snd : M × N →* N :=
  sorry

def inl : M →* M × N :=
  sorry

def inr : N →* M × N :=
  sorry

theorem coe_fst : (fst M N : M × N → M) = Prod.fst :=
  sorry

theorem coe_snd : (snd M N : M × N → N) = Prod.snd :=
  sorry

variable {M N}

theorem inl_apply (x : M) : inl M N x = (x, 1) :=
  sorry

theorem inr_apply (y : N) : inr M N y = (1, y) :=
  sorry

theorem fst_comp_inl : fst M N ∘* inl M N = MonoidHom.id M :=
  sorry

theorem snd_comp_inr : snd M N ∘* inr M N = MonoidHom.id N :=
  sorry

-- the two factors commute inside the product
theorem commute_inl_inr (m : M) (n : N) : Commute (inl M N m) (inr M N n) :=
  sorry

/-! ### The universal property -/

variable {P : Type w} [Group P]

/-- A pair of homs out of `M`, as one hom into the product. -/
protected def prod (f : M →* N) (g : M →* P) : M →* N × P :=
  sorry

theorem prod_apply (f : M →* N) (g : M →* P) (x : M) : f.prod g x = (f x, g x) :=
  sorry

theorem fst_comp_prod (f : M →* N) (g : M →* P) : fst N P ∘* f.prod g = f :=
  sorry

theorem snd_comp_prod (f : M →* N) (g : M →* P) : snd N P ∘* f.prod g = g :=
  sorry

-- every hom into a product is a pair
theorem prod_unique (f : M →* N × P) : (fst N P ∘* f).prod (snd N P ∘* f) = f :=
  sorry

end MonoidHom

/-- `G × H ≃* H × G`. -/
def MulEquiv.prodComm (M : Type u) (N : Type v) [Group M] [Group N] : M × N ≃* N × M :=
  sorry

end My
