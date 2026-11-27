import Algebra.Group.End
import Algebra.Group.Commute

/-! # Products of groups

Mathlib: `Mathlib/Algebra/Notation/Prod.lean` (the operations), `Mathlib/Algebra/Group/Prod.lean`
(the group, the homs).

`G × H` is a group componentwise: `(a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂)`. It comes with
four homs: the projections `fst`, `snd` and the inclusions `inl a = (a, 1)`, `inr b = (1, b)`.
Its universal property: a hom into `H × K` is the same as a pair of homs into `H` and `K`
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

variable (G : Type u) (H : Type v) [Group G] [Group H]

def fst : G × H →* G :=
  sorry

def snd : G × H →* H :=
  sorry

def inl : G →* G × H :=
  sorry

def inr : H →* G × H :=
  sorry

theorem coe_fst : (fst G H : G × H → G) = Prod.fst :=
  sorry

theorem coe_snd : (snd G H : G × H → H) = Prod.snd :=
  sorry

variable {G H}

theorem inl_apply (x : G) : inl G H x = (x, 1) :=
  sorry

theorem inr_apply (y : H) : inr G H y = (1, y) :=
  sorry

theorem fst_comp_inl : fst G H ∘* inl G H = MonoidHom.id G :=
  sorry

theorem snd_comp_inr : snd G H ∘* inr G H = MonoidHom.id H :=
  sorry

-- the two factors commute inside the product
theorem commute_inl_inr (m : G) (n : H) : Commute (inl G H m) (inr G H n) :=
  sorry

/-! ### The universal property -/

variable {K : Type w} [Group K]

/-- A pair of homs out of `G`, as one hom into the product. -/
protected def prod (f : G →* H) (g : G →* K) : G →* H × K :=
  sorry

theorem prod_apply (f : G →* H) (g : G →* K) (x : G) : f.prod g x = (f x, g x) :=
  sorry

theorem fst_comp_prod (f : G →* H) (g : G →* K) : fst H K ∘* f.prod g = f :=
  sorry

theorem snd_comp_prod (f : G →* H) (g : G →* K) : snd H K ∘* f.prod g = g :=
  sorry

-- every hom into a product is a pair
theorem prod_unique (f : G →* H × K) : (fst H K ∘* f).prod (snd H K ∘* f) = f :=
  sorry

end MonoidHom

/-- `G × H ≃* H × G`. -/
def MulEquiv.prodComm (G : Type u) (H : Type v) [Group G] [Group H] : G × H ≃* H × G :=
  sorry

end My
