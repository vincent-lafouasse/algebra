import Algebra.Hom
import Algebra.Core.Function

universe u v w

namespace My

open Group

structure Iso (G : Type u) (H : Type v) [Group G] [Group H] where
  toHom : G →* H
  invHom : H →* G
  left_inv : Hom.comp invHom toHom = Hom.id G
  right_inv : Hom.comp toHom invHom = Hom.id H

scoped infixr:25 " ≃* " => Iso

namespace Iso

variable {G : Type u} {H : Type v} {K : Type w}
variable [Group G] [Group H] [Group K]

/-! ### An isomorphism is a function

`e x` means `e.toHom x`. `@[coe]` makes goals display it as `e x` (or `⇑e`), not as
`Iso.toFun e x`; `coe_toHom` / `toHom_apply` are the interface between the two spellings. -/

@[coe] def toFun (e : G ≃* H) : G → H := e.toHom

instance : CoeFun (G ≃* H) (fun _ => G → H) where
  coe := Iso.toFun

theorem coe_toHom (e : G ≃* H) : (e.toHom : G → H) = e := rfl

theorem toHom_apply (e : G ≃* H) (x : G) : e.toHom x = e x := rfl

-- so that `rw` works on `e (x * y)` without first going back to `e.toHom`
theorem map_mul (e : G ≃* H) (x y : G) : e (x * y) = e x * e y := by
  rw [← toHom_apply]
  rw [Hom.map_mul]
  rfl

-- pointwise versions of left_inv / right_inv
theorem invHom_toHom (e : G ≃* H) (x : G) : e.invHom (e.toHom x) = x := by
  rw (config := { occs := .pos [2] }) [← Hom.id_apply x]
  rw [← e.left_inv]
  rfl

theorem toHom_invHom (e : G ≃* H) (y : H) : e.toHom (e.invHom y) = y := by
  rw (config := { occs := .pos [2] }) [← Hom.id_apply y]
  rw [← e.right_inv]
  rfl

-- G ≅ G
protected def refl (G : Type u) [Group G] : G ≃* G where
  toHom := Hom.id G
  invHom := Hom.id G
  left_inv := by
    rw [Hom.comp_id]
  right_inv := by
    rw [Hom.comp_id]

theorem refl_toHom (G : Type u) [Group G] : (Iso.refl G).toHom = Hom.id G := rfl

-- G ≅ H → H ≅ G
protected def symm (e : G ≃* H) : H ≃* G where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

theorem symm_toHom (e : G ≃* H) : e.symm.toHom = e.invHom := rfl

-- G ≅ H → H ≅ K → G ≅ K
protected def trans (e : G ≃* H) (e' : H ≃* K) : G ≃* K where
  toHom := e'.toHom.comp e.toHom
  invHom := e.invHom.comp e'.invHom
  left_inv := by
    rw [Hom.comp_assoc]
    rw [← Hom.comp_assoc e'.invHom e'.toHom e.toHom]
    rw [e'.left_inv]
    rw [Hom.id_comp]
    rw [e.left_inv]
  right_inv := by
    rw [Hom.comp_assoc]
    rw [← Hom.comp_assoc e.toHom e.invHom e'.invHom]
    rw [e.right_inv]
    rw [Hom.id_comp]
    rw [e'.right_inv]

theorem trans_toHom (e : G ≃* H) (e' : H ≃* K) :
    (e.trans e').toHom = e'.toHom.comp e.toHom := rfl

protected theorem injective (e : G ≃* H) : Function.Injective e.toHom := by
  intro a b hab
  have h := congrArg e.invHom hab
  rw [invHom_toHom e] at h
  rw [invHom_toHom e] at h
  exact h

protected theorem surjective (e : G ≃* H) : Function.Surjective e.toHom := by
  intro x
  refine ⟨e.invHom x, ?_⟩
  rw [toHom_invHom]

-- a bijective hom is an isomorphism
-- (the inverse is `Function.surjInv` from Core/Function.lean, hence `noncomputable`)
noncomputable def ofBijective (f : G →* H)
    (hi : Function.Injective f) (hs : Function.Surjective f) : G ≃* H where
  toHom := f
  invHom := {
    toFun := Function.surjInv hs
    map_mul := by
      intro a b
      apply hi
      rw [f.map_mul]
      rw [Function.surjInv_eq hs, Function.surjInv_eq hs, Function.surjInv_eq hs]
  }
  left_inv := by
    ext a
    apply hi
    rw [Hom.id_apply a]
    rw [Hom.comp_apply]
    rw [Function.surjInv_eq hs]
  right_inv := by
    ext a
    rw [Hom.id_apply a]
    rw [Hom.comp_apply]
    rw [Function.surjInv_eq hs]

theorem ofBijective_toHom (f : G →* H)
    (hi : Function.Injective f) (hs : Function.Surjective f) :
    (ofBijective f hi hs).toHom = f := rfl

end Iso
end My
