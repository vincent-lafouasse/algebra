import Algebra.Hom

universe u v w

namespace Algebra

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
def refl (G : Type u) [Group G] : G ≃* G where
  toHom := Hom.id G
  invHom := Hom.id G
  left_inv := by
    rw [Hom.comp_id]
  right_inv := by
    rw [Hom.comp_id]

-- G ≅ H → H ≅ G
def symm (e : G ≃* H) : H ≃* G where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

-- G ≅ H → H ≅ K → G ≅ K
def trans (e : G ≃* H) (e' : H ≃* K) : G ≃* K where
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

theorem injective (e : G ≃* H) : Function.Injective e.toHom := by
  intro a b hab
  have h := congrArg e.invHom hab
  rw [invHom_toHom e] at h
  rw [invHom_toHom e] at h
  exact h

theorem surjective (e : G ≃* H) : Function.Surjective e.toHom := by
  intro x
  refine ⟨e.invHom x, ?_⟩
  rw [toHom_invHom]

noncomputable def invFun (f : G →* H) (hs : Function.Surjective f) : H → G :=
  λ y => Classical.choose (hs y)

theorem invFun_spec (f : G →* H) (hs : Function.Surjective f) (y : H) :
    f (invFun f hs y) = y :=
  Classical.choose_spec (hs y)

-- a bijective hom is an isomorphism
-- (building the inverse needs `Classical.choose`, hence `noncomputable`)
noncomputable def ofBijective (f : G →* H)
    (hi : Function.Injective f) (hs : Function.Surjective f) : G ≃* H where
  toHom := f
  invHom := {
    toFun := invFun f hs
    map_mul := by
      intro a b
      apply hi
      rw [f.map_mul]
      rw [invFun_spec, invFun_spec, invFun_spec]
  }
  left_inv := by
    ext a
    apply hi
    rw [Hom.id_apply a]
    rw [Hom.comp_apply]
    rw [invFun_spec]
  right_inv := sorry

theorem ofBijective_toHom (f : G →* H)
    (hi : Function.Injective f) (hs : Function.Surjective f) :
    (ofBijective f hi hs).toHom = f :=
  sorry

end Iso
end Algebra
