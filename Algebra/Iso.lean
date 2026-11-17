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
def symm (e : G ≃* H) : H ≃* G :=
  sorry

-- G ≅ H → H ≅ K → G ≅ K
def trans (e : G ≃* H) (e' : H ≃* K) : G ≃* K :=
  sorry

theorem injective (e : G ≃* H) : Function.Injective e.toHom :=
  sorry

theorem surjective (e : G ≃* H) : Function.Surjective e.toHom :=
  sorry

-- a bijective hom is an isomorphism
-- (building the inverse needs `Classical.choose`, hence `noncomputable`)
noncomputable def ofBijective (f : G →* H)
    (hi : Function.Injective f) (hs : Function.Surjective f) : G ≃* H :=
  sorry

theorem ofBijective_toHom (f : G →* H)
    (hi : Function.Injective f) (hs : Function.Surjective f) :
    (ofBijective f hi hs).toHom = f :=
  sorry

end Iso
end Algebra
