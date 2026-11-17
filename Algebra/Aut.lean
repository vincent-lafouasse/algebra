import Algebra.Normal
import Algebra.Iso

universe u v

namespace Algebra

open Group

namespace Hom

variable {G : Type u} [Group G]

-- conjugation by g: x ↦ g x g⁻¹
def conj (g : G) : G →* G where
  toFun := λ x => g * x * g⁻¹
  map_mul := λ a b => by
    simp only [mul_assoc]
    rw [inv_mul_cancel_left]

theorem conj_apply (g x : G) : conj g x = g * x * g⁻¹ := rfl

theorem conj_one : conj (one : G) = id G := by
  unfold conj
  ext x
  rw [mk_apply]
  rw [id_apply]
  rw [inv_one]
  rw [mul_one, one_mul]

theorem conj_mul (g h : G) : conj (g * h) = comp (conj g) (conj h) := by
  ext x
  rw [comp_apply]
  rw [conj_apply, conj_apply, conj_apply]
  rw [inv_prod]
  simp only [mul_assoc]

end Hom

namespace Iso

variable {G : Type u} {H : Type v} [Group G] [Group H]

-- an iso is determined by its forward hom (inverses are unique)
theorem ext {e e' : G ≃* H} (h : e.toHom = e'.toHom) : e = e' := by
  cases e with
  | mk f g hl hr =>
    cases e' with
    | mk f' g' hl' hr' =>
      have eq : f = f' := h
      subst eq
      have eq' : g = g' := by
        calc g
         _ = Hom.comp g (Hom.id H) := by rw [Hom.comp_id]
         _ = Hom.comp g (f.comp g') := by rw [hr']
         _ = Hom.comp (g.comp f) g' := by rw [Hom.comp_assoc]
         _ = Hom.comp (Hom.id G) g' := by rw [hl]
         _ = g' := by rw [Hom.id_comp]
      subst eq'
      rfl

-- conjugation by g as an automorphism, with inverse conjugation by g⁻¹
def conjIso (g : G) : G ≃* G :=
  sorry

-- Aut(G): automorphisms under composition; (e * e') x = e (e' x)
instance : Group (G ≃* G) where
  mul e e' := e'.trans e
  one := refl G
  inv e := e.symm
  mul_assoc := sorry
  one_mul := sorry
  inv_mul_cancel := sorry

-- g ↦ (conjugation by g)
def conjHom : G →* (G ≃* G) :=
  sorry

theorem conjHom_apply (g x : G) : (conjHom g).toHom x = g * x * g⁻¹ :=
  sorry

-- the kernel of conjugation is the center
theorem ker_conjHom : Hom.ker (conjHom : G →* (G ≃* G)) = Subgroup.center G :=
  sorry

-- inner automorphisms are normal in Aut(G): φ ∘ conj g ∘ φ⁻¹ = conj (φ g)
theorem conj_by_aut (φ : G ≃* G) (g : G) :
    φ * conjIso g * φ⁻¹ = conjIso (φ.toHom g) :=
  sorry

instance range_conjHom_normal : (Hom.range (conjHom : G →* (G ≃* G))).Normal :=
  sorry

end Iso

namespace Subgroup

variable {G : Type u} [Group G]

-- normal ↔ invariant under every conjugation
theorem normal_iff_conj_invariant (N : Subgroup G) :
    N.Normal ↔ ∀ g : G, Hom.map (Hom.conj g) N = N :=
  sorry

end Subgroup
end Algebra
