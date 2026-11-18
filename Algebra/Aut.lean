import Algebra.Normal
import Algebra.Iso

universe u v

namespace My

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
  ext x
  rw [conj_apply, id_apply]
  rw [inv_one, mul_one, one_mul]

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
def conjIso (g : G) : G ≃* G where
  toHom := Hom.conj g
  invHom := Hom.conj g⁻¹
  left_inv := by
    rw [← Hom.conj_mul]
    rw [inv_mul_cancel]
    rw [Hom.conj_one]
  right_inv := by
    rw [← Hom.conj_mul]
    rw [mul_inv_cancel]
    rw [Hom.conj_one]

-- Aut(G): automorphisms under composition; (e * e') x = e (e' x)
instance : Group (G ≃* G) where
  mul e e' := e'.trans e
  one := refl G
  inv e := e.symm
  mul_assoc := by
    intro a b c
    show c.trans (b.trans a) = (c.trans b).trans a
    apply ext
    rw [trans_toHom, trans_toHom, trans_toHom, trans_toHom]
    rw [Hom.comp_assoc]
  one_mul := by
    intro a
    show (a.trans (refl G)) = a
    apply ext
    rw [trans_toHom, refl_toHom]
    rw [Hom.id_comp]
  inv_mul_cancel := by
    intro a
    show a.trans a.symm = refl G
    apply ext
    rw [refl_toHom, trans_toHom, symm_toHom]
    exact a.left_inv

theorem mul_toHom (e e' : G ≃* G) : (e * e').toHom = e.toHom.comp e'.toHom := rfl

theorem one_toHom : (one : G ≃* G).toHom = Hom.id G := rfl

theorem inv_toHom (e : G ≃* G) : (e⁻¹).toHom = e.invHom := rfl

theorem conjIso_toHom (g : G) : (conjIso g).toHom = Hom.conj g := rfl

-- g ↦ (conjugation by g)
def conjHom : G →* (G ≃* G) where
  toFun := conjIso
  map_mul := by
    intro a b
    apply ext
    rw [conjIso_toHom, mul_toHom, conjIso_toHom, conjIso_toHom]
    rw [Hom.conj_mul]

theorem conjHom_apply (g x : G) : (conjHom g).toHom x = g * x * g⁻¹ := rfl

theorem conjHom_eq (g : G) : conjHom g = conjIso g := rfl

-- the kernel of conjugation is the center
theorem ker_conjHom : Hom.ker (conjHom : G →* (G ≃* G)) = Subgroup.center G := by
  ext a
  constructor
  · intro h g
    rw [Hom.mem_ker] at h
    have hg := congrArg (λ (e : (G ≃* G)) => e.toHom g) h
    rw [conjHom_apply] at hg
    rw [one_toHom] at hg
    rw [Hom.id_apply] at hg
    rw [← eq_mul_inv_iff_mul_eq] at hg
    rw [inv_inv] at hg
    exact hg.symm
  · intro h
    rw [Hom.mem_ker]
    apply ext
    rw [Subgroup.mem_center] at h
    rw [one_toHom]
    ext x
    rw [Hom.id_apply]
    rw [conjHom_apply]
    have h' := h x
    rw [← eq_mul_inv_iff_mul_eq] at h'
    exact h'.symm

-- inner automorphisms are normal in Aut(G): φ ∘ conj g ∘ φ⁻¹ = conj (φ g)
theorem conj_by_aut (φ : G ≃* G) (g : G) :
    φ * conjIso g * φ⁻¹ = conjIso (φ.toHom g) := by
  apply ext
  rw [mul_toHom, mul_toHom]
  rw [inv_toHom]
  rw [conjIso_toHom, conjIso_toHom]
  apply Hom.ext
  intro x
  rw [Hom.comp_apply, Hom.comp_apply]
  rw [Hom.conj_apply, Hom.conj_apply]
  rw [Hom.map_conj]
  rw [toHom_invHom]

instance range_conjHom_normal : (Hom.range (conjHom : G →* (G ≃* G))).Normal where
  conj_mem := by
    intro n hn g
    rw [Hom.mem_range]
    rw [Hom.mem_range] at hn
    obtain ⟨k, hnk⟩ := hn
    refine ⟨g.toHom k, ?_⟩
    rw [← hnk]
    exact (conj_by_aut g k).symm

end Iso

namespace Subgroup

variable {G : Type u} [Group G]

-- normal ↔ invariant under every conjugation
theorem normal_iff_conj_invariant (N : Subgroup G) :
    N.Normal ↔ ∀ g : G, Hom.map (Hom.conj g) N = N :=
  sorry

end Subgroup
end My
