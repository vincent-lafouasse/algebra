import Algebra

/-! # Chapter 18: groups (exercises 18.1 – 18.5) -/

universe u

namespace Exercises.Ch18

open My My.Group

/-! ## 18.1
Soit X un ensemble possédant au moins deux éléments distincts a et b. Construire deux
applications f_a et f_b de X dans X telles que f_a ∘ f_b ≠ f_b ∘ f_a. -/

theorem ex_18_1 {X : Type u} {a b : X} (hab : a ≠ b) :
    ∃ fa fb : X → X, fa ∘ fb ≠ fb ∘ fa := by
  refine ⟨λ _ => a, λ _ => b, ?_⟩
  intro eq
  have falsity := congrFun eq a
  simp only [Function.comp] at falsity
  exact hab falsity

/-! ## 18.2
Soit G un groupe et Z = {h ∈ G : ∀ g ∈ G, hg = gh}. Montrer que Z est un sous-groupe de G.

Already done: this is `My.Subgroup.center` (note the book writes `h * g = g * h`, the
library `g * h = h * g`). Stated here as the existence of a subgroup with that carrier. -/

theorem ex_18_2 (G : Type u) [Group G] :
    ∃ Z : Subgroup G, ∀ h : G, h ∈ Z ↔ ∀ g : G, h * g = g * h := by
  have Z : Subgroup G := {
    mem := λ h => ∀ g : G, h * g = g * h
    one_mem := sorry
    mul_mem := sorry
    inv_mem := sorry
  }
  refine ⟨Z, $_⟩

/-! ## 18.3
Soit G un groupe et H une partie de G. Montrer que H est un sous-groupe de G si, et
seulement si, H est non vide et : ∀ (x, y) ∈ H², xy⁻¹ ∈ H.

"H is a subgroup" = some `Subgroup G` has exactly H as its members. -/

theorem ex_18_3 {G : Type u} [Group G] (H : G → Prop) :
    (∃ S : Subgroup G, ∀ x, x ∈ S ↔ H x) ↔
      (∃ x, H x) ∧ ∀ x y, H x → H y → H (x * y⁻¹) :=
  sorry

/-! ## 18.4
On munit ℝ₊* × ℝ de sa structure naturelle de groupe pour la loi produit.
Montrer que φ : ℝ₊* × ℝ → ℂ*, (r, θ) ↦ r e^{iθ} est un morphisme de groupes.

Needs ℝ, ℂ and the exponential: postponed until Mathlib and the bridge are set up. -/

/-! ## 18.5
Soit G un groupe. Montrer que G est commutatif si, et seulement si, φ : G → G, x ↦ x²
est un endomorphisme de G. -/

theorem ex_18_5 (G : Type u) [Group G] :
    (∀ a b : G, a * b = b * a) ↔ ∃ φ : G →* G, ∀ x, φ x = x * x :=
  sorry

end Exercises.Ch18
