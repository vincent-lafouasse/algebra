import Algebra

/-! # Chapter 18: groups (exercises 18.1 – 18.5) -/

universe u

namespace Exercises.Ch18

open My

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

This is `My.Subgroup.center` (the book writes `h * g = g * h`, Mathlib and the library
`g * h = h * g`). Stated here as the existence of a subgroup with that carrier. -/

theorem ex_18_2 (G : Type u) [Group G] :
    ∃ Z : Subgroup G, ∀ h : G, h ∈ Z ↔ ∀ g : G, h * g = g * h :=
  sorry

/-! ## 18.3
Soit G un groupe et H une partie de G. Montrer que H est un sous-groupe de G si, et
seulement si, H est non vide et : ∀ (x, y) ∈ H², xy⁻¹ ∈ H.

"H is a subgroup" = some `Subgroup G` has exactly H as its members. -/

theorem ex_18_3 {G : Type u} [Group G] (H : Set G) :
    (∃ S : Subgroup G, ∀ x, x ∈ S ↔ x ∈ H) ↔
      (∃ x, x ∈ H) ∧ ∀ x y, x ∈ H → y ∈ H → x * y⁻¹ ∈ H :=
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
