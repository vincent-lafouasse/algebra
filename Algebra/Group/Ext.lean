import Algebra.Group.Basic

/-! # Group structures are determined by their multiplication

Mathlib: `Mathlib/Algebra/Group/Ext.lean`.

`Group.ext` compares two `Group` *instances on the same type* `G`, not two groups: if their
multiplications agree, so do their `1` and `⁻¹`, hence the whole structure. It is the
uniqueness of the identity and of inverses, packaged as an equation between structures.
(Two groups that are "the same" in the usual sense are isomorphic: that is `G ≃* H`.)

Each instance is passed explicitly, as in `@one_mul G g₁ a`, so you can say which group
structure a lemma is about. -/

universe u

namespace My

/-- Two group structures on `G` with the same multiplication are equal.

Plan: show the identities agree (`1₁` is a left identity for `*₁ = *₂`, and `1₂` is a
right identity for `*₂`), then the inverses (`funext`, then uniqueness of inverses in one
structure), then destructure both instances and substitute. -/
theorem Group.ext {G : Type u} ⦃g₁ g₂ : Group G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) :
    g₁ = g₂ :=
  have h_one := congrFun h_mul g₁.one
  have h_one := congrFun h_one g₂.one
  sorry

theorem Group.ext_iff {G : Type u} {g₁ g₂ : Group G} :
    g₁ = g₂ ↔ (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G) :=
  Iff.intro (λ (he : g₁ = g₂) => by subst he; rfl)
            (λ h_mul => Group.ext h_mul)

end My
