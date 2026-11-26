import Algebra.Group.Basic
import Algebra.Group.MinimalAxioms

/-! # Group structures are determined by their multiplication

Mathlib: `Mathlib/Algebra/Group/Ext.lean`.

`Group.ext` compares two `Group` *instances on the same type* `G`, not two groups: if their
multiplications agree, so do their `1` and `⁻¹`, hence the whole structure. It is the
uniqueness of the identity and of inverses, packaged as an equation between structures.
(Two groups that are "the same" in the usual sense are isomorphic: that is `G ≃* H`.)

Each instance is passed explicitly, as in `@one_mul G g₁ a`, so you can say which group
structure a lemma is about. For a given `g`, `@one_mul G g a` reads `g.mul g.one a = a`.

The multiplications are compared through the projections, `g₁.mul = g₂.mul`. Mathlib writes
`(letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)`, which is the same
statement (equal by `rfl`) spelled with `*`'s canonical form; `MulOneClass.ext` in Mathlib uses
the projections, as here. The goal view shows `g₁.mul = g₂.mul` as `Mul.mul = Mul.mul`, since
the instance is hidden: `set_option pp.explicit true in` shows it, and destructuring the
instances (which names the fields) makes it readable for good. -/

universe u

namespace My

/-- Same multiplication, same identity (not in Mathlib in this form: the content of
`MulOneClass.ext`). `1₁ = 1₁ * 1₂ = 1₂`: one step is `g₂`'s `mul_one`, the other `g₁`'s
`one_mul`, and they chain because the two multiplications are one. -/
theorem Group.one_eq_of_mul_eq {G : Type u} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) :
    g₁.one = g₂.one := by
  obtain @⟨⟨mul₁⟩, ⟨one₁⟩, ⟨inv₁⟩, assoc₁, one_mul₁, mul_one₁,
    inv_mul_cancel₁, mul_inv_cancel₁⟩ := g₁
  obtain @⟨⟨mul₂⟩, ⟨one₂⟩, ⟨inv₂⟩, assoc₂, one_mul₂, mul_one₂,
    inv_mul_cancel₂, mul_inv_cancel₂⟩ := g₂
  sorry

/-- Same multiplication, same inverses (not in Mathlib). With one multiplication and, by
`Group.one_eq_of_mul_eq`, one identity, `a⁻¹₁` is an inverse of `a` in `g₂` too: uniqueness
of inverses there. -/
theorem Group.inv_eq_of_mul_eq {G : Type u} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) :
    g₁.inv = g₂.inv :=
  sorry

/-- Two group structures on `G` with the same multiplication are equal (not in Mathlib in this
form: Mathlib's hypothesis is the `letI` spelling of `h_mul`).

Plan: the identities agree (`Group.one_eq_of_mul_eq`), the inverses agree
(`Group.inv_eq_of_mul_eq`); destructure both instances and substitute. -/
theorem Group.ext {G : Type u} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) :
    g₁ = g₂ := by
  obtain @⟨⟨mul₁⟩, ⟨one₁⟩, ⟨inv₁⟩, assoc₁, one_mul₁, mul_one₁,
    inv_mul_cancel₁, mul_inv_cancel₁⟩ := g₁
  obtain @⟨⟨mul₂⟩, ⟨one₂⟩, ⟨inv₂⟩, assoc₂, one_mul₂, mul_one₂,
    inv_mul_cancel₂, mul_inv_cancel₂⟩ := g₂

  have same_unit : one₁ = one₂:= Group.one_eq_of_mul_eq h_mul
  have same_inv : inv₁= inv₂ := Group.inv_eq_of_mul_eq h_mul

  subst same_unit
  subst same_inv
  subst h_mul
  rfl

theorem Group.ext_iff {G : Type u} {g₁ g₂ : Group G} : g₁ = g₂ ↔ g₁.mul = g₂.mul :=
  Iff.intro (λ (he : g₁ = g₂) => by subst he; rfl)
            (λ h_mul => Group.ext h_mul)

end My
