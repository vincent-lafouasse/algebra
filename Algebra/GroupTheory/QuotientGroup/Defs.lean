import Algebra.GroupTheory.Coset
import Algebra.Group.Subgroup.Normal
import Algebra.Group.MinimalAxioms

/-! # Quotient groups `G ⧸ N`

Mathlib: `Mathlib/Algebra/Quotient.lean` (the `⧸` notation),
`Mathlib/GroupTheory/Coset/Defs.lean` (`G ⧸ s` for any subgroup),
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` (the group structure when `N` is normal).

`G ⧸ s` is core's `Quotient (leftRel s)`: the set of left cosets. Every element is `↑a`
(`QuotientGroup.mk a`) for some `a : G`, and `↑a = ↑b ↔ a⁻¹ * b ∈ s`. Those two facts
(`mk_surjective` / `induction_on` and `eq`) are all you should need about it.

When `N` is normal, `↑a * ↑b := ↑(a * b)` is well defined, and `G ⧸ N` is a group. -/

universe u v

namespace My

/-- `A ⧸ b`: the quotient of `A` by `b` (Mathlib uses one notation for groups, rings,
modules, …) -/
class HasQuotient (A : outParam (Type u)) (B : Type v) where
  -- `(A)` makes `A` explicit in the projection: `HasQuotient.Quotient A b`
  Quotient (A) : B → Type max u v

notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H

namespace QuotientGroup

section Classes

variable {α : Type u} [Group α]

instance instHasQuotientSubgroup : HasQuotient α (Subgroup α) :=
  ⟨λ s => Quotient (leftRel s)⟩

@[coe]
def mk {s : Subgroup α} (a : α) : α ⧸ s :=
  sorry

instance {s : Subgroup α} : CoeTC α (α ⧸ s) :=
  ⟨mk⟩

variable {s : Subgroup α}

-- two cosets are equal iff the representatives differ by an element of s
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
  sorry

theorem mk_surjective : Function.Surjective (mk : α → α ⧸ s) :=
  sorry

-- to prove something for every element of the quotient, prove it for every `↑z`
theorem induction_on {C : α ⧸ s → Prop} (q : α ⧸ s) (H : ∀ a : α, C a) : C q :=
  sorry

-- the class of g is the coset g • s
theorem eq_class_eq_leftCoset (s : Subgroup α) (g : α) :
    {x : α | (x : α ⧸ s) = g} = g • (s : Set α) :=
  sorry

end Classes

/-! ### The group structure on `G ⧸ N` -/

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

-- `Quotient.lift₂ f h` defines a function on two classes from `f` on representatives;
-- `h` says `f` doesn't depend on the choice of representatives: that is where normality is used
instance : Mul (G ⧸ N) :=
  sorry

instance : One (G ⧸ N) :=
  sorry

instance : Inv (G ⧸ N) :=
  sorry

-- the three left axioms; `Group.ofLeftAxioms` proves `mul_one` and `mul_inv_cancel`
instance Quotient.group : Group (G ⧸ N) :=
  Group.ofLeftAxioms sorry sorry sorry

theorem mk_mul (a b : G) : ((a * b : G) : G ⧸ N) = (a : G ⧸ N) * (b : G ⧸ N) :=
  sorry

theorem mk_inv (a : G) : ((a⁻¹ : G) : G ⧸ N) = (a : G ⧸ N)⁻¹ :=
  sorry

theorem mk_one : ((1 : G) : G ⧸ N) = 1 :=
  sorry

theorem eq_one_iff {N : Subgroup G} [N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N :=
  sorry

-- the quotient map, as a hom
def mk' : G →* G ⧸ N :=
  sorry

theorem mk'_apply (x : G) : mk' N x = x :=
  sorry

theorem mk'_surjective : Function.Surjective (mk' N) :=
  sorry

theorem ker_mk' : (mk' N).ker = N :=
  sorry

end QuotientGroup

end My
