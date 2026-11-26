import Algebra.GroupTheory.Coset
import Algebra.Group.Subgroup.Normal
import Algebra.Group.MinimalAxioms

/-! # Quotient groups `G ⧸ N`

Mathlib: `Mathlib/Algebra/Quotient.lean` (the `⧸` notation),
`Mathlib/GroupTheory/Coset/Defs.lean` (`G ⧸ H` for any subgroup),
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` (the group structure when `N` is normal).

`G ⧸ H` is core's `Quotient (leftRel H)`: the set of left cosets. Every element is `↑a`
(`QuotientGroup.mk a`) for some `a : G`, and `↑a = ↑b ↔ a⁻¹ * b ∈ H`. Those two facts
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

variable {G : Type u} [Group G]

instance instHasQuotientSubgroup : HasQuotient G (Subgroup G) :=
  ⟨λ H => Quotient (leftRel H)⟩

@[coe]
def mk {H : Subgroup G} (a : G) : G ⧸ H :=
  sorry

instance {H : Subgroup G} : CoeTC G (G ⧸ H) :=
  ⟨mk⟩

variable {H : Subgroup G}

-- two cosets are equal iff the representatives differ by an element of `H`
protected theorem eq {a b : G} : (a : G ⧸ H) = b ↔ a⁻¹ * b ∈ H :=
  sorry

theorem mk_surjective : Function.Surjective (mk : G → G ⧸ H) :=
  sorry

-- to prove something for every element of the quotient, prove it for every `↑a`
-- (Mathlib calls the hypothesis `H`; here that is the subgroup)
theorem induction_on {C : G ⧸ H → Prop} (q : G ⧸ H) (h : ∀ a : G, C a) : C q :=
  sorry

-- the class of `g` is the coset `g • H`
theorem eq_class_eq_leftCoset (H : Subgroup G) (g : G) :
    {x : G | (x : G ⧸ H) = g} = g • (H : Set G) :=
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
