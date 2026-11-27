import Algebra.Group.Hom
import Base.Logic.Relation
import Base.Logic.Equiv

/-! # Free groups

Mathlib: `Mathlib/GroupTheory/FreeGroup/Basic.lean`.

The free group on `α` is words in the letters `x` and `x⁻¹` (`x : α`), where the only rule is
`x x⁻¹ = x⁻¹ x = 1`. A letter is `(x, true)` for `x` and `(x, false)` for `x⁻¹`, so a word is a
`List (α × Bool)`.

`Red.Step` cancels one adjacent pair `(x, b) (x, !b)`; `Red` is any number of steps
(`ReflTransGen`). Mathlib's `FreeGroup α` is `Quot Red.Step`: a quotient by a relation that is
*not* an equivalence, so `Relation.EqvGen` and `Quot.eq` (`Base/Logic/Relation.lean`) are what
tell you when two words are equal in it.

The universal property (`lift`): a map `α → G` into any group extends to exactly one hom
`FreeGroup α →* G`. That is what "free" means: no relations beyond the group axioms.

The hard theorem is that two words are equal in `FreeGroup α` iff they reduce to a common word
(`Red.exact`), which rests on Church–Rosser for `Red` (`church_rosser`): two reductions of the
same word can always be brought back together. The other route, `Reduce.lean`, picks the unique
fully reduced word.

Mathlib defines `Red.Step` as an `inductive` with one constructor, `Red.Step.not`; here it is
an opaque `def`, with `Red.Step.not` as its stated rule. `red_def` is not in Mathlib, where `Red`
unfolds to `ReflTransGen Red.Step`. -/

universe u v

namespace My

variable {α : Type u}

namespace FreeGroup

def Red.Step : List (α × Bool) → List (α × Bool) → Prop :=
  sorry

-- the one rule: cancel `x x⁻¹` (or `x⁻¹ x`) anywhere in the word
theorem Red.Step.not {L₁ L₂ : List (α × Bool)} {x : α} {b : Bool} :
    Red.Step (L₁ ++ (x, b) :: (x, !b) :: L₂) (L₁ ++ L₂) :=
  sorry

def Red : List (α × Bool) → List (α × Bool) → Prop :=
  sorry

variable {L L₁ L₂ L₃ : List (α × Bool)}

theorem red_def : Red L₁ L₂ ↔ Relation.ReflTransGen Red.Step L₁ L₂ :=
  sorry

theorem Red.refl : Red L L :=
  sorry

theorem Red.trans : Red L₁ L₂ → Red L₂ L₃ → Red L₁ L₃ :=
  sorry

-- Church–Rosser: two reductions of the same word meet again
theorem church_rosser : Red L₁ L₂ → Red L₁ L₃ → Relation.Join Red L₂ L₃ :=
  sorry

end FreeGroup

-- explicit binders: with a `sorry` body, a `variable` would be dropped from the signature
def FreeGroup (α : Type u) : Type u :=
  sorry

namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}

-- the class of a word
def mk (L : List (α × Bool)) : FreeGroup α :=
  sorry

instance : Mul (FreeGroup α) :=
  sorry

instance : One (FreeGroup α) :=
  sorry

instance : Inv (FreeGroup α) :=
  sorry

instance : Group (FreeGroup α) :=
  sorry

-- `x ↦ x⁻¹` on words: reverse, and flip every letter
def invRev (w : List (α × Bool)) : List (α × Bool) :=
  sorry

theorem one_eq_mk : (1 : FreeGroup α) = mk [] :=
  sorry

theorem mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) :=
  sorry

theorem inv_mk : (mk L)⁻¹ = mk (invRev L) :=
  sorry

-- equal in the free group iff they reduce to a common word
theorem Red.exact : mk L₁ = mk L₂ ↔ Relation.Join Red L₁ L₂ :=
  sorry

-- the generators
def of (x : α) : FreeGroup α :=
  sorry

theorem of_injective : Function.Injective (@of α) :=
  sorry

protected theorem induction_on {motive : FreeGroup α → Prop} (z : FreeGroup α) (one : motive 1)
    (of : ∀ x, motive (of x)) (inv_of : ∀ x, motive (FreeGroup.of x) → motive (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive z :=
  sorry

/-! ### The universal property -/

variable {β : Type v} [Group β]

def lift : (α → β) ≃ (FreeGroup α →* β) :=
  sorry

theorem lift_apply_of {f : α → β} {x : α} : lift f (of x) = f x :=
  sorry

theorem lift_unique {f : α → β} (g : FreeGroup α →* β) (hg : ∀ x, g (of x) = f x)
    {x : FreeGroup α} : g x = lift f x :=
  sorry

-- homs out of a free group are determined by the generators
theorem ext_hom (f g : FreeGroup α →* β) (h : ∀ a, f (of a) = g (of a)) : f = g :=
  sorry

end FreeGroup

end My
