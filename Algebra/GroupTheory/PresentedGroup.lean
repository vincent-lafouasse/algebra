import Algebra.GroupTheory.FreeGroup.Basic
import Algebra.GroupTheory.QuotientGroup.Basic
import Algebra.Group.Subgroup.Basic

/-! # Presented groups `⟨α | rels⟩`

Mathlib: `Mathlib/GroupTheory/PresentedGroup.lean`.

Generators `α` and relations `rels : Set (FreeGroup α)`: the group is
`FreeGroup α ⧸ normalClosure rels`, the free group where every relation is forced to be `1`
(and so are its conjugates, products and inverses, which is why the *normal* closure).

The universal property (`toGroup`): a map `f : α → G` whose extension kills every relation
gives a hom `PresentedGroup rels →* G`. That is how you check a presentation: to show the
dihedral group is `⟨r, s | rⁿ, s², srsr⟩`, map the generators and check three equations.

This file is where free groups, normal closures and Noether 1 (`QuotientGroup.lift`) meet. -/

universe u v

namespace My

-- explicit binders: with a `sorry` body, a `variable` would be dropped from the signature
def PresentedGroup {α : Type u} (rels : Set (FreeGroup α)) : Type u :=
  sorry

namespace PresentedGroup

variable {α : Type u}

instance (rels : Set (FreeGroup α)) : Group (PresentedGroup rels) :=
  sorry

def mk (rels : Set (FreeGroup α)) : FreeGroup α →* PresentedGroup rels :=
  sorry

theorem mk_surjective (rels : Set (FreeGroup α)) : Function.Surjective (mk rels) :=
  sorry

def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  sorry

theorem mk_eq_one_iff {rels : Set (FreeGroup α)} {x : FreeGroup α} :
    mk rels x = 1 ↔ x ∈ Subgroup.normalClosure rels :=
  sorry

-- every relation holds
theorem one_of_mem {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x ∈ rels) : mk rels x = 1 :=
  sorry

theorem induction_on {rels : Set (FreeGroup α)} {C : PresentedGroup rels → Prop}
    (x : PresentedGroup rels) (H : ∀ z, C (mk rels z)) : C x :=
  sorry

/-! ### The universal property -/

variable {G : Type v} [Group G] {f : α → G} {rels : Set (FreeGroup α)}

theorem closure_rels_subset_ker (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    Subgroup.normalClosure rels ≤ (FreeGroup.lift f).ker :=
  sorry

def toGroup (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) : PresentedGroup rels →* G :=
  sorry

theorem toGroup.of (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) {x : α} : toGroup h (of x) = f x :=
  sorry

theorem toGroup.unique (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels →* G)
    (hg : ∀ x : α, g (PresentedGroup.of x) = f x) {x : PresentedGroup rels} : g x = toGroup h x :=
  sorry

theorem ext {φ ψ : PresentedGroup rels →* G} (hx : ∀ x : α, φ (of x) = ψ (of x)) : φ = ψ :=
  sorry

end PresentedGroup

end My
