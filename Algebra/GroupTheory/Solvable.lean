import Algebra.GroupTheory.Commutator
import Algebra.GroupTheory.Simple
import Algebra.GroupTheory.QuotientGroup.Basic

/-! # Solvable groups

Mathlib: `Mathlib/GroupTheory/Solvable.lean`.

The derived series takes commutators again and again: `G⁽⁰⁾ = G`, `G⁽ⁿ⁺¹⁾ = ⁅G⁽ⁿ⁾, G⁽ⁿ⁾⁆`.
`G` is solvable when it reaches `⊥`. Abelian groups are solvable in one step, and solvability
passes to subgroups, quotients and extensions.

This is the "solvable" of "solvable by radicals": a polynomial is solvable by radicals exactly
when its Galois group is solvable, and `S₅` is not (its derived series stops at `A₅`, which is
simple and not abelian). Nothing here needs finiteness.

Mathlib uses `[IsMulCommutative G]` where `[CommGroup G]` appears below. -/

universe u v w

namespace My

namespace Subgroup

-- explicit binders: with a `sorry` body, a `variable` would be dropped from the signature
def derivedSeries (G : Type u) [Group G] : Nat → Subgroup G :=
  sorry

variable (G : Type u) [Group G]

theorem derivedSeries_zero : derivedSeries G 0 = ⊤ :=
  sorry

theorem derivedSeries_succ (n : Nat) :
    derivedSeries G (n + 1) = ⁅derivedSeries G n, derivedSeries G n⁆ :=
  sorry

theorem derivedSeries_normal (n : Nat) : (derivedSeries G n).Normal :=
  sorry

-- (`My.`: inside `Subgroup`, `commutator` is the bracket instance)
theorem derivedSeries_one : derivedSeries G 1 = My.commutator G :=
  sorry

-- (Mathlib: `Antitone (derivedSeries G)`; `Nat` has no `My.Preorder` instance yet)
theorem derivedSeries_antitone {m n : Nat} (h : m ≤ n) : derivedSeries G n ≤ derivedSeries G m :=
  sorry

variable {G} {G' : Type v} [Group G'] (f : G →* G')

theorem map_derivedSeries_le_derivedSeries (n : Nat) :
    map f (derivedSeries G n) ≤ derivedSeries G' n :=
  sorry

theorem derivedSeries_le_map_derivedSeries (hf : Function.Surjective f) (n : Nat) :
    derivedSeries G' n ≤ map f (derivedSeries G n) :=
  sorry

end Subgroup

namespace Group

variable (G : Type u) [Group G]

class IsSolvable : Prop where
  solvable : ∃ n : Nat, Subgroup.derivedSeries G n = ⊥

variable {G}

-- (Mathlib: an anonymous instance, for `[IsMulCommutative G]`)
instance isSolvable_of_commGroup {G : Type u} [CommGroup G] : IsSolvable G :=
  sorry

theorem isSolvable_of_comm (h : ∀ a b : G, a * b = b * a) : IsSolvable G :=
  sorry

theorem isSolvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G :=
  sorry

variable {G' : Type v} [Group G'] {f : G' →* G}

-- solvability passes to subgroups (through an injection)…
theorem isSolvable_of_isSolvable_injective (hf : Function.Injective f) [IsSolvable G] :
    IsSolvable G' :=
  sorry

-- (Mathlib: an anonymous instance)
instance subgroup_isSolvable (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
  sorry

-- …to quotients (through a surjection)…
theorem isSolvable_of_surjective (hf : Function.Surjective f) [IsSolvable G'] : IsSolvable G :=
  sorry

-- (Mathlib: an anonymous instance)
instance quotient_isSolvable (H : Subgroup G) [H.Normal] [IsSolvable G] : IsSolvable (G ⧸ H) :=
  sorry

-- …and to extensions: `G` is solvable if a normal subgroup and its quotient are
theorem isSolvable_of_ker_le_range {G'' : Type w} [Group G''] (f : G' →* G) (g : G →* G'')
    (hfg : g.ker ≤ f.range) [IsSolvable G'] [IsSolvable G''] : IsSolvable G :=
  sorry

theorem isSolvable_iff_subgroup_quotient (H : Subgroup G) [H.Normal] :
    IsSolvable G ↔ IsSolvable H ∧ IsSolvable (G ⧸ H) :=
  sorry

end Group

-- a simple group is solvable exactly when it is abelian
theorem IsSimpleGroup.comm_iff_isSolvable {G : Type u} [Group G] [IsSimpleGroup G] :
    (∀ a b : G, a * b = b * a) ↔ Group.IsSolvable G :=
  sorry

end My
