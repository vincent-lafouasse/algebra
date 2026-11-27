import Algebra.Group.Subgroup.Normal
import Base.Logic.Nontrivial

/-! # Simple groups

Mathlib: `Mathlib/GroupTheory/Subgroup/Simple.lean`.

A group is simple when its only normal subgroups are `⊥` and `⊤`, and it is not trivial. Simple
groups are to groups what primes are to integers: they have no proper quotients, and every
finite group is built from them (Jordan–Hölder). Examples come later: `ℤ/p` for `p` prime, and
`Aₙ` for `n ≥ 5`, which is what makes the quintic unsolvable. -/

universe u v

namespace My

variable (G : Type u) [Group G]

class IsSimpleGroup : Prop extends Nontrivial G where
  eq_bot_or_eq_top_of_normal : ∀ (H : Subgroup G) [H.Normal], H = ⊥ ∨ H = ⊤

variable {G}

theorem Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] (H : Subgroup G) [H.Normal] :
    H = ⊥ ∨ H = ⊤ :=
  sorry

-- a nontrivial image of a simple group is simple
theorem IsSimpleGroup.isSimpleGroup_of_surjective {H : Type v} [Group H] [IsSimpleGroup G]
    [Nontrivial H] (f : G →* H) (hf : Function.Surjective f) : IsSimpleGroup H :=
  sorry

end My
