import Algebra.GroupTheory.Coset
import Algebra.Group.Pointwise.Set
import Base.Order.Setoid.Basic
import Base.Order.Disjoint
import Algebra.Group.Subgroup.Lattice

/-! # Double cosets `H \ G / K`

Mathlib: `Mathlib/GroupTheory/DoubleCoset.lean`.

The double coset of `a` is `H a K = {h * a * k | h ∈ H, k ∈ K}`. Like left cosets they
partition `G`: two double cosets are equal or disjoint. Mathlib's setoid is
`Setoid.ker (λ x => doubleCoset x H K)`, your `Base/Order/Setoid/Basic.lean` kernel: `x` and `y`
are related when they have the same double coset.

With `H = ⊥` they are the left cosets `a K`, and with `K = ⊥` the right cosets `H a`
(`bot_rel_eq_leftRel`, `rel_bot_eq_right_group_rel`). They are a counting tool for later:
Sylow's theorems and Mackey's formula split `G` into double cosets. -/

universe u

namespace My

namespace DoubleCoset

variable {G : Type u} [Group G] {α : Type u} [Mul α]

def doubleCoset (a : α) (s t : Set α) : Set α :=
  sorry

theorem mem_doubleCoset {s t : Set α} {a b : α} :
    b ∈ doubleCoset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y :=
  sorry

theorem mem_doubleCoset_self (H K : Subgroup G) (a : G) : a ∈ doubleCoset a H K :=
  sorry

theorem doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ doubleCoset a H K) :
    doubleCoset b H K = doubleCoset a H K :=
  sorry

theorem mem_doubleCoset_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) : b ∈ doubleCoset a H K :=
  sorry

-- equal or disjoint
theorem eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) :
    doubleCoset a H K = doubleCoset b H K :=
  sorry

/-! ### The quotient `H \ G / K` -/

def setoid (H K : Set G) : Setoid G :=
  sorry

def Quotient (H K : Set G) : Type u :=
  sorry

theorem rel_iff {H K : Subgroup G} {x y : G} :
    setoid ↑H ↑K x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b :=
  sorry

-- with `H = ⊥`: the left cosets of `K`
theorem bot_rel_eq_leftRel (H : Subgroup G) :
    (setoid ↑(⊥ : Subgroup G) ↑H).r = (QuotientGroup.leftRel H).r :=
  sorry

-- with `K = ⊥`: the right cosets of `H`
theorem rel_bot_eq_right_group_rel (H : Subgroup G) :
    (setoid ↑H ↑(⊥ : Subgroup G)).r = (QuotientGroup.rightRel H).r :=
  sorry

def mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K :=
  sorry

theorem eq {H K : Subgroup G} {a b : G} :
    mk H K a = mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k :=
  sorry

theorem mk_eq_of_doubleCoset_eq {H K : Subgroup G} {a b : G}
    (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H K b :=
  sorry

end DoubleCoset

end My
