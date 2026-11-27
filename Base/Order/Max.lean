import Base.Order.Defs.PartialOrder

/-! # Maximal and minimal elements

Mathlib: `Mathlib/Order/Max.lean` (`IsMax`, `IsTop`, …), `Mathlib/Order/Minimal.lean`
(`Maximal`, `Minimal`).

`IsMax a`: nothing is above `a` (Mathlib spells it `∀ ⦃b⦄, a ≤ b → b ≤ a`, without `<`).
`IsTop a`: `a` is above everything, which is stronger. Zorn gives the weak one: a maximal
ideal is `IsMax` among proper ideals, but there can be many.

`Maximal P x`: `x` is maximal among the elements satisfying `P`.

The `_def` lemmas are the interface (the definitions stay opaque). Some are not in Mathlib,
where these definitions unfold by `Iff.rfl`: here, `isMax_def`, `isTop_def`, `maximal_def`. -/

universe u

namespace My

variable {α : Type u} [Preorder α]

def IsMax (a : α) : Prop :=
  sorry

def IsMin (a : α) : Prop :=
  sorry

def IsTop (a : α) : Prop :=
  sorry

def IsBot (a : α) : Prop :=
  sorry

theorem isMax_def {a : α} : IsMax a ↔ ∀ ⦃b⦄, a ≤ b → b ≤ a :=
  sorry

theorem isTop_def {a : α} : IsTop a ↔ ∀ b, b ≤ a :=
  sorry

theorem IsTop.isMax {a : α} (h : IsTop a) : IsMax a :=
  sorry

def Maximal (P : α → Prop) (x : α) : Prop :=
  sorry

def Minimal (P : α → Prop) (x : α) : Prop :=
  sorry

theorem maximal_def {P : α → Prop} {x : α} : Maximal P x ↔ P x ∧ ∀ ⦃y⦄, P y → x ≤ y → y ≤ x :=
  sorry

end My
