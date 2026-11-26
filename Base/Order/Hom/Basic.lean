import Base.Order.Defs.PartialOrder
import Base.Logic.Equiv
import Base.Data.Set

/-! # Order isomorphisms, subtypes, intervals

Mathlib: `Mathlib/Order/Hom/Basic.lean` (`≃o`), `Mathlib/Order/Basic.lean` (`Subtype.le`),
`Mathlib/Order/Interval/Set/Defs.lean` (`Set.Ici`).

An order isomorphism `α ≃o β` is a bijection with `e a ≤ e b ↔ a ≤ b`. Mathlib defines it
as `RelIso (· ≤ ·) (· ≤ ·)`, a bijection preserving any relation; here it is its own
structure, extending `α ≃ β` (not in Mathlib), with Mathlib's field name `map_rel_iff'`.

A subtype `{x // p x}` gets the order of `α`, so a set of elements `↥(Set.Ici a)` (everything
above `a`) is ordered too. -/

universe u v

namespace My

/-! ### Order isomorphisms -/

structure OrderIso (α : Type u) (β : Type v) [LE α] [LE β] extends α ≃ β where
  map_rel_iff' : ∀ {a b : α}, toFun a ≤ toFun b ↔ a ≤ b

infixl:25 " ≃o " => OrderIso

namespace OrderIso

variable {α : Type u} {β : Type v} [LE α] [LE β]

instance : CoeFun (α ≃o β) (λ _ => α → β) :=
  sorry

theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  sorry

end OrderIso

/-! ### Subtypes inherit the order -/

instance Subtype.le {α : Type u} [LE α] {p : α → Prop} : LE (Subtype p) :=
  sorry

theorem Subtype.coe_le_coe {α : Type u} [LE α] {p : α → Prop} {x y : Subtype p} :
    x.val ≤ y.val ↔ x ≤ y :=
  sorry

/-! ### Everything above `a` -/

namespace Set

variable {α : Type u} [Preorder α]

def Ici (a : α) : Set α :=
  sorry

theorem mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x :=
  sorry

end Set

end My
