import Base.Order.Defs.PartialOrder
import Base.Order.Monotone.Defs
import Base.Logic.Equiv
import Base.Data.Set

/-! # Order isomorphisms, subtypes, intervals

Mathlib: `Mathlib/Order/Hom/Basic.lean` (`≃o`), `Mathlib/Order/Basic.lean` (`Subtype.le`),
`Mathlib/Order/Interval/Set/Defs.lean` (`Set.Ici`, `Set.Icc`).

An order isomorphism `α ≃o β` is a bijection with `e a ≤ e b ↔ a ≤ b`. Mathlib defines it
as `RelIso (· ≤ ·) (· ≤ ·)`, a bijection preserving any relation; here it is its own
structure, extending `α ≃ β` (not in Mathlib), with Mathlib's field name `map_rel_iff'`.

A subtype `{x // p x}` gets the order of `α`, so a set of elements `↥(Set.Ici a)` (everything
above `a`) is ordered too.

An order hom `α →o β` is a monotone map, bundled with its proof (Mathlib's `OrderHom`). The
fixed-point theorems and closure operators take one. -/

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

/-! ### Monotone maps, bundled -/

structure OrderHom (α : Type u) (β : Type v) [Preorder α] [Preorder β] where
  toFun : α → β
  monotone' : Monotone toFun

infixr:25 " →o " => OrderHom

namespace OrderHom

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

instance : CoeFun (α →o β) (λ _ => α → β) :=
  sorry

theorem coe_mk (f : α → β) (hf : Monotone f) : ((⟨f, hf⟩ : α →o β) : α → β) = f :=
  sorry

protected theorem monotone (f : α →o β) : Monotone f :=
  sorry

theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  sorry

end OrderHom

/-! ### Everything above `a` -/

namespace Set

variable {α : Type u} [Preorder α]

def Ici (a : α) : Set α :=
  sorry

theorem mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x :=
  sorry

-- the closed interval `[a, b]`: the diamond isomorphism (`ModularLattice.lean`) is between two
def Icc (a b : α) : Set α :=
  sorry

theorem mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  sorry

end Set

end My
