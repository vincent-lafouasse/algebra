import Base.Order.Lattice

/-! # Boolean algebras

Mathlib: `Mathlib/Order/BooleanAlgebra/Defs.lean` (the class),
`Mathlib/Order/BooleanAlgebra/Basic.lean` and `Mathlib/Order/Heyting/Basic.lean` (the lemmas).

A Boolean algebra is a distributive lattice with a top `⊤`, a bottom `⊥`, and a complement
`xᶜ`: `x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`. The model to keep in mind is `Set α`, with `∩`, `∪`,
`univ`, `∅` and set complement. Everything below (involution `xᶜᶜ = x`, De Morgan, …) follows
from the two complement laws and distributivity.

Mathlib's class also has an implication `x ⇨ y` (from Heyting algebras) and gives `\` and `⇨`
default definitions; here there is no `⇨`, and `sdiff_eq` is a plain field (not in Mathlib).
`le_top` and `bot_le` are fields of this class, not the general lemmas of
`CompleteLattice/Defs.lean`: unifying them needs Mathlib's `OrderTop`/`OrderBot`, for later. -/

universe u

namespace My

class BooleanAlgebra (α : Type u) extends DistribLattice α, Compl α, SDiff α, Top α, Bot α where
  protected inf_compl_le_bot : ∀ x : α, x ⊓ xᶜ ≤ ⊥
  protected top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ xᶜ
  protected le_top : ∀ a : α, a ≤ ⊤
  protected bot_le : ∀ a : α, ⊥ ≤ a
  protected sdiff_eq : ∀ x y : α, x \ y = x ⊓ yᶜ

variable {α : Type u} [BooleanAlgebra α] {x y : α}

/-! ### The complement laws -/

theorem inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
  sorry

theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
  sorry

theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
  sorry

theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ :=
  sorry

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
  sorry

theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  sorry

theorem compl_bot : (⊥ : α)ᶜ = ⊤ :=
  sorry

/-! ### Complement is an order-reversing involution -/

-- the key: a complement is unique (if `x ⊓ y = ⊥` and `x ⊔ y = ⊤`, then `y = xᶜ`)
theorem compl_compl (x : α) : xᶜᶜ = x :=
  sorry

theorem compl_injective : Function.Injective (compl : α → α) :=
  sorry

theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
  sorry

theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
  sorry

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
  sorry

/-! ### De Morgan -/

theorem compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ :=
  sorry

theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
  sorry

end My
