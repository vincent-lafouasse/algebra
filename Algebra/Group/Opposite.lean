import Algebra.Group.End

/-! # The opposite group `Gᵐᵒᵖ`

Mathlib: `Mathlib/Algebra/Opposites.lean` (the type, `op`, `unop`),
`Mathlib/Algebra/Group/Opposite.lean` (the group).

`Gᵐᵒᵖ` is a copy of `G` with the multiplication reversed: `op a * op b = op (b * a)`. It
explains the reversed order in `Equiv.mulRight_mul`: right translation is a hom *out of
`Gᵐᵒᵖ`*, and a right action of `G` is a left action of `Gᵐᵒᵖ`
(`Algebra/GroupTheory/GroupAction.lean`).

Mathlib defines `MulOpposite α` as a `def` over a one-field structure, with `op` and `unop`
as `def`s; here it is the structure itself, with constructor `op` and field `unop` (not in
Mathlib). `op` is a different type on purpose: Lean must not confuse `a * b` in `G` with
`op a * op b` in `Gᵐᵒᵖ`. -/

universe u

namespace My

structure MulOpposite (α : Type u) where op ::
  unop : α

postfix:max "ᵐᵒᵖ" => MulOpposite

namespace MulOpposite

variable {α : Type u}

theorem unop_op (x : α) : unop (op x) = x :=
  sorry

theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  sorry

theorem op_injective : Function.Injective (op : α → αᵐᵒᵖ) :=
  sorry

theorem unop_injective : Function.Injective (unop : αᵐᵒᵖ → α) :=
  sorry

theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  sorry

theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  sorry

/-- `op`, as a bijection. -/
def opEquiv : α ≃ αᵐᵒᵖ :=
  sorry

/-! ### The group structure: multiplication reversed -/

variable [Group α]

instance : Mul αᵐᵒᵖ :=
  sorry

instance : One αᵐᵒᵖ :=
  sorry

instance : Inv αᵐᵒᵖ :=
  sorry

instance instGroup : Group αᵐᵒᵖ :=
  sorry

theorem op_mul (x y : α) : op (x * y) = op y * op x :=
  sorry

theorem unop_mul (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x :=
  sorry

theorem op_one : op (1 : α) = 1 :=
  sorry

theorem unop_one : unop (1 : αᵐᵒᵖ) = 1 :=
  sorry

theorem op_inv (x : α) : op x⁻¹ = (op x)⁻¹ :=
  sorry

theorem unop_inv (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ :=
  sorry

end MulOpposite

end My
