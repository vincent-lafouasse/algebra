/-! # Order notation

Mathlib: `Mathlib/Order/Notation.lean`.

`⊥` and `⊤` (the smallest and largest element) and `⊓` (meet, here: intersection).
Core Lean has `LE` for `≤` and `Min` for `min`; `⊓` is notation for `min`. -/

universe u

namespace My

class Bot (α : Type u) where
  bot : α

class Top (α : Type u) where
  top : α

notation "⊥" => Bot.bot

notation "⊤" => Top.top

end My

infixl:69 " ⊓ " => Min.min
