/-! # The bracket notation `⁅x, y⁆`

Mathlib: `Mathlib/Algebra/Notation/Bracket.lean`.

One notation for every "commutator": `⁅g, h⁆ = g h g⁻¹ h⁻¹` in a group, `⁅H, K⁆` for two
subgroups, and later `⁅x, y⁆ = x y - y x` in a ring (the Lie bracket). Type it `\[-` and `\-]`. -/

universe u v

namespace My

class Bracket (L : Type u) (M : Type v) where
  bracket : L → M → M

notation "⁅" x ", " y "⁆" => Bracket.bracket x y

end My
