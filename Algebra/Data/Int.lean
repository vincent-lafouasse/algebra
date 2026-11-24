/-! # Integers

Mathlib: `Mathlib/Data/Int/Init.lean` (`Int.induction_on`).

`Int` is core's: two constructors, `Int.ofNat n` (that is `n`) and `Int.negSucc n` (that is
`-(n + 1)`), so `cases k` splits every integer into exactly one of the two.

Core already has the conversion facts; use them rather than unfolding `+` or `-` on `Int`:
- `Int.ofNat_eq_natCast : Int.ofNat n = ↑n` (after `cases`, goals say `Int.ofNat n`,
  lemmas say `↑n`)
- `Int.negSucc_eq : Int.negSucc n = -(↑n + 1)`
- `Int.neg_negSucc : -Int.negSucc n = ↑(n + 1)`
- `Int.neg_ofNat_succ : -↑(n.succ) = Int.negSucc n`
- `Int.negSucc_sub_one : Int.negSucc n - 1 = Int.negSucc (n + 1)`
- `Int.natCast_add : ↑(n + m) = ↑n + ↑m`
- `Int.add_neg_one : i + -1 = i - 1`

For a leftover arithmetic side goal, `omega` (core) decides linear facts over `Int` and `Nat`. -/

namespace My

namespace Int

/-- Induction on the integers, going up from `0` through `↑i + 1` and down through
`-↑i - 1`. Use it as `induction k using Int.induction_on with | zero | succ i ih | pred i ih`.
Prove it by `cases i`, then a `Nat` induction in each case. -/
theorem induction_on {motive : Int → Prop} (i : Int) (zero : motive 0)
    (succ : ∀ i : Nat, motive ↑i → motive (↑i + 1))
    (pred : ∀ i : Nat, motive (-↑i) → motive (-↑i - 1)) : motive i := by
  cases i with
  | ofNat n =>
    induction n with
    | zero => exact zero
    | succ n ih => exact succ n ih
  | negSucc n =>
    induction n with
    | zero => exact pred 0 zero
    | succ n ih => exact pred n.succ ih

-- one step up from a negative number (not in Mathlib; `Int.negSucc_sub_one` read backwards)
theorem negSucc_succ_add_one (n : Nat) : Int.negSucc (n + 1) + 1 = Int.negSucc n := by
  rw [← Int.negSucc_sub_one]
  rw [Int.sub_add_cancel]

-- one step up from `-1` (not in Mathlib)
theorem negSucc_zero_add_one : Int.negSucc 0 + 1 = 0 := by
  rw [Int.negSucc_eq]
  rw [Int.neg_add]
  rw [Int.neg_add_cancel_right]
  rw [Int.neg_ofNat_zero]

end Int

end My
