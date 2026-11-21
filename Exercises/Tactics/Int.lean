/-! # Warm-up on core's `Int`

`Int` has two constructors, `Int.ofNat n` (`n`) and `Int.negSucc n` (`-(n + 1)`).
Tactics: `rfl`/`decide` on closed terms, `cases k with | ofNat n | negSucc n`, a second `cases`
on the `Nat` inside, `nofun`/`injection` on constructors, and rewriting between `Int.ofNat n`
and `↑n` (`Int.ofNat_eq_natCast`).

Each statement here is already in core under the name in the comment: prove it without that
lemma (the primed name avoids the clash). -/

namespace Exercises.Int

/-! ## Computing -/

-- closed terms compute: `rfl` or `decide`
theorem negSucc_two : Int.negSucc 2 = -3 :=
  rfl

theorem neg_three_add_five : (-3 : Int) + 5 = 2 :=
  rfl

-- with a variable, `rfl` still works when the computation does not get stuck on `n`
theorem ofNat_add_one (n : Nat) : Int.ofNat n + 1 = Int.ofNat (n + 1) :=
  sorry

/-! ## Constructors -/

-- core: `Int.negSucc_inj`. `injection` (or `cases h`)
theorem negSucc_inj' {m n : Nat} (h : Int.negSucc m = Int.negSucc n) : m = n :=
  sorry

-- different constructors are never equal: `nofun`, or `intro h; cases h`
theorem ofNat_ne_negSucc (m n : Nat) : Int.ofNat m ≠ Int.negSucc n :=
  sorry

/-! ## Case analysis -/

-- core: `Int.neg_neg`. `cases k`; one of the cases needs a second `cases` (why?)
theorem neg_neg' (k : Int) : - -k = k :=
  sorry

-- core: `Int.zero_add`. `rfl` fails in one case: which, and what `Nat` fact unsticks it?
theorem zero_add' (k : Int) : 0 + k = k :=
  sorry

-- core: `Int.eq_nat_or_neg`. a witness per case; for `negSucc n` the witness is `n + 1`
theorem eq_nat_or_neg' (k : Int) : ∃ n : Nat, k = ↑n ∨ k = -↑n :=
  sorry

/-! ## `Int.ofNat n` versus `↑n` -/

-- core: `Int.natCast_add` (special case). the same number written two ways
theorem natCast_succ (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 :=
  sorry

end Exercises.Int
