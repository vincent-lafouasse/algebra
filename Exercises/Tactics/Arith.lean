/-! # Arithmetic on `Nat`: computation, `omega`, induction

`rfl`, `decide`, `omega`, `nofun`, `injection`, `induction … with`, `induction … generalizing`,
`show`, strengthening an induction hypothesis. -/

namespace Exercises.Arith

/-! ## Closed computations and decision procedures -/

-- both sides compute to the same numeral: `rfl` (or `decide`)
theorem two_add_two : 2 + 2 = 4 :=
  sorry

-- `decide` evaluates a decidable statement; quantifiers bounded by `n < 10` are decidable
theorem no_square_two : ∀ n, n < 10 → n * n ≠ 2 :=
  sorry

-- `omega`: linear arithmetic over `Nat` and `Int`, hypotheses included
theorem omega_warmup (a b : Nat) (h : a + 3 ≤ b) : a < b ∧ b ≠ 0 :=
  sorry

-- `nofun`: no constructor pattern fits `n + 1 = 0` (`omega` works too)
theorem succ_ne_zero' (n : Nat) : n + 1 ≠ 0 :=
  sorry

-- `injection h`: constructors are injective
theorem succ_inj' {m n : Nat} (h : m + 1 = n + 1) : m = n :=
  sorry

/-! ## Induction -/

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

-- `induction n with | zero => _ | succ n ih => _`. The equations of `double` hold by `rfl`,
-- so `show` the unfolded goal, then `omega` with `ih` in context
theorem double_eq (n : Nat) : double n = 2 * n :=
  sorry

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

-- Gauss. `omega` can't multiply two variables: expand products with
-- `simp only [Nat.mul_add, Nat.add_mul] at *` first; it then treats `n * n` as an opaque atom
theorem gauss (n : Nat) : 2 * sumTo n = n * (n + 1) :=
  sorry

-- tail-recursive version with an accumulator
def sumAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

-- the recursive call changes `acc`, so the induction hypothesis must hold for every `acc`:
-- `induction n generalizing acc`
theorem sumAcc_eq (n acc : Nat) : sumAcc n acc = acc + sumTo n :=
  sorry

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- `fib (n + 2)` looks two steps back, plain induction only one. Strengthen the statement:
-- prove `∀ n, fib n ≤ 2 ^ n ∧ fib (n + 1) ≤ 2 ^ (n + 1)` first (with `have`), using `Nat.pow_succ`
theorem fib_le_pow (n : Nat) : fib n ≤ 2 ^ n :=
  sorry

/-! ## Definitions with an `∃` -/

def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- unfold by `obtain ⟨k, hk⟩ := ha`; prove with `exact ⟨witness, by omega⟩`
theorem even_add {a b : Nat} (ha : Even a) (hb : Even b) : Even (a + b) :=
  sorry

theorem not_even_one : ¬Even 1 :=
  sorry

-- induction, then `rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩`
theorem even_or_even_succ (n : Nat) : Even n ∨ Even (n + 1) :=
  sorry

end Exercises.Arith
