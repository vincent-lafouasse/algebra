import Algebra.Group.Commute
import Algebra.Data.Int

/-! # Powers

Mathlib: `Mathlib/Algebra/Group/Defs.lean` (`npowRec`, `zpowRec`, `pow_succ`, …),
`Mathlib/Algebra/Group/Basic.lean`, `Mathlib/Algebra/Group/Commute/Defs.lean`.

`g ^ n` for `n : Nat` by recursion, `g ^ n * g` at each step (Mathlib's `npowRec`, which
makes `pow_succ` true by `rfl`). Then `g ^ k` for `k : Int` by cases (`zpowRec`):
`Int.ofNat n` (k ≥ 0) and `Int.negSucc n` (k = -(n+1)).

In Mathlib the power is a field of `Monoid` with `npowRec` as its default; here it is just
this definition. -/

universe u

namespace My

variable {G : Type u} [Group G]

/-! ### Natural powers -/

def npowRec : Nat → G → G
  | 0, _ => 1
  | n + 1, g => npowRec n g * g

instance : Pow G Nat :=
  ⟨fun g n => npowRec n g⟩

-- the two defining equations (`rfl`)
theorem pow_zero (g : G) : g ^ (0 : Nat) = 1 :=
  rfl

theorem pow_succ (g : G) (n : Nat) : g ^ (n + 1) = g ^ n * g :=
  rfl

theorem pow_one (g : G) : g ^ (1 : Nat) = g := by
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

theorem one_pow (n : Nat) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => exact pow_zero 1
  | succ n ih => rw [pow_succ, ih, mul_one]

theorem pow_add (g : G) (m n : Nat) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [← Nat.add_assoc]
    rw [pow_succ, pow_succ]
    rw [ih]
    rw [mul_assoc]

theorem pow_succ' (g : G) (n : Nat) : g ^ (n + 1) = g * g ^ n := by
  rw [Nat.add_comm]
  rw [pow_add]
  rw [pow_one]

theorem pow_two (g : G) : g ^ 2 = g * g := by
  rw [pow_succ]
  rw [pow_one]

theorem pow_three' (g : G) : g ^ 3 = g * g * g := by
  rw [pow_succ]
  rw [pow_two]

theorem pow_three (g : G) : g ^ 3 = g * (g * g) := by
  rw [← mul_assoc]
  rw [pow_three']

theorem pow_mul (g : G) (m n : Nat) : g ^ (m * n) = (g ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ n ih =>
    rw [Nat.left_distrib]
    rw [pow_add]
    rw [pow_succ]
    rw [ih]
    rw [Nat.mul_one]

theorem pow_mul' (g : G) (m n : Nat) : g ^ (m * n) = (g ^ n) ^ m := by
  rw [Nat.mul_comm]
  rw [pow_mul]

-- powers of the same element commute
theorem pow_mul_comm (g : G) (m n : Nat) : g ^ m * g ^ n = g ^ n * g ^ m := by
  rw [← pow_add]
  rw [Nat.add_comm]
  rw [pow_add]

theorem pow_right_comm (g : G) (m n : Nat) : (g ^ m) ^ n = (g ^ n) ^ m := by
  rw [← pow_mul]
  rw [Nat.mul_comm]
  rw [pow_mul]

theorem inv_pow (g : G) (n : Nat) : g⁻¹ ^ n = (g ^ n)⁻¹ := by
  induction n with
  | zero => rw [pow_zero, pow_zero, inv_one]
  | succ n ih =>
    rw [pow_succ, pow_succ']
    rw [ih]
    rw [mul_inv_rev]

/-! ### Commuting with powers -/

namespace Commute

variable {a b : G}

theorem pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n) b := by
  induction n with
  | zero =>
    rw [pow_zero]; exact one_left b
  | succ n ih =>
    rw [pow_succ]
    exact mul_left ih h

theorem pow_right (h : Commute a b) (n : Nat) : Commute a (b ^ n) :=
  pow_left h.symm n |> Commute.symm

theorem pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m) (b ^ n) :=
  pow_right (pow_left h m) n

theorem self_pow (g : G) (n : Nat) : Commute g (g ^ n) :=
  pow_right (Commute.refl g) n

-- (ab)^n = a^n b^n needs a and b to commute: false in general (try n = 2)
protected theorem mul_pow (h : Commute a b) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, one_mul]
  | succ n ih =>
    calc
      (a * b) ^ (n + 1)
      _ = (a * b) ^ n * (a * b) := by rw [pow_succ]
      _ = a ^ n * b ^ n * (a * b) := by rw [ih]
      _ = a ^ n * (b ^ n * a) * b := by simp only [mul_assoc]
      _ = a ^ n * (a * b ^ n) * b := by rw [← pow_right h n |> Commute.eq]
      _ = (a ^ n * a) * (b ^ n * b) := by simp only [mul_assoc]
      _ = a ^ (n + 1) * b ^ (n + 1) := by rw [← pow_succ, ← pow_succ]

end Commute

theorem mul_pow {G : Type u} [CommGroup G] (a b : G) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n :=
  Commute.mul_pow (Commute.all a b) n

/-! ### Integer powers -/

-- k ≥ 0: g ^ n; k = -(n+1): (g ^ (n+1))⁻¹
def zpowRec : Int → G → G
  | Int.ofNat n, g => g ^ n
  | Int.negSucc n, g => (g ^ (n + 1))⁻¹

instance : Pow G Int :=
  ⟨fun g k => zpowRec k g⟩

-- the defining equations (`rfl`)
theorem zpow_natCast (g : G) (n : Nat) : g ^ (n : Int) = g ^ n :=
  rfl

theorem zpow_negSucc (g : G) (n : Nat) : g ^ (Int.negSucc n) = (g ^ (n + 1))⁻¹ :=
  rfl

theorem zpow_zero (g : G) : g ^ (0 : Int) = 1 :=
  rfl

theorem zpow_one (g : G) : g ^ (1 : Int) = g := by
  rw [← Int.ofNat_one]
  rw [zpow_natCast g 1]
  rw [pow_one]

theorem zpow_two (g : G) : g ^ (2 : Int) = g * g := by
  rw [← Int.ofNat_two]
  rw [zpow_natCast]
  rw [pow_two]

theorem one_zpow (k : Int) : (1 : G) ^ k = 1 := by
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]
    rw [zpow_natCast]
    rw [one_pow n]
  | negSucc n =>
    rw [zpow_negSucc]
    rw [inv_eq_one]
    exact one_pow (n + 1)

-- split on k; `-(ofNat (n+1)) = negSucc n` is the Int fact you need
theorem zpow_neg (g : G) (k : Int) : g ^ (-k) = (g ^ k)⁻¹ := by
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]
    rw [zpow_natCast]
    cases n with
    | zero =>
      rw [Int.neg_ofNat_zero]
      rw [zpow_zero]
      rw [pow_zero]
      exact Eq.symm inv_one
    | succ
      n =>
      conv =>
        lhs; rw [Nat.add_one]
      rw [Int.neg_ofNat_succ]
      rw [zpow_negSucc]
  | negSucc n =>
    rw [Int.neg_negSucc]
    rw [zpow_negSucc]
    rw [My.inv_inv]
    rw [zpow_natCast]

theorem zpow_neg_one (g : G) : g ^ (-1 : Int) = g⁻¹ := by
  rw [zpow_neg g 1]
  rw [zpow_one]

theorem inv_zpow (g : G) (k : Int) : g⁻¹ ^ k = (g ^ k)⁻¹ := by
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]
    rw [zpow_natCast]
    rw [zpow_natCast]
    exact inv_pow g n
  | negSucc n =>
    rw [zpow_negSucc]
    rw [zpow_negSucc]
    rw [inv_inj]
    rw [inv_pow]

-- stepping stones for `zpow_add`: one more / one less
theorem zpow_add_one (g : G) (k : Int) : g ^ (k + 1) = g ^ k * g := by
  match k with
  | .ofNat n =>
    rw [Int.ofNat_eq_natCast]
    rw [zpow_natCast]
    rw [← Int.natCast_add_one]
    rw [zpow_natCast]
    exact pow_succ g n
  | .negSucc 0 =>
    rw [zpow_negSucc]
    rw [Int.negSucc_zero_add_one]
    rw [zpow_zero]
    rw [Nat.zero_add]
    rw [pow_one]
    exact Eq.symm (inv_mul_cancel g)
  | .negSucc (n + 1) =>
    rw [Int.negSucc_succ_add_one]
    rw [zpow_negSucc]
    rw [zpow_negSucc]
    rw [pow_succ' g (n + 1)]
    conv =>
      rhs; rw [mul_inv_rev]
    rw [inv_mul_cancel_right]

theorem zpow_sub_one (g : G) (k : Int) : g ^ (k - 1) = g ^ k * g⁻¹ := by
  have h := zpow_add_one g (k - 1)
  rw [Int.sub_add_cancel] at h
  rw [h]
  rw [mul_inv_cancel_right]

-- the hard one: split on the sign of `l`, then induction on its size,
-- moving one factor at a time with the two lemmas above
theorem zpow_add (g : G) (k l : Int) : g ^ (k + l) = g ^ k * g ^ l := by
  induction l using Int.induction_on with
  | zero => rw [Int.add_zero, zpow_zero, mul_one]
  | succ n ih =>
    rw [← Int.add_assoc]
    rw [zpow_add_one]
    rw [ih]
    rw [zpow_add_one]
    rw [mul_assoc]
  | pred n ih =>
    rw [zpow_sub_one]
    rw [← Int.add_sub_assoc]
    rw [zpow_sub_one]
    rw [ih]
    simp only [mul_assoc]

-- `k - l` is `k + -l` (`Int.sub_eq_add_neg`), then the two laws above
theorem zpow_sub (g : G) (k l : Int) : g ^ (k - l) = g ^ k * (g ^ l)⁻¹ := by
  rw [Int.sub_eq_add_neg]
  rw [zpow_add]
  rw [zpow_neg]

theorem zpow_mul (g : G) (k l : Int) : g ^ (k * l) = (g ^ k) ^ l := by
  induction l using Int.induction_on with
  | zero => rw [Int.mul_zero, zpow_zero, zpow_zero]
  | succ n ih =>
    rw [Int.mul_add]
    rw [zpow_add_one]
    rw [Int.mul_one]
    rw [zpow_add]
    rw [ih]
  | pred n ih =>
    rw [Int.mul_sub]
    rw [Int.mul_one]
    rw [zpow_sub]
    rw [zpow_sub_one]
    rw [ih]

end My
