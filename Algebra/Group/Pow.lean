import Algebra.Group.Commute

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

instance : Pow G Nat := ⟨fun g n => npowRec n g⟩

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
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, mul_one]

-- the other way round: needs induction (and `mul_assoc`)
theorem pow_succ' (g : G) (n : Nat) : g ^ (n + 1) = g * g ^ n := by
  induction n with
  | zero => rw [Nat.zero_add, pow_one, pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ]
    conv => lhs; rw [ih]
    rw [pow_succ]
    rw [mul_assoc]

theorem pow_two (g : G) : g ^ 2 = g * g := by
  rw [pow_succ]
  rw [pow_one]

theorem pow_three' (g : G) : g ^ 3 = g * g * g := by
  rw [pow_succ]
  rw [pow_two]

theorem pow_three (g : G) : g ^ 3 = g * (g * g) := by
  rw [← mul_assoc]
  rw [pow_three']

theorem pow_add (g : G) (m n : Nat) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [← Nat.add_assoc]
    rw [pow_succ, pow_succ]
    rw [ih]
    rw [mul_assoc]

theorem pow_mul (g : G) (m n : Nat) : g ^ (m * n) = (g ^ m) ^ n :=
  sorry

theorem pow_mul' (g : G) (m n : Nat) : g ^ (m * n) = (g ^ n) ^ m :=
  sorry

-- powers of the same element commute
theorem pow_mul_comm (g : G) (m n : Nat) : g ^ m * g ^ n = g ^ n * g ^ m :=
  sorry

theorem pow_right_comm (g : G) (m n : Nat) : (g ^ m) ^ n = (g ^ n) ^ m :=
  sorry

theorem inv_pow (g : G) (n : Nat) : g⁻¹ ^ n = (g ^ n)⁻¹ :=
  sorry

/-! ### Commuting with powers -/

namespace Commute

variable {a b : G}

theorem pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n) b :=
  sorry

theorem pow_right (h : Commute a b) (n : Nat) : Commute a (b ^ n) :=
  sorry

theorem pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m) (b ^ n) :=
  sorry

theorem self_pow (g : G) (n : Nat) : Commute g (g ^ n) :=
  sorry

-- (ab)^n = a^n b^n needs a and b to commute: false in general (try n = 2)
protected theorem mul_pow (h : Commute a b) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n :=
  sorry

end Commute

theorem mul_pow {G : Type u} [CommGroup G] (a b : G) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n :=
  sorry

/-! ### Integer powers -/

-- k ≥ 0: g ^ n; k = -(n+1): (g ^ (n+1))⁻¹
def zpowRec : Int → G → G
  | Int.ofNat n, g => g ^ n
  | Int.negSucc n, g => (g ^ (n + 1))⁻¹

instance : Pow G Int := ⟨fun g k => zpowRec k g⟩

-- the defining equations (`rfl`)
theorem zpow_natCast (g : G) (n : Nat) : g ^ (n : Int) = g ^ n :=
  sorry

theorem zpow_negSucc (g : G) (n : Nat) : g ^ (Int.negSucc n) = (g ^ (n + 1))⁻¹ :=
  sorry

theorem zpow_zero (g : G) : g ^ (0 : Int) = 1 :=
  sorry

theorem zpow_one (g : G) : g ^ (1 : Int) = g :=
  sorry

theorem zpow_two (g : G) : g ^ (2 : Int) = g * g :=
  sorry

theorem one_zpow (k : Int) : (1 : G) ^ k = 1 :=
  sorry

-- split on k; `-(ofNat (n+1)) = negSucc n` is the Int fact you need
theorem zpow_neg (g : G) (k : Int) : g ^ (-k) = (g ^ k)⁻¹ :=
  sorry

theorem zpow_neg_one (g : G) : g ^ (-1 : Int) = g⁻¹ :=
  sorry

theorem inv_zpow (g : G) (k : Int) : g⁻¹ ^ k = (g ^ k)⁻¹ :=
  sorry

-- stepping stones for `zpow_add`: one more / one less
theorem zpow_add_one (g : G) (k : Int) : g ^ (k + 1) = g ^ k * g :=
  sorry

theorem zpow_sub_one (g : G) (k : Int) : g ^ (k - 1) = g ^ k * g⁻¹ :=
  sorry

-- the hard one: split on the sign of `l`, then induction on its size,
-- moving one factor at a time with the two lemmas above
theorem zpow_add (g : G) (k l : Int) : g ^ (k + l) = g ^ k * g ^ l :=
  sorry

theorem zpow_mul (g : G) (k l : Int) : g ^ (k * l) = (g ^ k) ^ l :=
  sorry

end My
