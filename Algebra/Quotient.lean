import Algebra.Coset

universe u

namespace Algebra

open Group Subgroup

variable {G : Type u} [Group G]

-- G / N: the type of left cosets of N (any subgroup; the group structure needs normality)
def QuotientGroup (N : Subgroup G) : Type u := Quotient (leftSetoid N)

namespace QuotientGroup

/-! ### Well-definedness: pure group algebra, the only place normality is used -/

-- paper proof (write it here first):
-- (ab)⁻¹(a'b') = b⁻¹ (a⁻¹a') b · b⁻¹b'  — conjugate of a⁻¹a' by b⁻¹, times b⁻¹b'
theorem mul_rel {N : Subgroup G} [N.Normal] {a a' b b' : G}
    (ha : a⁻¹ * a' ∈ N) (hb : b⁻¹ * b' ∈ N) : (a * b)⁻¹ * (a' * b') ∈ N := by
  have ha' := Normal.conj_mem'  (a⁻¹ * a')  ha b
  have h := N.mul_mem ha' hb
  simp only [mul_assoc] at h
  rw [inv_prod]
  simp only [mul_assoc]
  sorry

-- paper proof: (a⁻¹)⁻¹ a'⁻¹ = a a'⁻¹, and a'⁻¹a ∈ N (symmetry); use `Normal.mem_comm`
theorem inv_rel {N : Subgroup G} [N.Normal] {a a' : G}
    (ha : a⁻¹ * a' ∈ N) : a⁻¹⁻¹ * a'⁻¹ ∈ N :=
  sorry

/-! ### Cosets as elements: any subgroup, no normality needed -/

-- the class of a in G / N
def mk (N : Subgroup G) (a : G) : QuotientGroup N := Quotient.mk (leftSetoid N) a

-- when two elements give the same coset (core has `Quotient.sound` / `Quotient.exact`)
theorem mk_eq_mk_iff (N : Subgroup G) (a b : G) : mk N a = mk N b ↔ a⁻¹ * b ∈ N :=
  sorry

-- the quotient view agrees with the set view: equal in G / N ↔ equal as cosets
-- (rewrite with `mk_eq_mk_iff` and `leftCoset_eq_iff`)
theorem mk_eq_mk_iff_leftCoset_eq (N : Subgroup G) (a b : G) :
    mk N a = mk N b ↔ leftCoset a N = leftCoset b N :=
  sorry

-- every coset is the class of some element (`Quotient.ind` or `Quotient.exists_rep`)
theorem mk_surjective (N : Subgroup G) : Function.Surjective (mk N) :=
  sorry

/-! ### The operations -/

variable (N : Subgroup G) [N.Normal]

-- mk a * mk b := mk (a * b), via `Quotient.lift₂` and `mul_rel`
def qmul : QuotientGroup N → QuotientGroup N → QuotientGroup N :=
  sorry

-- (mk a)⁻¹ := mk a⁻¹, via `Quotient.lift` and `inv_rel`
def qinv : QuotientGroup N → QuotientGroup N :=
  sorry

-- each axiom: `Quotient.ind` down to representatives, then G's axiom
instance : Group (QuotientGroup N) where
  mul := qmul N
  one := mk N one
  inv := qinv N
  mul_assoc := sorry
  one_mul := sorry
  inv_mul_cancel := sorry

/-! ### Computation lemmas: the API boundary (should all be `rfl` once qmul/qinv exist) -/

theorem mk_mul (a b : G) : mk N a * mk N b = mk N (a * b) :=
  sorry

theorem mk_inv (a : G) : (mk N a)⁻¹ = mk N a⁻¹ :=
  sorry

theorem mk_one : (one : QuotientGroup N) = mk N one :=
  sorry

/-! ### The projection G → G / N -/

def mkHom : G →* QuotientGroup N :=
  sorry

theorem mkHom_apply (a : G) : mkHom N a = mk N a :=
  sorry

-- the kernel of the projection is N itself: every normal subgroup is a kernel
theorem ker_mkHom : Hom.ker (mkHom N) = N :=
  sorry

end QuotientGroup
end Algebra
