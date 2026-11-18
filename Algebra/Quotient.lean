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
  simp only [mul_assoc, mul_inv_cancel_left] at h
  rw [inv_prod]
  simp only [mul_assoc]
  exact h

-- paper proof: (a⁻¹)⁻¹ a'⁻¹ = a a'⁻¹, and a'⁻¹a ∈ N (symmetry); use `Normal.mem_comm`
theorem inv_rel {N : Subgroup G} [N.Normal] {a a' : G}
    (ha : a⁻¹ * a' ∈ N) : a⁻¹⁻¹ * a'⁻¹ ∈ N := by
  have h :=
    calc a⁻¹⁻¹ * a'⁻¹
     _ = a * a'⁻¹ := by rw [inv_inv]
  rw [h]
  have ha' := Normal.mem_comm ha
  have ha'' := N.inv_mem ha'
  rw [inv_prod] at ha''
  rw [inv_inv] at ha''
  exact ha''

/-! ### Cosets as elements: any subgroup, no normality needed -/

-- the class of a in G / N
def mk (N : Subgroup G) (a : G) : QuotientGroup N := Quotient.mk (leftSetoid N) a

-- when two elements give the same coset (core has `Quotient.sound` / `Quotient.exact`)
theorem mk_eq_mk_iff (N : Subgroup G) (a b : G) : mk N a = mk N b ↔ a⁻¹ * b ∈ N := by
  constructor
  · intro h
    have e : leftRel N a b := Quotient.exact h
    rw [leftRel_iff] at e
    exact e
  · intro h
    rw [← leftRel_iff] at h
    exact Quotient.sound h

-- the quotient view agrees with the set view: equal in G / N ↔ equal as cosets
-- (rewrite with `mk_eq_mk_iff` and `leftCoset_eq_iff`)
theorem mk_eq_mk_iff_leftCoset_eq (N : Subgroup G) (a b : G) :
    mk N a = mk N b ↔ leftCoset a N = leftCoset b N := by
  rw [mk_eq_mk_iff]
  rw [leftCoset_eq_iff]

-- every coset is the class of some element (`Quotient.ind` or `Quotient.exists_rep`)
theorem mk_surjective (N : Subgroup G) : Function.Surjective (mk N) := by
  intro (b : QuotientGroup  N)
  obtain ⟨rep_b, hb⟩ := Quotient.exists_rep b
  refine ⟨rep_b, ?_⟩
  rw [← hb]
  rfl

/-! ### The operations -/

variable (N : Subgroup G) [N.Normal]

-- mk a * mk b := mk (a * b), via `Quotient.lift₂` and `mul_rel`
def qmul : QuotientGroup N → QuotientGroup N → QuotientGroup N :=
  Quotient.lift₂ (λ a b => mk N (a * b)) (by
    intro a b a' b' eq_a eq_b
    apply Quotient.sound
    exact mul_rel eq_a eq_b)

-- (mk a)⁻¹ := mk a⁻¹, via `Quotient.lift` and `inv_rel`
def qinv : QuotientGroup N → QuotientGroup N :=
  Quotient.lift (λ x => mk N x⁻¹) (by
    intro a b eq
    apply Quotient.sound
    exact inv_rel eq)

-- each axiom: `Quotient.ind` down to representatives, then G's axiom
instance : Group (QuotientGroup N) where
  mul := qmul N
  one := mk N one
  inv := qinv N
  mul_assoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    rename_i x y z
    show mk N (x * y * z) = mk N (x * (y * z))
    rw [mul_assoc]
  one_mul := by
    intro a
    induction a using Quotient.ind
    rename_i x
    show mk N (one * x) = mk N x
    rw [one_mul]
  inv_mul_cancel := by
    intro a
    induction a using Quotient.ind
    rename_i x
    show mk N (x⁻¹ * x) = mk N one
    rw [inv_mul_cancel]

/-! ### Computation lemmas: the API boundary (should all be `rfl` once qmul/qinv exist) -/

theorem mk_mul (a b : G) : mk N a * mk N b = mk N (a * b) :=
  rfl

theorem mk_inv (a : G) : (mk N a)⁻¹ = mk N a⁻¹ :=
  rfl

theorem mk_one : (one : QuotientGroup N) = mk N one :=
  rfl

/-! ### The projection G → G / N -/

def mkHom : G →* QuotientGroup N where
  toFun := λ x => mk N x
  map_mul := mk_mul N

theorem mkHom_apply (a : G) : mkHom N a = mk N a :=
  sorry

-- the kernel of the projection is N itself: every normal subgroup is a kernel
theorem ker_mkHom : Hom.ker (mkHom N) = N :=
  sorry

end QuotientGroup
end Algebra
