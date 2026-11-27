import Algebra.Group.End
import Base.Data.Set.Image

/-! # Conjugacy

Mathlib: `Mathlib/Algebra/Group/Conj.lean`.

`IsConj a b`: `b` is a conjugate `c * a * c⁻¹` of `a`. It is an equivalence relation, and its
classes are the conjugacy classes `ConjClasses G`, a quotient type, like `G ⧸ H`.

- `isConj_iff` is the way in and out of `IsConj`;
- `conjugatesOf a : Set G` is the class of `a` as a set, `ConjClasses.carrier` the same seen
  from the quotient;
- in a commutative group every class is a single element (`isConj_iff_eq`, `mkEquiv`).

The elementwise lemmas (`conj_mul`, `conj_inv`, `conj_injective`) are in
`Algebra/Group/Basic.lean`: this file imports `End.lean`, as Mathlib's does, and `Commute.lean`
needs them earlier. -/

universe u v

namespace My

variable {G : Type u} {H : Type v} [Group G] [Group H]

-- (not in Mathlib: there `∃ c : αˣ, SemiconjBy ↑c a b`, through units, so that it makes sense
-- in a monoid; `isConj_iff` is the same statement for groups)
def IsConj (a b : G) : Prop :=
  ∃ c : G, c * a * c⁻¹ = b

-- the interface: the only lemma that looks inside `IsConj`
theorem isConj_iff {a b : G} : IsConj a b ↔ ∃ c : G, c * a * c⁻¹ = b :=
  Iff.rfl

/-! ### Conjugation as a function (not in Mathlib)

`conj c a` is `c * a * c⁻¹`, as a plain function: a name for the expression, for reading.
Mathlib has none; it writes the product, or uses `MulAut.conj c`, the same map packaged as an
automorphism. Lemmas you `rw` with (`conj_mul`, `Normal.conj_mem`, …) stay about the
product, since that is what shows up in goals: `conj_apply` goes back and forth. -/

def conj (c a : G) : G :=
  c * a * c⁻¹

-- the interface: the only lemma that looks inside `conj`
theorem conj_apply (c a : G) : conj c a = c * a * c⁻¹ :=
  rfl

-- the packaged version is the same map
theorem MulAut.conj_apply_eq_conj (c a : G) : MulAut.conj c a = conj c a :=
  rfl

theorem isConj_iff_conj {a b : G} : IsConj a b ↔ ∃ c : G, conj c a = b :=
  Iff.rfl

/-! ### An equivalence relation -/

theorem IsConj.refl (a : G) : IsConj a a := by
  refine ⟨1, ?_⟩
  rw [inv_one]
  rw [mul_one, one_mul]

theorem IsConj.symm {a b : G} : IsConj a b → IsConj b a := by
  intro h
  obtain ⟨x, hx⟩ := isConj_iff_conj.mp h
  rw [conj_apply] at hx
  replace hx := eq_mul_inv_of_mul_eq hx
  replace hx := eq_inv_mul_of_mul_eq hx
  rw [← mul_assoc] at hx
  exact ⟨x⁻¹, Eq.symm hx⟩

theorem isConj_comm {g h : G} : IsConj g h ↔ IsConj h g :=
  Iff.intro IsConj.symm IsConj.symm

theorem IsConj.trans {a b c : G} : IsConj a b → IsConj b c → IsConj a c := by
  intro ⟨x, hab⟩ ⟨x', hbc⟩
  subst hab
  have h :=
    calc
      x' * (x * a * x⁻¹) * x'⁻¹
      _ = (x' * x) * a * (x⁻¹ * x'⁻¹) := by simp only [mul_assoc]
      _ = (x' * x) * a * (x' * x)⁻¹ := by rw [mul_inv_rev]
  rw [h] at hbc
  exact Exists.intro (x' * x) hbc

/-! ### Conjugates of special elements -/

-- `1` is conjugate only to itself
theorem isConj_one_right {a : G} : IsConj 1 a ↔ a = 1 :=
  sorry

theorem isConj_one_left {a : G} : IsConj a 1 ↔ a = 1 :=
  sorry

theorem IsConj.pow {a b : G} (n : Nat) : IsConj a b → IsConj (a ^ n) (b ^ n) :=
  sorry

theorem conj_pow {i : Nat} {a b : G} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ :=
  sorry

theorem conj_zpow {i : Int} {a b : G} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ :=
  sorry

-- in a commutative group, conjugate means equal
theorem isConj_iff_eq {G : Type u} [CommGroup G] {a b : G} : IsConj a b ↔ a = b :=
  sorry

-- a hom sends conjugates to conjugates
protected theorem MonoidHom.map_isConj (f : G →* H) {a b : G} : IsConj a b → IsConj (f a) (f b) :=
  sorry

/-! ### Conjugacy classes -/

/-- `IsConj` as a `Setoid`: the relation together with the proof that it is an equivalence. -/
protected def IsConj.setoid (G : Type u) [Group G] : Setoid G :=
  sorry

/-- The conjugacy classes of `G`: the quotient of `G` by `IsConj`. -/
def ConjClasses (G : Type u) [Group G] : Type u :=
  sorry

namespace ConjClasses

/-- The class of `a`. -/
protected def mk {G : Type u} [Group G] (a : G) : ConjClasses G :=
  sorry

-- the class of `1`
instance : One (ConjClasses G) :=
  sorry

theorem one_eq_mk_one : (1 : ConjClasses G) = ConjClasses.mk 1 :=
  sorry

-- two classes are equal exactly when the representatives are conjugate
theorem mk_eq_mk_iff_isConj {a b : G} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  sorry

-- to prove something for every class, prove it for every `mk a`
theorem forall_isConj {p : ConjClasses G → Prop} : (∀ q, p q) ↔ ∀ a, p (ConjClasses.mk a) :=
  sorry

theorem mk_surjective : Function.Surjective (@ConjClasses.mk G _) :=
  sorry

theorem exists_rep (q : ConjClasses G) : ∃ a : G, ConjClasses.mk a = q :=
  sorry

/-- A hom maps conjugacy classes to conjugacy classes: `MonoidHom.map_isConj` is what makes
this well defined. -/
def map (f : G →* H) : ConjClasses G → ConjClasses H :=
  sorry

theorem map_surjective {f : G →* H} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) :=
  sorry

-- in a commutative group, classes are elements
theorem mk_injective {G : Type u} [CommGroup G] : Function.Injective (@ConjClasses.mk G _) :=
  sorry

theorem mk_bijective {G : Type u} [CommGroup G] : Function.Bijective (@ConjClasses.mk G _) :=
  sorry

/-- The bijection between a commutative group and its conjugacy classes. -/
def mkEquiv {G : Type u} [CommGroup G] : G ≃ ConjClasses G :=
  sorry

end ConjClasses

/-! ### A class as a set -/

/-- The set of conjugates of `a`. -/
def conjugatesOf (a : G) : Set G :=
  sorry

theorem mem_conjugatesOf_self {a : G} : a ∈ conjugatesOf a :=
  sorry

theorem IsConj.conjugatesOf_eq {a b : G} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  sorry

theorem isConj_iff_conjugatesOf_eq {a b : G} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  sorry

namespace ConjClasses

/-- The set a class represents: `conjugatesOf` of any representative
(`IsConj.conjugatesOf_eq` is what makes this well defined). -/
def carrier : ConjClasses G → Set G :=
  sorry

theorem mem_carrier_mk {a : G} : a ∈ carrier (ConjClasses.mk a) :=
  sorry

theorem mem_carrier_iff_mk_eq {a : G} {q : ConjClasses G} : a ∈ carrier q ↔ ConjClasses.mk a = q :=
  sorry

theorem carrier_eq_preimage_mk {q : ConjClasses G} : q.carrier = ConjClasses.mk ⁻¹' {q} :=
  sorry

end ConjClasses

end My
