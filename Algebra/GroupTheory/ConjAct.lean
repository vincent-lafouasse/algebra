import Algebra.GroupTheory.GroupAction
import Algebra.GroupTheory.Centralizer
import Algebra.Group.Conj

/-! # Conjugation as an action

Mathlib: `Mathlib/GroupTheory/GroupAction/ConjAct.lean`.

`G` acts on itself in two ways: left multiplication (`Group.toMulAction`) and conjugation,
`g • h = g * h * g⁻¹`. One type can carry only one `•`, so conjugation goes through a copy of
`G`: `ConjAct G`, the same group under another name. `toConjAct g` is `g` seen in the copy, and
`toConjAct g • h = g * h * g⁻¹`.

What the general action vocabulary means for conjugation:
- orbits are conjugacy classes (`orbit_eq_carrier_conjClasses`, `mem_orbit_conjAct`);
- stabilizers are centralizers (`stabilizer_eq_centralizer`);
- fixed points are the center (`fixedPoints_eq_center`).

So orbit–stabilizer for this action is the class equation's main ingredient: the class of `g`
is in bijection with `G ⧸ centralizer {g}`. -/

universe u

namespace My

def ConjAct (G : Type u) : Type u :=
  sorry

namespace ConjAct

open MulAction Subgroup
variable {G : Type u} [Group G]

-- the same group, under another name
instance : Group (ConjAct G) :=
  sorry

/-- An element of the copy, seen in `G`. -/
def ofConjAct : ConjAct G ≃* G :=
  sorry

/-- An element of `G`, seen in the copy. -/
def toConjAct : G ≃* ConjAct G :=
  sorry

theorem «forall» (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (toConjAct x) :=
  sorry

theorem toConjAct_ofConjAct (x : ConjAct G) : toConjAct (ofConjAct x) = x :=
  sorry

theorem ofConjAct_toConjAct (x : G) : ofConjAct (toConjAct x) = x :=
  sorry

theorem ofConjAct_one : ofConjAct (1 : ConjAct G) = 1 :=
  sorry

theorem toConjAct_one : toConjAct (1 : G) = 1 :=
  sorry

theorem ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹ :=
  sorry

theorem toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹ :=
  sorry

theorem ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  sorry

theorem toConjAct_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y :=
  sorry

/-! ### The action -/

instance : MulAction (ConjAct G) G :=
  sorry

theorem smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  sorry

theorem toConjAct_smul (g h : G) : toConjAct g • h = g * h * g⁻¹ :=
  sorry

theorem toConjAct_inv_smul (g h : G) : toConjAct g⁻¹ • h = g⁻¹ * h * g :=
  sorry

-- the action is `MulAut.conj`, element by element
theorem smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  sorry

/-! ### Orbits, stabilizers, fixed points -/

theorem fixedPoints_eq_center : fixedPoints (ConjAct G) G = (center G : Set G) :=
  sorry

theorem mem_orbit_conjAct {g h : G} : g ∈ orbit (ConjAct G) h ↔ IsConj g h :=
  sorry

-- Mathlib also has `orbitRel_conjAct : ⇑(orbitRel (ConjAct G) G) = IsConj` ("same orbit" is
-- "conjugate"). It is left out until `orbitRel`'s relation is filled in: with `r a b := sorry`
-- its statement doesn't mention `G`, so `orbitRel G α` doesn't typecheck yet.

theorem orbit_eq_carrier_conjClasses (g : G) : orbit (ConjAct G) g = (ConjClasses.mk g).carrier :=
  sorry

theorem stabilizer_eq_centralizer (g : G) : stabilizer (ConjAct G) g = centralizer {toConjAct g} :=
  sorry

end ConjAct

end My
