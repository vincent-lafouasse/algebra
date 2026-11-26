import Algebra.Group.End
import Algebra.Group.Opposite
import Algebra.Group.Subgroup.Lattice
import Algebra.GroupTheory.QuotientGroup.Defs

/-! # Group actions, orbits, stabilizers

Mathlib: `Mathlib/Algebra/Group/Action/Defs.lean` (`MulAction`, `smul_smul`, …),
`Mathlib/GroupTheory/GroupAction/Defs.lean` (`orbit`, `stabilizer`, `orbitRel`),
`Mathlib/GroupTheory/GroupAction/Quotient.lean` (`orbitEquivQuotientStabilizer`).

An action of `G` on a type `α` is an operation `g • a : α` (core's `SMul`, typed `\bu`) with
`1 • a = a` and `(g * h) • a = g • (h • a)`. Mathlib asks only for a monoid; here `G` is a
group, so every `g • ·` is a bijection (`inv_smul_smul`).

- `orbit G a` is where `a` can be moved: `{g • a | g : G}`.
- `stabilizer G a` is what fixes `a`: a subgroup of `G`.
- `orbitRel G α` is "same orbit", an equivalence relation: the orbits partition `α`.

Orbit–stabilizer, as a bijection: `orbit G a ≃ G ⧸ stabilizer G a`. No finiteness is needed;
counting (`|orbit| * |stabilizer| = |G|`) comes later, with finite sets.

Hints for orbit–stabilizer (a thinking exercise):
- Which map `G ⧸ stabilizer G a → orbit G a` is the obvious candidate? Define it on
  representatives first.
- When do `g • a` and `h • a` coincide? Compare your answer with `QuotientGroup.eq`.
- That one fact gives both "well defined" and "injective". Surjective is `mem_orbit_iff`.

Conjugation (`g • x = g * x * g⁻¹`, orbits are conjugacy classes, stabilizers are
centralizers) is also an action of `G` on `G`, which clashes with left multiplication below.
Mathlib separates them with a type synonym, `ConjAct G`: for later. -/

universe u v

namespace My

class MulAction (G : Type u) (α : Type v) [Group G] extends SMul G α where
  protected one_smul : ∀ a : α, (1 : G) • a = a
  protected mul_smul : ∀ (g h : G) (a : α), (g * h) • a = g • h • a

section

variable {G : Type u} {α : Type v} [Group G] [MulAction G α]

-- the axioms, as theorems outside the `MulAction` namespace (as in Mathlib)
-- `G` explicit (as in Mathlib): `one_smul G a`, since nothing in `a` tells Lean which group
variable (G) in
theorem one_smul (a : α) : (1 : G) • a = a :=
  sorry

theorem mul_smul (g h : G) (a : α) : (g * h) • a = g • h • a :=
  sorry

-- `mul_smul` read backwards, the direction you usually rewrite in
theorem smul_smul (g h : G) (a : α) : g • h • a = (g * h) • a :=
  sorry

theorem inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a :=
  sorry

theorem smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a :=
  sorry

-- `g • ·` is injective
theorem smul_left_cancel_iff (g : G) {a b : α} : g • a = g • b ↔ a = b :=
  sorry

theorem inv_smul_eq_iff {g : G} {a b : α} : g⁻¹ • a = b ↔ a = g • b :=
  sorry

end

namespace MulAction

variable (G : Type u) {α : Type v} [Group G] [MulAction G α]

/-! ### Orbits -/

def orbit (a : α) : Set α :=
  {b | ∃ g : G, g • a = b}

variable {G}

theorem mem_orbit_iff {a b : α} : b ∈ orbit G a ↔ ∃ g : G, g • a = b :=
  sorry

theorem mem_orbit (a : α) (g : G) : g • a ∈ orbit G a :=
  sorry

theorem mem_orbit_self (a : α) : a ∈ orbit G a :=
  sorry

-- two orbits that meet are equal
theorem orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔ a ∈ orbit G b :=
  sorry

/-! ### Being in the same orbit -/

variable (G α)

-- `a ~ b` when `a ∈ orbit G b`: reflexive by `one_smul`, symmetric by `⁻¹`, transitive by `*`
def orbitRel : Setoid α where
  r a b := sorry
  iseqv := sorry

variable {G α}

-- theorem orbitRel_apply {a b : α} : (orbitRel G α).r a b ↔ a ∈ orbit G b :=
-- sorry

/-! ### Stabilizers -/

variable (G)

def stabilizer (a : α) : Subgroup G where
  carrier := sorry
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

variable {G}

theorem mem_stabilizer_iff {a : α} {g : G} : g ∈ stabilizer G a ↔ g • a = a :=
  sorry

variable (G α) in
/-- The points that every element fixes (Mathlib: `MulAction.fixedPoints`). For conjugation
these are the central elements (`ConjAct.fixedPoints_eq_center`). -/
def fixedPoints : Set α :=
  {a | ∀ g : G, g • a = a}

theorem mem_fixedPoints {a : α} : a ∈ fixedPoints G α ↔ ∀ g : G, g • a = a :=
  sorry

/-! ### Orbit–stabilizer

The orbit is a set, so its type is the subtype `{b // b ∈ orbit G a}` (Mathlib writes
`orbit G a`, coerced to a type). See the hints at the top. -/

variable (G)

noncomputable def orbitEquivQuotientStabilizer (a : α) :
    { b // b ∈ orbit G a } ≃ G ⧸ stabilizer G a :=
  sorry

end MulAction

/-! ### Each `g` as a permutation; Cayley's theorem

Mathlib: `Mathlib/Algebra/Group/Action/Basic.lean` (`toPerm`), `…/Action/End.lean`
(`toPermHom`), `…/Action/Faithful.lean` (`FaithfulSMul`), `Mathlib/GroupTheory/Perm/Subgroup.lean`
(`subgroupOfMulAction`).

`g • ·` is a bijection of `α` (inverse `g⁻¹ • ·`): `toPerm g`. The axioms `one_smul`, `mul_smul`
say exactly that `g ↦ toPerm g` is a hom `G →* Perm α`. It is injective when the action is
*faithful*: different elements act differently. Then `G` is isomorphic to its image, a group
of permutations: Cayley's theorem, for `G` acting on itself by left multiplication. -/

/-- Different elements act differently. -/
class FaithfulSMul (M : Type u) (α : Type v) [SMul M α] : Prop where
  eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂

namespace MulAction

variable {G : Type u} {α : Type v} [Group G] [MulAction G α]

/-- `g`, seen as a permutation of `α`. -/
def toPerm (g : G) : Equiv.Perm α where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv := sorry
  right_inv := sorry

theorem toPerm_injective [FaithfulSMul G α] :
    Function.Injective (MulAction.toPerm : G → Equiv.Perm α) :=
  sorry

variable (G α)

/-- `toPerm` as a hom: `one_smul` and `mul_smul`, read as equations of permutations. -/
def toPermHom : G →* Equiv.Perm α where
  toFun := MulAction.toPerm
  map_one' := sorry
  map_mul' := sorry

theorem coe_toPermHom : (MulAction.toPermHom G α : G → Equiv.Perm α) = MulAction.toPerm :=
  sorry

end MulAction

/-- **Cayley's theorem**, for any faithful action: `G` is isomorphic to a group of
permutations of `H`. With `H = G` acting on itself, the textbook statement. -/
noncomputable def Equiv.Perm.subgroupOfMulAction (G : Type u) (H : Type v) [Group G] [MulAction G H]
    [FaithfulSMul G H] : G ≃* (MulAction.toPermHom G H).range :=
  sorry

/-! ### Examples -/

section Examples

variable {G : Type u} [Group G]

-- `G` acts on itself by left multiplication (Mathlib: `Monoid.toMulAction`)
instance Group.toMulAction : MulAction G G where
  smul g x := sorry
  one_smul := sorry
  mul_smul := sorry

theorem smul_eq_mul (g x : G) : g • x = g * x :=
  sorry

-- the action on itself is faithful: compare at `1` (Mathlib: for any `MulOneClass`)
instance : FaithfulSMul G G :=
  sorry

/-! #### Right multiplication, as a left action of `Gᵐᵒᵖ`

(Mathlib: `Mul.toSMulMulOpposite` in `Mathlib/Algebra/Group/Action/Defs.lean`,
`Monoid.toOppositeMulAction` in `…/Action/Opposite.lean`.) `op a • b = b * a`. Through
`MulAction.toPermHom Gᵐᵒᵖ G`, right translation becomes a hom, which is what
`Equiv.mulRight_mul`'s reversed order was asking for. -/

instance Mul.toSMulMulOpposite : SMul Gᵐᵒᵖ G :=
  ⟨λ a b => b * a.unop⟩

theorem op_smul_eq_mul (a b : G) : MulOpposite.op a • b = b * a :=
  sorry

instance Monoid.toOppositeMulAction : MulAction Gᵐᵒᵖ G where
  one_smul := sorry
  mul_smul := sorry

-- one orbit, and nothing but `1` fixes anything (not in Mathlib in this form)
theorem MulAction.orbit_self_eq_univ (a : G) : MulAction.orbit G a = Set.univ :=
  sorry

-- (not in Mathlib in this form: `IsCancelSMul.stabilizer_eq_bot`)
theorem MulAction.stabilizer_self_eq_bot (a : G) : MulAction.stabilizer G a = ⊥ :=
  sorry

-- automorphisms act on `G` by evaluation (Mathlib: `MulAut.applyMulAction`)
instance MulAut.applyMulAction : MulAction (MulAut G) G where
  smul φ x := sorry
  one_smul := sorry
  mul_smul := sorry

theorem MulAut.smul_def (φ : MulAut G) (x : G) : φ • x = φ x :=
  sorry

-- a subgroup acts wherever `G` does, by restriction. With `G` acting on itself, the orbit of
-- `x` under `H` is the right coset `H x`.
instance Subgroup.mulAction {α : Type v} [MulAction G α] (H : Subgroup G) : MulAction H α where
  smul h a := sorry
  one_smul := sorry
  mul_smul := sorry

theorem Subgroup.smul_def {α : Type v} [MulAction G α] {H : Subgroup G} (h : H) (a : α) :
    h • a = h.val • a :=
  sorry

end Examples

end My
