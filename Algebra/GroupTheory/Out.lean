import Algebra.GroupTheory.Center
import Algebra.GroupTheory.QuotientGroup.Basic

/-! # Inner and outer automorphisms

Mathlib: no named `Inn` / `Out`; it works with `MulAut.conj.range` directly (see
`Mathlib/Algebra/Group/End.lean` for `MulAut.conj`).

`Inn G` is the image of `MulAut.conj : G →* MulAut G`, the automorphisms `x ↦ g * x * g⁻¹`.
It is normal in `MulAut G`, so `Out G := MulAut G ⧸ Inn G` is a group. Since the kernel of
`conj` is the center (`MulAut.ker_conj`), the first isomorphism theorem gives
`G ⧸ center G ≃* Inn G`.

Hints for the normality proof (a thinking exercise):
- An element of `Inn G` is `conj g` for some `g`. Conjugating it by `φ : MulAut G` gives
  `φ * conj g * φ⁻¹`. What does that do to an element `x`? (Use `MulAut.mul_apply`.)
- The answer is again of the form `conj _`. Of which element?
- Two automorphisms that agree on every `x` are equal (`MulEquiv.ext`). -/

universe u

namespace My

variable (G : Type u) [Group G]

/-- The inner automorphisms of `G`: the image of `MulAut.conj` (not in Mathlib). -/
def Inn : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

variable {G}

-- the interface: read membership through this, not through `range` (not in Mathlib)
theorem mem_inn_iff {φ : MulAut G} : φ ∈ Inn G ↔ ∃ g : G, MulAut.conj g = φ :=
  sorry

theorem conj_mem_inn (g : G) : MulAut.conj g ∈ Inn G :=
  sorry

-- the thinking exercise: see the hints above (Mathlib states this for `MulAut.conj.range`)
instance : (Inn G).Normal :=
  sorry

variable (G)

/-- The outer automorphism group `Aut(G) / Inn(G)` (not in Mathlib). A `def`, like `MulAut`,
so its group structure is registered under this name only. -/
def Out : Type u :=
  MulAut G ⧸ Inn G

-- `Out G` is the quotient group, unfolded once (`inferInstanceAs` finds `Quotient.group`)
instance : Group (Out G) :=
  inferInstanceAs (Group (MulAut G ⧸ Inn G))

/-- `G ⧸ Z(G) ≃* Inn(G)` (not in Mathlib under this name). The first isomorphism theorem
applied to `MulAut.conj`, whose kernel is the center (`MulAut.ker_conj`). The two quotients
`G ⧸ ker conj` and `G ⧸ center G` are different types, so the equation has to be used to
move across: look up the `▸` notation. -/
noncomputable def quotientCenterEquivInn : G ⧸ Subgroup.center G ≃* Inn G :=
  sorry

end My
