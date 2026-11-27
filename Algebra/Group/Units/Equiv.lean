import Algebra.Group.Equiv

/-! # Translations

Mathlib: `Mathlib/Algebra/Group/Units/Equiv.lean`.

Left translation `x ↦ a * x` is a permutation of `G`, with inverse `x ↦ a⁻¹ * x`: that is
`Equiv.mulLeft a`. It is *not* a hom (it sends `1` to `a`), so it lives in `Perm G`, not in
`MulAut G`. How translations compose (`mulLeft_mul`, …) needs the group `Perm G`, so it is in
`Algebra/Group/End.lean`. -/

universe u

namespace My

namespace Equiv

variable {G : Type u} [Group G]

/-- Left multiplication by `a`, as a permutation of `G`. -/
protected def mulLeft (a : G) : Perm G :=
  sorry

theorem coe_mulLeft (a : G) : ((Equiv.mulLeft a : Perm G) : G → G) = (a * ·) :=
  sorry

theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (a⁻¹ * ·) :=
  sorry

theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  sorry

/-- Right multiplication by `a`, as a permutation of `G`. -/
protected def mulRight (a : G) : Perm G :=
  sorry

theorem coe_mulRight (a : G) : ((Equiv.mulRight a : Perm G) : G → G) = (· * a) :=
  sorry

theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  sorry

theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = (· * a⁻¹) :=
  sorry

end Equiv

-- (Mathlib: `_root_.Group.mulLeft_bijective`, stated in the `Equiv` section)
theorem Group.mulLeft_bijective {G : Type u} [Group G] (a : G) : Function.Bijective (a * ·) :=
  sorry

theorem Group.mulRight_bijective {G : Type u} [Group G] (a : G) : Function.Bijective (· * a) :=
  sorry

end My
