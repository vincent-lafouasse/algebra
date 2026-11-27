import Base.Order.CompleteLattice.Defs
import Base.Order.Hom.Basic
import Base.Order.Bounds.Defs

/-! # Fixed points of monotone maps (Knaster–Tarski)

Mathlib: `Mathlib/Order/FixedPoints.lean`, `Mathlib/Logic/Function/Defs.lean` (`IsFixedPt`),
`Mathlib/Dynamics/FixedPoints/Defs.lean` (`Function.fixedPoints`).

In a complete lattice, a monotone `f` has a least fixed point
`lfp f = sInf {a | f a ≤ a}` and a greatest one, `gfp f = sSup {a | a ≤ f a}`.

Mathlib's `Schröder–Bernstein` is a fixed point of a monotone map on `Set α` (`F.lfp` there).
Your `Base/Logic/SchroederBernstein.lean` goes through `Nat` recursion; this is the other road.

Mathlib bundles `lfp` itself as a monotone map, `(α →o α) →o α`; here it is a plain function on
`α →o α`. -/

universe u

namespace My

namespace Function

variable {α : Type u}

def IsFixedPt (f : α → α) (x : α) : Prop :=
  sorry

theorem isFixedPt_def {f : α → α} {x : α} : IsFixedPt f x ↔ f x = x :=
  sorry

def fixedPoints (f : α → α) : Set α :=
  sorry

theorem mem_fixedPoints {f : α → α} {x : α} : x ∈ fixedPoints f ↔ IsFixedPt f x :=
  sorry

end Function

namespace OrderHom

variable {α : Type u} [CompleteLattice α]

-- explicit `f`: with a `sorry` body, a `variable` would be dropped from the signature
def lfp (f : α →o α) : α :=
  sorry

def gfp (f : α →o α) : α :=
  sorry

variable (f : α →o α)

theorem lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a :=
  sorry

theorem lfp_le_fixed {a : α} (h : f a = a) : f.lfp ≤ a :=
  sorry

theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ f.lfp :=
  sorry

theorem map_lfp : f f.lfp = f.lfp :=
  sorry

theorem isFixedPt_lfp : Function.IsFixedPt f f.lfp :=
  sorry

theorem isLeast_lfp : IsLeast (Function.fixedPoints f) f.lfp :=
  sorry

theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ f.gfp :=
  sorry

theorem gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : f.gfp ≤ a :=
  sorry

theorem map_gfp : f f.gfp = f.gfp :=
  sorry

theorem isGreatest_gfp : IsGreatest (Function.fixedPoints f) f.gfp :=
  sorry

end OrderHom

end My
