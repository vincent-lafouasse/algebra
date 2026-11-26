import Base.Data.Quot
import Base.Data.Set.Image
import Base.Logic.Equiv

/-! # The kernel of a function, and the first isomorphism theorem for sets

Mathlib: `Mathlib/Order/Setoid/Basic.lean` (only the kernel part; that file also makes
`Setoid α` a complete lattice).

`Setoid.ker f` relates `x` and `y` when `f x = f y`. Its classes are the fibers of `f`, so the
quotient by it is "`α` with the points `f` can't tell apart glued together", and `f` becomes
injective on it (`kerLift`). Onto its range, that is a bijection:

    quotientKerEquivRange f : Quotient (Setoid.ker f) ≃ Set.range f

This is the first isomorphism theorem with the algebra taken out. The group version,
`QuotientGroup.quotientKerEquivRange`, is this plus two facts: the classes of `ker f` are the
cosets of the subgroup `f.ker`, and the bijection respects `*`. -/

universe u v

namespace My

namespace Setoid

variable {α : Type u} {β : Type v}

/-- The kernel of `f`: `x` and `y` are related when `f` can't tell them apart. -/
def ker (f : α → β) : Setoid α where
  r x y := f x = f y
  iseqv :=
    { refl := λ _ => rfl
      symm := Eq.symm
      trans := Eq.trans }

-- the interface: the only lemma that looks inside `ker`
theorem ker_def {f : α → β} {x y : α} : ker f x y ↔ f x = f y := by
  unfold ker
  rfl

-- the class of `y` is the fiber of `f` over `f y`
theorem ker_iff_mem_preimage {f : α → β} {x y : α} : ker f x y ↔ x ∈ f ⁻¹' {f y} := by
  rw [ker_def]
  rw [Set.mem_preimage]
  rw [Set.mem_singleton_iff]

theorem ker_apply_mk_out {f : α → β} (a : α) :
    f (Quotient.out (⟦a⟧ : Quotient (Setoid.ker f))) = f a :=
  Quotient.mk_out (s := Setoid.ker f) a |> ker_def.mp

/-! ### `f`, on the quotient by its kernel -/

theorem piecewise_constant (f : α → β) : ∀ (a b : α), ker f a b → f a = f b := by
  intro _ _
  rw [ker_def]
  exact id

/-- `f` on classes: well defined, since related elements have the same image by definition. -/
def kerLift (f : α → β) : Quotient (ker f) → β :=
  Quotient.lift f (piecewise_constant f)

theorem kerLift_mk (f : α → β) (x : α) : kerLift f ⟦x⟧ = f x :=
  rfl

-- the point of quotienting by the kernel
theorem kerLift_injective (f : α → β) : Function.Injective (kerLift f) := by
  intro q₁ q₂ he
  obtain ⟨x₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨x₂, rfl⟩ := Quotient.exists_rep q₂
  rw [kerLift_mk, kerLift_mk] at he
  rw [Quotient.sound]
  exact ker_def.mpr he

-- no need for AC because the reps don't leave the function. same with kerLift_injective
theorem range_kerLift_eq_range (f : α → β) : Set.range (kerLift f) = Set.range f := by
  apply Set.Subset.antisymm
  · intro y ⟨q, hx⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rw [kerLift_mk] at hx
    exact Exists.intro x hx
  · intro y ⟨x, hx⟩
    rw [← kerLift_mk f x] at hx
    exact ⟨⟦x⟧, hx⟩

/-! ### The first isomorphism theorem for sets -/

/-- The quotient by the kernel of `f` is in bijection with the range of `f`. -/
noncomputable def quotientKerEquivRange (f : α → β) : Quotient (ker f) ≃ Set.range f :=
  sorry

/-- With a right inverse `g` of `f` in hand, the inverse needs no choice. -/
def quotientKerEquivOfRightInverse (f : α → β) (g : β → α) (hf : Function.RightInverse g f) :
    Quotient (ker f) ≃ β :=
  sorry

/-- A surjective `f`: the quotient by its kernel is in bijection with all of `β`. -/
noncomputable def quotientKerEquivOfSurjective (f : α → β) (hf : Function.Surjective f) :
    Quotient (ker f) ≃ β :=
  sorry

end Setoid

end My
