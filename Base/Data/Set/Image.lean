import Base.Data.Set
import Base.Logic.Function

/-! # Images, preimages, ranges

Mathlib: `Mathlib/Data/Set/Defs.lean` and `Mathlib/Data/Set/Operations.lean` (the definitions),
`Mathlib/Data/Set/Image.lean` (the lemmas).

For `f : α → β`:
- `f '' s` is the image of `s : Set α`, the set of values `f x` with `x ∈ s`;
- `f ⁻¹' t` is the preimage of `t : Set β`, the set of `x` with `f x ∈ t`;
- `range f` is the image of everything.

Preimage is the well-behaved one: it commutes with `∩` and `∪` on the nose. Image commutes
with `∪` but only gets `⊆` for `∩`; equality needs `f` injective.

`image_subset_iff` is the key fact: `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`. Many of the others follow
from it. -/

universe u v w

namespace My

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

def image (f : α → β) (s : Set α) : Set β :=
  {b | ∃ a, a ∈ s ∧ f a = b}

def preimage (f : α → β) (t : Set β) : Set α :=
  {a | f a ∈ t}

def range (f : α → β) : Set β :=
  {b | ∃ a, f a = b}

/-- `f '' s`: the image of `s` under `f` -/
infixl:80 " '' " => image

/-- `f ⁻¹' t`: the preimage of `t` under `f` (typed `\-1'`) -/
infixl:80 " ⁻¹' " => preimage

/-! ### Membership: the interface -/

-- `∃ x ∈ s, P` is `∃ x, x ∈ s ∧ P`
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl

theorem mem_image_of_mem (f : α → β) {x : α} {s : Set α} (h : x ∈ s) : f x ∈ f '' s :=
  sorry

theorem mem_preimage {f : α → β} {t : Set β} {a : α} : a ∈ f ⁻¹' t ↔ f a ∈ t :=
  Iff.rfl

theorem mem_range {f : α → β} {y : β} : y ∈ range f ↔ ∃ x, f x = y :=
  Iff.rfl

theorem mem_range_self (f : α → β) (x : α) : f x ∈ range f :=
  sorry

/-! ### Monotonicity and the adjunction -/

-- (Mathlib may have renamed this `image_mono`)
theorem image_subset {s t : Set α} (f : α → β) (h : s ⊆ t) : f '' s ⊆ f '' t :=
  sorry

theorem preimage_mono {f : α → β} {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t :=
  sorry

-- the image is the smallest set whose preimage contains `s`
theorem image_subset_iff {f : α → β} {s : Set α} {t : Set β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  sorry

theorem image_preimage_subset (f : α → β) (t : Set β) : f '' (f ⁻¹' t) ⊆ t :=
  sorry

theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f '' s) :=
  sorry

-- the two inclusions above become equalities under the right hypothesis on `f`.
-- Find a counterexample to each without it.
theorem preimage_image_eq {f : α → β} (s : Set α) (hf : Function.Injective f) :
    f ⁻¹' (f '' s) = s :=
  sorry

theorem image_preimage_eq {f : α → β} (t : Set β) (hf : Function.Surjective f) :
    f '' (f ⁻¹' t) = t :=
  sorry

/-! ### Identity and composition -/

theorem image_id (s : Set α) : id '' s = s :=
  sorry

theorem image_comp (g : β → γ) (f : α → β) (s : Set α) : g ∘ f '' s = g '' (f '' s) :=
  sorry

theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  sorry

theorem preimage_comp {g : β → γ} {f : α → β} {u : Set γ} : g ∘ f ⁻¹' u = f ⁻¹' (g ⁻¹' u) :=
  sorry

/-! ### `∩`, `∪`, `∅`, `univ`, `{a}` -/

theorem preimage_inter {f : α → β} {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  sorry

theorem preimage_union {f : α → β} {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  sorry

theorem preimage_univ {f : α → β} : f ⁻¹' univ = univ :=
  sorry

theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t :=
  sorry

-- only `⊆`: two different points of `s` and `t` can have the same image
theorem image_inter_subset (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  sorry

theorem image_inter {f : α → β} {s t : Set α} (hf : Function.Injective f) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  sorry

theorem image_empty (f : α → β) : f '' ∅ = ∅ :=
  sorry

theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
  sorry

theorem image_univ {f : α → β} : f '' univ = range f :=
  sorry

-- (from memory: Mathlib's older name is `range_iff_surjective`)
theorem range_eq_univ {f : α → β} : range f = univ ↔ Function.Surjective f :=
  sorry

end Set

end My
