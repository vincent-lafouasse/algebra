/-! # Sets

Mathlib: `Mathlib/Data/Set/Defs.lean`, `Mathlib/Data/Set/Basic.lean`.

A set of elements of `α` is a predicate on `α`: `Set α := α → Prop`. Membership `a ∈ s`
means `s a`, and `{x | p x}` is the set of those `x` with `p x`. Everything else is defined
through these two, so use the `mem_` lemmas rather than unfolding.

Images and preimages are in `Base/Data/Set/Image.lean`, functions between sets (`MapsTo`,
`InjOn`, `BijOn`, …) in `Base/Data/Set/Function.lean`. -/

universe u

namespace My

def Set (α : Type u) : Type u :=
  α → Prop

namespace Set

variable {α : Type u}

protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

def setOf (p : α → Prop) : Set α :=
  p

/-- `{x | p x}` -/
syntax "{" ident " | " term "}" : term

/-- `{x : α | p x}` -/
syntax "{" ident " : " term " | " term "}" : term

macro_rules
  | `({$x:ident | $p}) => `(setOf fun $x:ident => $p)
  | `({$x:ident : $t | $p}) => `(setOf fun $x:ident : $t => $p)

-- the defining property of `{x | p x}` (an `=` of Props, so it `rw`s like an iff)
theorem mem_setOf_eq {a : α} {p : α → Prop} : (a ∈ {x | p x}) = p a :=
  rfl

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x
  apply propext
  exact h x

-- named, as in Mathlib, so that `⊆` has a definition of its own (`Subset.refl` etc. are about it)
protected def Subset (s₁ s₂ : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : HasSubset (Set α) :=
  ⟨Set.Subset⟩

theorem subset_def {s t : Set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

-- `{a}`
instance : Singleton α (Set α) :=
  ⟨fun a => {x | x = a}⟩

theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := by
  show a ∈ {x | x = b} ↔ a = b
  rfl

def univ : Set α :=
  {_x | True}

theorem mem_univ (x : α) : x ∈ (univ : Set α) :=
  trivial

-- `∅`
instance : EmptyCollection (Set α) :=
  ⟨{_x | False}⟩

theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False := by
  show x ∈ {_x | False} ↔ False
  rfl

/-! ### A set as a type

`↥s` is the subtype `{x // x ∈ s}`: an element is a value with a proof that it lies in `s`
(the same move as `↥H` for a subgroup). -/

-- (Mathlib: `Set.Elem`, with the same coercion)
def Elem (s : Set α) : Type u :=
  {x : α // x ∈ s}

instance : CoeSort (Set α) (Type u) :=
  ⟨Elem⟩

/-! ### `⊆` is a partial order

There is no dot notation on `h : s ⊆ t` (its head is `HasSubset.Subset`, not `Set`): write
`Subset.trans h h'`. -/

protected theorem Subset.refl (s : Set α) : s ⊆ s :=
  λ _ h => h

protected theorem Subset.trans {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u :=
  λ _ h => h |> hst |> htu

-- the way to prove two sets equal by double inclusion
protected theorem Subset.antisymm {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ s) : s = t := by
  apply ext
  intro x
  exact Iff.intro (λ h => hst h) (λ h => hts h)

theorem subset_univ (s : Set α) : s ⊆ univ :=
  λ _ _ => trivial

theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  λ _ h_in_empty => False.elim h_in_empty

/-! ### `∩`, `∪`, `\`

Core provides the notation classes `Inter`, `Union` and `SDiff`. -/

instance : Inter (Set α) :=
  ⟨fun s t => {x | x ∈ s ∧ x ∈ t}⟩

instance : Union (Set α) :=
  ⟨fun s t => {x | x ∈ s ∨ x ∈ t}⟩

instance : SDiff (Set α) :=
  ⟨fun s t => {x | x ∈ s ∧ x ∉ t}⟩

-- the interface: membership in `∩`, `∪`, `\`
theorem mem_inter_iff (x : α) (s t : Set α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl

theorem mem_union (x : α) (s t : Set α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl

theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

-- `s ∩ t` is the largest set inside both
theorem inter_subset_left {s t : Set α} : s ∩ t ⊆ s :=
  sorry

theorem inter_subset_right {s t : Set α} : s ∩ t ⊆ t :=
  sorry

theorem subset_inter {r s t : Set α} (hrs : r ⊆ s) (hrt : r ⊆ t) : r ⊆ s ∩ t :=
  sorry

-- `s ∪ t` is the smallest set containing both
theorem subset_union_left {s t : Set α} : s ⊆ s ∪ t :=
  sorry

theorem subset_union_right {s t : Set α} : t ⊆ s ∪ t :=
  sorry

theorem union_subset {r s t : Set α} (hsr : s ⊆ r) (htr : t ⊆ r) : s ∪ t ⊆ r :=
  sorry

theorem inter_comm (s t : Set α) : s ∩ t = t ∩ s :=
  sorry

theorem union_comm (s t : Set α) : s ∪ t = t ∪ s :=
  sorry

theorem diff_subset {s t : Set α} : s \ t ⊆ s :=
  sorry

end Set

end My
