/-! # Sets

Mathlib: `Mathlib/Data/Set/Defs.lean`, `Mathlib/Data/Set/Basic.lean`.

A set of elements of `α` is a predicate on `α`: `Set α := α → Prop`. Membership `a ∈ s`
means `s a`, and `{x | p x}` is the set of those `x` with `p x`. Everything else is defined
through these two, so use the `mem_` lemmas rather than unfolding. -/

universe u

namespace My

def Set (α : Type u) : Type u := α → Prop

namespace Set

variable {α : Type u}

protected def Mem (s : Set α) (a : α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

def setOf (p : α → Prop) : Set α := p

/-- `{x | p x}` -/
syntax "{" ident " | " term "}" : term
/-- `{x : α | p x}` -/
syntax "{" ident " : " term " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident => $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t => $p)

-- the defining property of `{x | p x}` (an `=` of Props, so it `rw`s like an iff)
theorem mem_setOf_eq {a : α} {p : α → Prop} : (a ∈ {x | p x}) = p a :=
  rfl

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x
  have hx : s x ↔ t x := h x
  rw [hx]

instance : HasSubset (Set α) := ⟨fun s t => ∀ ⦃a⦄, a ∈ s → a ∈ t⟩

theorem subset_def {s t : Set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

-- `{a}`
instance : Singleton α (Set α) := ⟨fun a => {x | x = a}⟩

theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  let sb : Set α := {b}
  calc a ∈ sb
   _ ↔ sb a := Iff.rfl
   _ ↔ (a = b) := sorry

def univ : Set α := {_x | True}

theorem mem_univ (x : α) : x ∈ (univ : Set α) :=
  trivial

-- `∅`
instance : EmptyCollection (Set α) := ⟨{_x | False}⟩

theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  sorry

end Set
end My
