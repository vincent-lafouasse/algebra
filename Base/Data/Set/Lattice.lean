import Base.Order.CompleteLattice.Defs
import Base.Order.BooleanAlgebra.Defs

/-! # Sets form a complete lattice and a Boolean algebra

Mathlib: `Mathlib/Order/BooleanAlgebra/Set.lean` (`⊔` is `∪`, `⊓` is `∩`, complements),
`Mathlib/Data/Set/Lattice.lean` (unions and intersections of families).

`⊔`, `⊓`, `⊤`, `⊥` on sets are `∪`, `∩`, `univ`, `∅`: the `_eq_` lemmas below translate. A
family of sets `S : Set (Set α)` has a union `sSup S` (Mathlib: `⋃₀ S`, `Set.sUnion`) and an
intersection `sInf S` (`⋂₀ S`). With complements `sᶜ` it is also a Boolean algebra
(Mathlib: a complete Boolean algebra, both at once). -/

universe u

namespace My

namespace Set

variable {α : Type u}

instance : Max (Set α) :=
  ⟨(· ∪ ·)⟩

instance : Min (Set α) :=
  ⟨(· ∩ ·)⟩

instance : Top (Set α) :=
  ⟨univ⟩

instance : Bot (Set α) :=
  ⟨∅⟩

instance : SupSet (Set α) :=
  ⟨λ S => {x | ∃ s, s ∈ S ∧ x ∈ s}⟩

instance : InfSet (Set α) :=
  ⟨λ S => {x | ∀ s, s ∈ S → x ∈ s}⟩

theorem sup_eq_union {s t : Set α} : s ⊔ t = s ∪ t :=
  sorry

theorem inf_eq_inter {s t : Set α} : s ⊓ t = s ∩ t :=
  sorry

theorem top_eq_univ : (⊤ : Set α) = univ :=
  sorry

theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  sorry

-- (Mathlib: `Set.mem_sUnion` and `Set.mem_sInter`, for `⋃₀` and `⋂₀`)
theorem mem_sSup {S : Set (Set α)} {x : α} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s :=
  sorry

theorem mem_sInf {S : Set (Set α)} {x : α} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s :=
  sorry

instance : CompleteLattice (Set α) where
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  le_sSup := sorry
  sSup_le := sorry
  sInf_le := sorry
  le_sInf := sorry
  le_top := sorry
  bot_le := sorry

/-! ### Complements -/

instance : Compl (Set α) :=
  ⟨λ s => {x | x ∉ s}⟩

theorem compl_def (s : Set α) : sᶜ = {x | x ∉ s} :=
  sorry

-- the interface (Mathlib: `Mathlib/Data/Set/Operations.lean`)
theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s :=
  sorry

theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  sorry

theorem notMem_compl_iff {s : Set α} {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  sorry

theorem inter_compl_self (s : Set α) : s ∩ sᶜ = ∅ :=
  sorry

theorem compl_inter_self (s : Set α) : sᶜ ∩ s = ∅ :=
  sorry

theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  sorry

theorem compl_univ : (univ : Set α)ᶜ = ∅ :=
  sorry

-- De Morgan, for sets
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  sorry

theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  sorry

instance : BooleanAlgebra (Set α) where
  le_sup_inf := sorry
  inf_compl_le_bot := sorry
  top_le_sup_compl := sorry
  le_top := sorry
  bot_le := sorry
  sdiff_eq := sorry

end Set

end My
