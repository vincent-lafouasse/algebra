import Base.Logic.Function
import Base.Data.Set

/-! # The Schröder–Bernstein theorem

Mathlib: `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean`.

Injections both ways give a bijection. Mathlib states it for embeddings and proves it with a
least fixed point on `Set α`; here it is stated for plain functions (Mathlib's exact statement
takes `Function.Injective` hypotheses too), and nothing beyond `Set`, `invFun` and `Nat`
recursion is needed.

Things to settle on the way:
- which subset of `α` gets sent by `f`, and which by "undo `g`";
- `invFun g : α → β` needs `[Nonempty β]`: where does it come from (and what if `α` is
  empty)?
- the case split "`x` is in the subset or not" is not decidable: `open Classical`. -/

universe u v

namespace My

open Classical in
theorem Function.Embedding.schroeder_bernstein {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (hf : _root_.Function.Injective f) (hg : _root_.Function.Injective g) :
    ∃ h : α → β, Function.Bijective h :=
  sorry

end My
