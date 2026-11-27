import Base.Data.Quot

/-! # Closures of relations

Mathlib: `Mathlib/Logic/Relation.lean` (`ReflTransGen`, `EqvGen`, `Join`), `Mathlib/Data/Quot.lean`
(`Quot.eq`). Core v4.35 has none of these.

`EqvGen r` is the smallest equivalence relation containing `r`. It answers the question your
`Quot.lean` left open: `Quot r` works for *any* relation `r`, not just an equivalence, and
`Quot.mk r a = Quot.mk r b` holds exactly when `EqvGen r a b` (`Quot.eq`). The hard direction,
`eqvGen_exact`, lifts `Quot r` into a second quotient, by `EqvGen.setoid r`.

`ReflTransGen r` ("zero or more `r`-steps") is what the free group uses: a word reduces to another
by a chain of cancellations.

Mathlib defines `ReflTransGen` and `EqvGen` as `inductive` types, whose constructors are the
lemmas stubbed below (`ReflTransGen.refl`/`tail`, `EqvGen.rel`/`refl`/`symm`/`trans`). Here they
are opaque `def`s; if you make them inductive, the constructor stubs go away.

The `_def` lemmas are the interface (the definitions stay opaque). Some are not in Mathlib,
where these definitions unfold by `Iff.rfl`: here, `join_def`. -/

universe u

namespace My

namespace Relation

variable {α : Type u} {r : α → α → Prop} {a b c : α}

/-! ### Reflexive-transitive closure -/

def ReflTransGen (r : α → α → Prop) : α → α → Prop :=
  sorry

theorem ReflTransGen.refl : ReflTransGen r a a :=
  sorry

-- one more step at the end
theorem ReflTransGen.tail (hab : ReflTransGen r a b) (hbc : r b c) : ReflTransGen r a c :=
  sorry

theorem ReflTransGen.single (hab : r a b) : ReflTransGen r a b :=
  sorry

theorem ReflTransGen.trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) :
    ReflTransGen r a c :=
  sorry

/-! ### Equivalence closure -/

def EqvGen (r : α → α → Prop) : α → α → Prop :=
  sorry

theorem EqvGen.rel (x y : α) (h : r x y) : EqvGen r x y :=
  sorry

theorem EqvGen.refl (x : α) : EqvGen r x x :=
  sorry

theorem EqvGen.symm (x y : α) (h : EqvGen r x y) : EqvGen r y x :=
  sorry

theorem EqvGen.trans (x y z : α) (hxy : EqvGen r x y) (hyz : EqvGen r y z) : EqvGen r x z :=
  sorry

theorem EqvGen.equivalence (r : α → α → Prop) : Equivalence (EqvGen r) :=
  sorry

def EqvGen.setoid (r : α → α → Prop) : Setoid α :=
  sorry

-- (Mathlib states `r ≤ p` with the order on relations)
theorem EqvGen.mono {p : α → α → Prop} (hrp : ∀ x y, r x y → p x y) (h : EqvGen r a b) :
    EqvGen p a b :=
  sorry

-- closing an equivalence relation adds nothing; with `mono`: `EqvGen r` is the smallest one
theorem _root_.My.Equivalence.eqvGen_iff (h : Equivalence r) : EqvGen r a b ↔ r a b :=
  sorry

/-! ### Joinability -/

-- `a` and `b` both reach some common `c` (Church–Rosser, for the free group)
def Join (r : α → α → Prop) : α → α → Prop :=
  sorry

theorem join_def : Join r a b ↔ ∃ c, r a c ∧ r b c :=
  sorry

end Relation

/-! ### Quotients by an arbitrary relation -/

open Relation

theorem Quot.eqvGen_exact {α : Type u} {r : α → α → Prop} {a b : α}
    (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  sorry

theorem Quot.eqvGen_sound {α : Type u} {r : α → α → Prop} {a b : α} (H : EqvGen r a b) :
    Quot.mk r a = Quot.mk r b :=
  sorry

theorem Quot.eq {α : Type u} {r : α → α → Prop} {x y : α} :
    Quot.mk r x = Quot.mk r y ↔ EqvGen r x y :=
  sorry

end My
