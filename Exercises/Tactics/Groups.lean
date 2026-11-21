import Algebra

/-! # Groups: practising on the library

`simp only [mul_assoc, …]` (normalize brackets), `rw … at`, `calc`, `have`, `subst`,
`ext`, `obtain ⟨a, rfl⟩`, definitional unfolding (`apply hg` on `g (f a) = g (f b)`). -/

namespace Exercises.Groups

open My

variable {G : Type} [Group G]

-- `simp only [mul_assoc]` rewrites everywhere, as often as it can: brackets go to the right
theorem reassoc (a b c d : G) : (a * b) * (c * d) = a * (b * c) * d :=
  sorry

-- cancellation lemmas in a `simp only`; `simp?` would tell you which ones
theorem telescope (a b : G) : a * b * b⁻¹ * a⁻¹ = 1 :=
  sorry

-- conjugating twice is conjugating by the product
theorem conj_conj (g h x : G) : g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ :=
  sorry

-- equations have solutions…
theorem solve_left (a b : G) : ∃ x, a * x = b :=
  sorry

-- …and only one: `apply mul_left_cancel (a := a)` names the implicit argument
theorem solve_left_unique {a b x y : G} (hx : a * x = b) (hy : a * y = b) : x = y :=
  sorry

-- `a⁻¹ = a` exactly when `a` squares to one; `calc` for one direction
theorem inv_eq_self_iff (a : G) : a⁻¹ = a ↔ a * a = 1 :=
  sorry

-- if every element squares to one, the group is commutative: `have` the instances you need
-- (`h (a * b)`, `h a`, `h b`), turn them into statements about inverses, `rw … at`
theorem comm_of_sq_eq_one (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a :=
  sorry

-- `(ab)⁻¹ = a⁻¹b⁻¹` iff `a` and `b` commute: get in and out of `Commute` with `commute_iff_eq`
theorem inv_mul_iff_comm (a b : G) : (a * b)⁻¹ = a⁻¹ * b⁻¹ ↔ a * b = b * a :=
  sorry

-- if a commutes with b, it commutes with b⁻¹: `Commute.inv_right`
theorem comm_inv {a b : G} (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a :=
  sorry

/-! ## Subgroups -/

-- `Subgroup.ext`, then rewrite with `mem_*` lemmas, `constructor`
theorem inf_self (S : Subgroup G) : S ⊓ S = S :=
  sorry

-- `subst h` replaces `x` by `1` everywhere when `h : x = 1`
theorem inf_bot (S : Subgroup G) : S ⊓ ⊥ = ⊥ :=
  sorry

/-! ## Homomorphisms -/

variable {H K : Type} [Group H] [Group K]

-- the image of a commutative group is commutative: `obtain ⟨a, rfl⟩ := hx`, then `← map_mul`
theorem range_comm (f : G →* H) (hG : ∀ a b : G, a * b = b * a) {x y : H}
    (hx : x ∈ f.range) (hy : y ∈ f.range) : x * y = y * x :=
  sorry

-- `(g.comp f) a` *is* `g (f a)` by definition, so `apply hg` works on it directly
theorem comp_injective {f : G →* H} {g : H →* K}
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (g.comp f) :=
  sorry

-- a hom is trivial iff its kernel is everything
theorem trivial_iff_ker_top (f : G →* H) : (∀ x, f x = 1) ↔ f.ker = ⊤ :=
  sorry

end Exercises.Groups
