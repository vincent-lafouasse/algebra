# Roadmap

An index of what is in the library, what each piece needs, and where it leads.
Per-file proof counts live in `uv run scripts/check.py`; this file is about dependencies.

**Status:** ✓ proved · ◐ partly proved · ○ stubbed · · not in the repo yet

**Prerequisites:** ⇒ *hard*: the statement or the proof cannot be written without it.
→ *soft*: motivation, an analogy, or a shortcut; you can go without.

---

## The main line

| # | Milestone | Status | Where |
|---|---|---|---|
| 0 | Foundations: sets, functions, `Quot`, monoids and groups, homs, subgroups, cosets | ✓/◐ | `Base/`, `Algebra/Group/` |
| 1 | **Noether 1**: `G ⧸ ker f ≃* range f` | ○ | `QuotientGroup/Basic` |
| 2 | **Noether 2, 3**, correspondence theorem | ○ | `QuotientGroup/Basic` |
| 3 | **Lagrange**: the order of a subgroup divides the order of the group | · | needs a cardinality layer |
| 4 | Actions: orbit–stabilizer, Cayley | ○ | `GroupAction`, `ConjAct` |
| 5 | `Finset` and `∑` | · | `Base/Data/` |
| 6 | Class equation, Cauchy, p-groups, **Sylow** | · | |
| 7 | Permutations: cycles, **sign**, `Aₙ` simple for `n ≥ 5` | · | |
| 8 | Rings, ideals, quotient rings, CRT, PID/UFD | · | |
| 9 | Modules, bases, dimension, rank–nullity | · | |
| 10 | **Structure theorem over a PID**: finite abelian groups, Jordan form | · | |
| 11 | Polynomials, field extensions, **Galois**, Abel–Ruffini | · | |

### 1. Noether 1 — hard prerequisites

- ⇒ `Subgroup.Normal`: `Normal.conj_mem'`, `MonoidHom.normal_ker` (`Subgroup/Normal`) ○
- ⇒ `G ⧸ N` as a group: `QuotientGroup.mk`, `eq`, `induction_on`, the instance (`QuotientGroup/Defs`) ○
  - ⇒ `leftRel`, `leftRel_apply` (`Coset`) ✓
  - ⇒ `Quotient.map₂`, `Quotient.out` (`Base/Data/Quot`) ✓
  - ⇒ `Group.ofLeftAxioms` (`MinimalAxioms`) ✓
- ⇒ `rangeRestrict`, `ker`, `range` (`Subgroup/Ker`) ✓
- ⇒ `MulEquiv.ofBijective` (`Group/Equiv`) ✓
- → `Setoid.quotientKerEquivRange`, the same theorem for sets (`Base/Order/Setoid/Basic`) ○

### 2. Noether 2, 3, correspondence — hard prerequisites

- ⇒ everything in 1
- ⇒ Noether 2: `subgroupOf` (`Subgroup/Map`) ○, `normal_subgroupOf` (`Subgroup/Normal`) ○,
  `mem_sup_of_normal_right` (`Subgroup/Pointwise`) ○
  - ⇒ `closure_induction` (`Subgroup/Closure`) ○
- ⇒ Noether 3: `QuotientGroup.map`, `Normal.map` for surjective homs, `map`/`comap` (`Subgroup/Map`) ◐
- ⇒ correspondence: `comap`, `≃o`, `Set.Ici` (`Base/Order/Hom/Basic`) ○
- → the diamond isomorphism (`Base/Order/ModularLattice`) ○: Noether 2 read in the lattice of subgroups
- → `Subgroup.gc_map_comap` (`Subgroup/Map`) ○

### 3. Lagrange — hard prerequisites

- ⇒ a cardinality layer (·): "α has `n` elements" as `Nonempty (α ≃ Fin n)`, uniqueness of `n`
  (pigeonhole), sizes of products. Mathlib: `Nat.card`, built on `Cardinal` (too heavy).
- ⇒ `groupEquivQuotientProdSubgroup : G ≃ (G ⧸ H) × H` (·)
  - ⇒ `Quotient.out` ✓, `Equiv.mulLeft` (`Group/Units/Equiv`) ○
- Gives: `Subgroup.card_subgroup_dvd_card`, `index_mul_card`, `orderOf_dvd_card` (needs `zpowers` ○).

---

## Themes

### Quotients

```
Quot (core) ─┬─ Base/Data/Quot ✓ ── Setoid.ker ◐ ── leftRel ✓ ── G ⧸ N ○ ── Noether 1 ○
             │                                                      ├── Abelianization ○
             │                                                      ├── PresentedGroup ○
             │                                                      └── Solvable (quotients) ○
             └─ Base/Logic/Relation ○ (EqvGen, Quot.eq) ── FreeGroup ○ ── PresentedGroup ○
Setoid.ker ── DoubleCoset.setoid ○
```

- `Base/Logic/Relation`: ⇒ `Quot.lean` ✓. The proof of `Quot.eqvGen_exact` lifts into a second
  quotient. A good next step after `Quot.lean`.
- `FreeGroup/Basic`: ⇒ `Relation` (`ReflTransGen`, `Join`). `of_injective` ⇒ `church_rosser`, the
  hardest lemma in the file. `FreeGroup/Reduce` is the other route (unique reduced words).
- `PresentedGroup`: ⇒ `FreeGroup`, `normalClosure` (`Subgroup/Basic`), `QuotientGroup.lift`.
- `DoubleCoset`: ⇒ `Setoid.ker` ✓, `s * t` (`Group/Pointwise/Set`), `Disjoint` (`Base/Order/Disjoint`).

### Order

```
PartialOrder ─ Monotone ─ GaloisConnection ─┬─ GaloisInsertion ─ Subgroup.gi ○
     │                                       └─ ClosureOperator ○
     ├─ Lattice ─┬─ DistribLattice ─ BooleanAlgebra ─ Set α
     │           ├─ IsModularLattice ○ (diamond isomorphism)
     │           └─ CompleteLattice ─ Knaster–Tarski ○ (lfp, gfp)
     ├─ OrderHom (→o) ○, OrderIso (≃o), Icc, Ici
     └─ bounds, IsMax, Maximal ○ ─ IsChain ─ Zorn ○
```

- Everything here is ○: the Order layer is a stub skeleton, except `Monotone` (2/4).
- `ClosureOperator` ⇒ `OrderHom`, `GaloisConnection`.
- `FixedPoints` ⇒ `CompleteLattice` (instance stubs), `OrderHom`, bounds.
  → `Base/Logic/SchroederBernstein` (Mathlib proves Schröder–Bernstein with `lfp`).
- `Zorn` ⇒ bounds, `IsMax`, `Set.Pairwise`, `Classical.choice`. Needed later (hard) by: every vector
  space has a basis, Krull (maximal ideals exist), existence of algebraic closures.
- `ModularLattice` ⇒ `Lattice`, `Icc`, `≃o`.

### Constructions of groups

| Construction | File | Status | Hard prerequisites |
|---|---|---|---|
| `G × H` | `Group/Prod` | ○ | — |
| `∀ i, f i` | `Group/Pi` | ○ | — |
| `Gᵐᵒᵖ` | `Group/Opposite` | ○ | — |
| `Multiplicative α` | `Group/TypeTags/Basic` | ○ | — |
| `Perm α`, `MulAut G` | `Group/End` | ◐ | `Equiv`, `MulEquiv` |
| `N ⋊[φ] G` | `GroupTheory/SemidirectProduct` | ○ | `MulAut` (`End`), `MulAut.conj` |
| `G ⧸ N` | `QuotientGroup/` | ○ | see milestone 1 |
| `Gᵃᵇ` | `GroupTheory/Abelianization` | ○ | `commutator G`, `QuotientGroup.lift` |
| `FreeGroup α` | `GroupTheory/FreeGroup/` | ○ | `Relation` |
| `⟨α \| rels⟩` | `GroupTheory/PresentedGroup` | ○ | `FreeGroup`, `normalClosure` |
| dihedral, `ℤ/n` | · | · | ⇒ `ℤ/n` (as `ℤ ⧸ nℤ` or `Fin n`); → `⋊` or a presentation |

### Inside a group

| Topic | File | Status | Hard prerequisites |
|---|---|---|---|
| `closure`, `⊔`, complete lattice | `Subgroup/Closure` | ○ | — |
| `Subgroup.gi` | `Subgroup/Closure` | ○ | `GaloisInsertion`, `closure_le`, `closure_eq` |
| `Normal` | `Subgroup/Normal` | ○ | `MulAut.conj` for `normal_iff_map_conj_eq` |
| `normalClosure` | `Subgroup/Basic` | ○ | `closure`, `Normal` |
| `H * N`, `H ⊔ N` with `N` normal | `Subgroup/Pointwise` | ○ | `s * t`, `closure_induction`, `Normal` |
| center, centralizer | `GroupTheory/Center`, `Centralizer` | ○ | — |
| conjugacy classes | `Group/Conj` | ◐ | `MulAut.conj` |
| `⁅g, h⁆`, `⁅H, K⁆`, `G'` | `GroupTheory/Commutator` | ○ | `closure`, `Normal`, `map`, `centralizer`, `center` |
| simple groups | `GroupTheory/Simple` | ○ | `Normal`, `Nontrivial` |
| solvable groups | `GroupTheory/Solvable` | ○ | `⁅H, K⁆`, `map`, `G ⧸ N` (quotient instance), `Simple` |
| double cosets | `GroupTheory/DoubleCoset` | ○ | see Quotients |
| `Inn G`, `Out G` | `GroupTheory/Out` | ○ | `MulAut.conj`, `center`, Noether 1 |

### Actions

- `GroupAction` (○): `MulAction`, orbits, stabilizers, `orbitRel`, `toPerm`, Cayley.
  - ⇒ `Perm α` group (`End`), `Setoid` ✓. Orbit–stabilizer as a bijection ⇒ `G ⧸ stabilizer` (milestone 1).
  - Counting versions ⇒ the cardinality layer (milestone 3), and the class equation ⇒ `∑` (milestone 5).
- `ConjAct` (○): conjugation as an action. ⇒ `GroupAction`, `centralizer`.

---

## Decisions pending

- **`npow` as a field of `Monoid`** (Mathlib's design). Today `^` is the free `npowRec` for every
  monoid, and `pow_zero`/`pow_succ` are `rfl`. Needed (hard) once ℕ or ℤ become `My.Monoid`s:
  core already has `Pow Nat Nat` and `Pow Int Nat`, and a second `^` on them would not be the
  same term, so `rw` with the general lemmas would miss. Making it a field turns those two
  `rfl`s into the field axioms.
- **Units `Mˣ`** (Mathlib: `Algebra/Group/Units/Defs`): unblocked by `Monoid`, not stubbed yet.
  Needed (hard) by the sign `Perm α →* ℤˣ` (or use `Multiplicative`/`Bool`), `(ℤ/n)ˣ`, Euler.
- **`Nat` and `Int` as `My.Preorder`s.** Without them there's no `Monotone`/`Antitone` over `ℕ`
  (`derivedSeries_antitone` is stated by hand for now).
- **`to_additive`** (·): halves every additive copy: additive groups, ℤ-modules, ideals, `∑`.
  Needed in practice before rings. `/` and `div` lemmas wait for it.
- **Documentation generator** (·): a Lean metaprogram (`CoreM`, `ppExpr`, `findDocString?`,
  `collectAxioms`) or doc-gen4 in a side folder. `scripts/api.py` is the stopgap.

## Not yet in the repo, by milestone

- 3: `Fin n` cardinality, `Nat.card`-like counting, `Subgroup.index`, `orderOf`.
- 5: `List` lemmas, `Multiset` (a `Quot` of `List` by permutation), `Finset`, `∑`/`∏`.
- 6: `IsPGroup`, the class equation, Cauchy, Sylow I–III.
- 7: cycles, `Equiv.swap`, `Perm.sign`, `alternatingGroup`, `A₅` simple.
- 8–11: `Monoid` → `Ring`, `Ideal`, `ZMod`, `Polynomial`, `Module`, `Field`, `IntermediateField`,
  Galois correspondence, the fundamental theorem of algebra via Artin (needs ℝ: an ordered field
  where odd-degree polynomials have roots and positive elements have square roots).

---

*Maintenance:* every new stub file gets a row here (and in `README.md`'s layout table), with its
hard prerequisites. Statuses are coarse; `check.py` has the numbers.
