# algebra

Group theory in Lean 4, from the axioms up, without Mathlib.

The `Group` class has five axioms (associativity, identity and inverse on both sides), but
three are enough: `Group.ofLeftAxioms` and `Group.ofRightAxioms` build a group from one side's
laws. Everything else is proved here. The library tracks Mathlib: names, statements, namespaces
and file layout follow Mathlib's, so that reading this code teaches you Mathlib. Each file's
header names the Mathlib files it mirrors. Where something has no Mathlib counterpart, a
comment says "(not in Mathlib)".

## Layout

What each file needs and where it leads: [ROADMAP.md](ROADMAP.md).

Two libraries. `Base` holds the foundations that are not algebra (functions, bijections,
sets, order) and imports nothing but core; `Algebra` is built on it. `Base` has its own
module prefix so that it can later move to its own repository without changing any import.

| File | Contents | Mathlib |
|---|---|---|
| `Base/Logic/Function.lean` | injective/surjective/bijective, `surjInv`, `invFun` | `Logic/Function/{Defs,Basic}` |
| `Base/Logic/Function/Conjugate.lean` | `Function.Semiconj`, `Function.Commute` | `Logic/Function/Conjugate` |
| `Base/Logic/Equiv.lean` | bijections `α ≃ β`, permutations `Equiv.Perm α` | `Logic/Equiv/Defs` |
| `Base/Logic/Nontrivial.lean` | `Nontrivial α`: two distinct elements | `Basic/Nontrivial/Defs` |
| `Base/Logic/Relation.lean` | `ReflTransGen`, `EqvGen`, `Join`; `Quot.eq` for any relation | `Logic/Relation`, `Data/Quot` |
| `Base/Logic/SchroederBernstein.lean` | injections both ways give a bijection | `SetTheory/Cardinal/SchroederBernstein` |
| `Base/Data/Set.lean` | `Set α`, `{x \| p x}`, `⊆` (= `≤`, a partial order), `{a}`, `univ`, `∅`, `∩ ∪ \`, `↥s`, `Set.Nonempty`, `Set.Pairwise` | `Data/Set/{Defs,Basic}` |
| `Base/Data/Set/Image.lean` | images `f '' s`, preimages `f ⁻¹' t`, `range f`, `Set.image_preimage` | `Data/Set/{Defs,Operations,Image,Lattice/Image}` |
| `Base/Data/Set/Function.lean` | `MapsTo`, `InjOn`, `SurjOn`, `BijOn`, `EqOn`, `InvOn`, `BijOn.equiv` | `Data/Set/Function` |
| `Base/Data/Set/Lattice.lean` | `Set α` as a complete lattice (`⊔ = ∪`, `sSup` = union of a family) and a Boolean algebra (`sᶜ`) | `Order/BooleanAlgebra/Set`, `Data/Set/Lattice` |
| `Base/Data/Int.lean` | `Int.induction_on`, `negSucc` stepping facts | `Data/Int/Init` |
| `Base/Data/Quot.lean` | `⟦a⟧`, `Quotient.eq`, `Quotient.map₂`, `Quotient.out` | `Data/Quot` |
| `Base/Order/Notation.lean` | `⊥`, `⊤`, `⊓`, `⊔`, `ᶜ` | `Order/Notation` |
| `Base/Order/Defs/PartialOrder.lean` | `Preorder`, `PartialOrder` | `Order/Defs/PartialOrder` |
| `Base/Order/Monotone/Defs.lean` | `Monotone`, `Antitone` | `Order/Monotone/Defs` |
| `Base/Order/GaloisConnection/Defs.lean` | `GaloisConnection l u`, `GaloisInsertion` | `Order/GaloisConnection/Defs` |
| `Base/Order/Hom/Basic.lean` | order isomorphisms `α ≃o β`, order homs `α →o β`, `Subtype.le`, `Set.Ici`, `Set.Icc` | `Order/Hom/Basic`, `Order/Basic`, `Order/Interval/Set/Defs` |
| `Base/Order/Max.lean` | `IsMax`, `IsTop`, `Maximal` | `Order/Max`, `Order/Minimal` |
| `Base/Order/Bounds/Defs.lean` | `upperBounds`, `BddAbove`, `IsLeast`, `IsLUB` and duals | `Order/Bounds/{Defs,Basic}` |
| `Base/Order/Disjoint.lean` | `Disjoint a b`, `Set.disjoint_left` | `Order/Disjoint`, `Data/Set/Disjoint` |
| `Base/Order/Closure.lean` | `ClosureOperator`, `GaloisConnection.closureOperator` | `Order/Closure` |
| `Base/Order/FixedPoints.lean` | Knaster–Tarski: `OrderHom.lfp`, `gfp` | `Order/FixedPoints`, `Logic/Function/Defs`, `Dynamics/FixedPoints/Defs` |
| `Base/Order/Zorn.lean` | `IsChain`, `zorn_le`, `zorn_subset` | `Order/Preorder/Chain`, `Order/Zorn` |
| `Base/Order/ModularLattice.lean` | `IsModularLattice`, the diamond isomorphism | `Order/ModularLattice` |
| `Base/Order/Lattice.lean` | `SemilatticeSup`, `SemilatticeInf`, `Lattice`, `DistribLattice` | `Order/Defs/Lattice` |
| `Base/Order/BooleanAlgebra/Defs.lean` | `BooleanAlgebra`: complements `xᶜ`, De Morgan | `Order/BooleanAlgebra/{Defs,Basic}`, `Order/Heyting/Basic` |
| `Base/Order/CompleteLattice/Defs.lean` | `sSup`, `sInf`, `CompleteLattice` | `Order/SetNotation`, `Order/CompleteLattice/Defs` |
| `Base/Order/Setoid/Basic.lean` | `Setoid.ker f`, the first isomorphism theorem for sets | `Order/Setoid/Basic` |
| `Algebra/Group/Defs.lean` | `Monoid`, `CommMonoid`, `Group`, `CommGroup` | `Algebra/Group/Defs` |
| `Algebra/Group/MinimalAxioms.lean` | `Group.ofLeftAxioms`, `Group.ofRightAxioms` | `Algebra/Group/MinimalAxioms` |
| `Algebra/Group/Basic.lean` | monoid rearrangements, then cancellation, inverses | `Algebra/Group/{Defs,Basic}` |
| `Algebra/Group/Commute.lean` | `Commute a b` | `Algebra/Group/Commute/{Defs,Basic}` |
| `Algebra/Group/Pow.lean` | `g ^ n` (Nat and Int) | `Algebra/Group/Defs`, `…/Basic` |
| `Algebra/Group/Hom.lean` | monoid homomorphisms `M →* N` (`map_inv`, `mk'` for groups) | `Algebra/Group/Hom/Defs` |
| `Algebra/Group/Equiv.lean` | isomorphisms `G ≃* H` | `Algebra/Group/Equiv/Defs` |
| `Algebra/Group/Prod.lean` | `G × H`, `fst`, `snd`, `inl`, `inr`, `MonoidHom.prod` | `Algebra/Notation/Prod`, `Algebra/Group/Prod` |
| `Algebra/Group/Opposite.lean` | the opposite group `Gᵐᵒᵖ` | `Algebra/Opposites`, `Algebra/Group/Opposite` |
| `Algebra/Group/TypeTags/Basic.lean` | `Multiplicative α`, the group `Multiplicative ℤ` | `Algebra/Group/TypeTags/Basic` |
| `Algebra/Group/Pi.lean` | products of families `∀ i, f i`, `Pi.evalMonoidHom`, `MonoidHom.pi` | `Algebra/Notation/Pi/Defs`, `Algebra/Group/Pi/{Basic,Hom}` |
| `Algebra/Group/Pointwise/Set.lean` | products of sets `s * t` | `Algebra/Group/Pointwise/Set/Basic` |
| `Algebra/Notation/Bracket.lean` | the notation `⁅x, y⁆` | `Algebra/Notation/Bracket` |
| `Algebra/Group/Units/Equiv.lean` | translations `Equiv.mulLeft`/`mulRight`, `Group.mulLeft_bijective` | `Algebra/Group/Units/Equiv` |
| `Algebra/Group/End.lean` | the group `Perm α`, how translations compose, `MulAut G`, `MulAut.conj` | `Algebra/Group/End` |
| `Algebra/Group/Conj.lean` | `IsConj`, `ConjClasses`, `conjugatesOf` | `Algebra/Group/Conj` |
| `Algebra/Group/Subgroup/` | `Subgroup`, `≤`, `⊥ ⊤ ⊓ ⊔`, `ker`, `range`, `map`, `comap`, `subgroupOf`, `zpowers`, `closure`, `Subgroup.gi`, `Normal`, `normalClosure`, `H * N` | `Algebra/Group/Subgroup/` |
| `Algebra/GroupTheory/Center.lean`, `Centralizer.lean` | `center G`, `centralizer s` | `GroupTheory/Subgroup/{Center,Centralizer}` |
| `Algebra/GroupTheory/Coset.lean` | `a • s`, translating sets, `leftRel` | `GroupTheory/Coset/{Defs,Basic}`, `Algebra/Group/Pointwise/Set/Basic` |
| `Algebra/GroupTheory/QuotientGroup/` | `G ⧸ N`, `lift`, `map`, the three isomorphism theorems, the correspondence theorem | `GroupTheory/QuotientGroup/{Defs,Basic}` |
| `Algebra/GroupTheory/Out.lean` | `Inn G`, `Out G`, `G ⧸ center G ≃* Inn G` | (not in Mathlib; uses `MulAut.conj.range`) |
| `Algebra/GroupTheory/GroupAction.lean` | `MulAction`, `orbit`, `stabilizer`, `orbitRel`, orbit–stabilizer, `toPerm`, Cayley | `Algebra/Group/Action/{Defs,Basic,End,Faithful}`, `GroupTheory/GroupAction/{Defs,Quotient}`, `GroupTheory/Perm/Subgroup` |
| `Algebra/GroupTheory/ConjAct.lean` | conjugation as an action: orbits = classes, stabilizers = centralizers | `GroupTheory/GroupAction/ConjAct` |
| `Algebra/GroupTheory/Commutator.lean` | `⁅g, h⁆`, `⁅H, K⁆`, the commutator subgroup `commutator G` | `Algebra/Group/Commutator`, `GroupTheory/Commutator/Basic` |
| `Algebra/GroupTheory/Abelianization.lean` | `Gᵃᵇ = G ⧸ G'` and its universal property | `GroupTheory/Abelianization/Defs` |
| `Algebra/GroupTheory/Simple.lean` | `IsSimpleGroup` | `GroupTheory/Subgroup/Simple` |
| `Algebra/GroupTheory/Solvable.lean` | `derivedSeries`, `IsSolvable`, closure under subgroups, quotients, extensions | `GroupTheory/Solvable` |
| `Algebra/GroupTheory/SemidirectProduct.lean` | `N ⋊[φ] G`, `inl`, `inr`, `rightHom`, `lift` | `GroupTheory/SemidirectProduct` |
| `Algebra/GroupTheory/DoubleCoset.lean` | `H a K`, `H \ G / K` | `GroupTheory/DoubleCoset` |
| `Algebra/GroupTheory/FreeGroup/` | `FreeGroup α`, reduction, `lift`, reduced words | `GroupTheory/FreeGroup/{Basic,Reduce}` |
| `Algebra/GroupTheory/PresentedGroup.lean` | `⟨α \| rels⟩`, `toGroup` | `GroupTheory/PresentedGroup` |
| `Algebra/GroupTheory/Examples.lean` | `PUnit`, `Bool` under xor, `ℤ ⧸ 2ℤ ≃* Bool` | (not in Mathlib) |
| `Exercises/` | exercise sheets, stated with the library above | |

## Building

```
lake build
```

Requires the toolchain in `lean-toolchain` (Lean 4.35.0). The library itself imports
nothing but core Lean; [Batteries](https://github.com/leanprover-community/batteries)
is a development dependency, used only for linting.

## Linting

```
scripts/lint.sh
```

runs the default Batteries environment linters on `Algebra` (unused arguments, unused
`have`s, `simp` lemmas in bad form, tautological statements, ill-typed instances, …) and
ignores missing docstrings. To configure:

- skip one declaration: `@[nolint unusedArguments]` (any linter name);
- inside a file (after `import Batteries.Tactic.Lint`): `#lint`, `#lint only unusedArguments`,
  `#list_linters`.

## Status

Restarted on 2026-11-21 with the Mathlib-shaped design: every proof is a `sorry` stub to
fill in. `lake build` lists them as warnings. The goal is
`QuotientGroup.quotientKerEquivRange`, the first isomorphism theorem.

Each `sorry` is an axiom, and anything that uses a `sorry`'d lemma inherits it,
while the build warning only marks the declaration where the `sorry` is written. To check
that no proof you consider finished leans on a stub:

```
uv run scripts/check.py                 # per-file progress; exits 1 and lists anything tainted
uv run scripts/check.py Algebra/Group   # only files under a path
uv run scripts/check.py -v              # also lists every stub
uv run scripts/check.py -a              # also lists what uses `Quot.sound` and choice
```

It also counts the axioms proved declarations rest on: Lean's three (`propext`, `Quot.sound`,
`Classical.choice`) are legitimate, and anything else is reported in red as non-standard.

It prints, per file, proved / total for theorems and for definitions (stubs and tainted ones
count in the total), with a ✓ on finished files. A declaration is *tainted* if it has no
`sorry` of its own but depends on one: a proof that looks finished but isn't.

The result is cached in `.lake/check-cache.tsv` under a hash of the sources, the toolchain
and the lakefile, so a run on an unchanged tree is instant.

For a single declaration, `#print axioms My.QuotientGroup.quotientKerEquivRange` in any file importing `Algebra`.

## References

The BibTeX entries are in [`references.bib`](references.bib).

[AdMKU] J. Avigad, L. de Moura, S. Kong, and S. Ullrich, *Theorem Proving in Lean 4*, available at <https://lean-lang.org/theorem_proving_in_lean4/>.

[AM] J. Avigad and P. Massot, *Mathematics in Lean*, available at <https://leanprover-community.github.io/mathematics_in_lean/>.

[Bou70] N. Bourbaki, *Algèbre : Chapitres 1 à 3*, Éléments de mathématique, Hermann, Paris, 1970.

[Cal84] J. Calais, *Éléments de théorie des groupes*, Presses Universitaires de France, Paris, 1984.

[Cay89] A. Cayley, “On the Theory of Groups”, *American Journal of Mathematics* **11** (1889), no. 2, 139–157, <https://doi.org/10.2307/2369415>.

[DF04] D. S. Dummit and R. M. Foote, *Abstract Algebra*, 3rd ed., John Wiley & Sons, Hoboken, NJ, 2004.

[dMU21] L. de Moura and S. Ullrich, “The Lean 4 Theorem Prover and Programming Language”, in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science **12699**, Springer, 2021, 625–635, <https://doi.org/10.1007/978-3-030-79876-5_37>.

[DMG+21] C. Deschamps, F. Moulin, Y. Gentric et al., *Maths MPSI-MP2I : Tout-en-un*, 6th ed., Dunod, Paris, 2021.

[Gal32] É. Galois, “Lettre à Auguste Chevalier” (29 May 1832), *Revue encyclopédique* **55** (1832), 568–576; reprinted in *Journal de mathématiques pures et appliquées* **11** (1846), 408–415.

[Gou09] X. Gourdon, *Les maths en tête : Algèbre*, 2nd ed., Ellipses, Paris, 2009.

[Jor70] C. Jordan, *Traité des substitutions et des équations algébriques*, Gauthier-Villars, Paris, 1870, <https://archive.org/details/traitdessubsti00jorduoft>.

[mC20] The mathlib Community, “The Lean Mathematical Library”, in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs* (CPP 2020), ACM, 2020, 367–381, <https://doi.org/10.1145/3372885.3373824>. The Lean 4 library this project tracks is at <https://github.com/leanprover-community/mathlib4>.

[Per96] D. Perrin, *Cours d'algèbre*, Ellipses, Paris, 1996.

[Tao22] T. Tao, *Analysis I*, 4th ed., Texts and Readings in Mathematics 37, Springer, Singapore, 2022.
