# algebra

Group theory in Lean 4, from the axioms up, without Mathlib.

The `Group` class has three axioms (associativity, left identity, left inverse);
everything else is proved here. The library tracks Mathlib: names, statements, namespaces
and file layout follow Mathlib's, so that reading this code teaches you Mathlib. Each file's
header names the Mathlib files it mirrors. Where something has no Mathlib counterpart, a
comment says "(not in Mathlib)".

## Layout

| File | Contents | Mathlib |
|---|---|---|
| `Algebra/Logic/Function.lean` | injective/surjective/bijective, `surjInv`, `invFun` | `Logic/Function/{Defs,Basic}` |
| `Algebra/Logic/Equiv.lean` | bijections `α ≃ β` | `Logic/Equiv/Defs` |
| `Algebra/Data/Set.lean` | `Set α`, `{x \| p x}`, `⊆`, `{a}`, `univ` | `Data/Set/{Defs,Basic}` |
| `Algebra/Data/Int.lean` | `Int.induction_on`, `negSucc` stepping facts | `Data/Int/Init` |
| `Algebra/Order/Notation.lean` | `⊥`, `⊤`, `⊓` | `Order/Notation` |
| `Algebra/Group/Defs.lean` | `Group`, `CommGroup` | `Algebra/Group/Defs` |
| `Algebra/Group/Basic.lean` | cancellation, inverses | `Algebra/Group/{Defs,Basic}` |
| `Algebra/Group/Commute.lean` | `Commute a b` | `Algebra/Group/Commute/{Defs,Basic}` |
| `Algebra/Group/Pow.lean` | `g ^ n` (Nat and Int) | `Algebra/Group/Defs`, `…/Basic` |
| `Algebra/Group/Hom.lean` | homomorphisms `G →* H` | `Algebra/Group/Hom/Defs` |
| `Algebra/Group/Equiv.lean` | isomorphisms `G ≃* H` | `Algebra/Group/Equiv/Defs` |
| `Algebra/Group/End.lean` | `MulAut G`, `MulAut.conj` | `Algebra/Group/End` |
| `Algebra/Group/Subgroup/` | `Subgroup`, `≤`, `⊥ ⊤ ⊓`, `ker`, `range`, `map`, `comap`, `zpowers`, `Normal` | `Algebra/Group/Subgroup/` |
| `Algebra/GroupTheory/Center.lean`, `Centralizer.lean` | `center G`, `centralizer s` | `GroupTheory/Subgroup/{Center,Centralizer}` |
| `Algebra/GroupTheory/Coset.lean` | `a • s`, `leftRel` | `GroupTheory/Coset/{Defs,Basic}` |
| `Algebra/GroupTheory/QuotientGroup/` | `G ⧸ N`, `lift`, the first isomorphism theorem | `GroupTheory/QuotientGroup/{Defs,Basic}` |
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
scripts/axioms.sh        # exits 1 and lists any finished-looking declaration that depends on sorry
scripts/axioms.sh -v     # also lists every stub
```

It also prints a progress count, for example `theorems: 151 / 211 done (60 stubs, 0 tainted)`, and the same for definitions.

For a single declaration, `#print axioms My.QuotientGroup.quotientKerEquivRange` in any file importing `Algebra`.

## References

The BibTeX entries are in [`references.bib`](references.bib).

[AdMKU] J. Avigad, L. de Moura, S. Kong, and S. Ullrich, *Theorem Proving in Lean 4*, available at <https://lean-lang.org/theorem_proving_in_lean4/>.

[AM] J. Avigad and P. Massot, *Mathematics in Lean*, available at <https://leanprover-community.github.io/mathematics_in_lean/>.

[Bou70] N. Bourbaki, *Algèbre : Chapitres 1 à 3*, Éléments de mathématique, Hermann, Paris, 1970.

[Cal84] J. Calais, *Éléments de théorie des groupes*, Presses Universitaires de France, Paris, 1984.

[DF04] D. S. Dummit and R. M. Foote, *Abstract Algebra*, 3rd ed., John Wiley & Sons, Hoboken, NJ, 2004.

[DMG+21] C. Deschamps, F. Moulin, Y. Gentric et al., *Maths MPSI-MP2I : Tout-en-un*, 6th ed., Dunod, Paris, 2021.

[Gou09] X. Gourdon, *Les maths en tête : Algèbre*, 2nd ed., Ellipses, Paris, 2009.

[Per96] D. Perrin, *Cours d'algèbre*, Ellipses, Paris, 1996.
