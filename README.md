# algebra

Group theory in Lean 4, from the axioms up, without Mathlib.

The `Group` class has three axioms (associativity, left identity, left inverse);
everything else is proved here. Names and design follow Mathlib where it makes
sense, so the code should feel familiar to Mathlib users.

## Layout

| File | Contents |
|---|---|
| `Algebra/Group.lean` | the `Group` class and basic lemmas (cancellation, inverses) |
| `Algebra/Hom.lean` | homomorphisms `G →* H`, composition, `ext` |
| `Algebra/Subgroup.lean` | subgroups, center, kernel, image, preimage |
| `Algebra/Normal.lean` | normal subgroups |
| `Algebra/Iso.lean` | isomorphisms `G ≃* H`, bijective homs |
| `Algebra/Aut.lean` | conjugation, the group `Aut(G)`, `ker (g ↦ conj g) = Z(G)` |
| `Algebra/Coset.lean` | left cosets as equivalence classes |
| `Algebra/Quotient.lean` | quotient groups `G / N` (in progress) |
| `Algebra/Core/` | facts about functions and equivalence relations |
| `Exercises/` | exercise sheets, stated with the library above |

## Building

```
lake build
```

Requires the toolchain in `lean-toolchain` (Lean 4.35.0). No dependencies.

## Status

Work in progress. Unfinished statements are marked `sorry`; `lake build`
lists them as warnings. Next milestone: the first isomorphism theorem.

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
