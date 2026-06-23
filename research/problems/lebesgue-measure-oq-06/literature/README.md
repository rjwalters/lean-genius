# Literature: Banach-Tarski Paradox Formalization

## Primary Sources

### Banach & Tarski (1924)
- **Title**: "Sur la décomposition des ensembles de points en parties respectivement congruentes"
- **Venue**: Fundamenta Mathematicae 6, 244–277
- **Note**: Original paper. Proves paradoxical decomposability of the unit ball using the Hausdorff paradox.

### Hausdorff (1914)
- **Title**: "Bemerkung über den Inhalt von Punktmengen" (and "Grundzüge der Mengenlehre")
- **Note**: Contains the Hausdorff paradox: paradoxical decomposition of S² minus a countable set.
  This is the key prerequisite for Banach-Tarski.

### Wagon, Stan (1985)
- **Title**: "The Banach-Tarski Paradox"
- **Venue**: Cambridge University Press (Encyclopedia of Mathematics and its Applications, Vol. 24)
- **Note**: Definitive modern treatment. Chapter 1–3 gives the free-subgroup-in-SO(3) argument;
  Chapter 4 gives Tarski's equivalence theorem. Best reference for formalization.

### Tarski (1938)
- **Title**: "Algebraische Fassung des Massproblems"
- **Venue**: Fundamenta Mathematicae 31, 47–66
- **Note**: Tarski's equivalence: G-paradoxical decomposability ⟺ no G-invariant finitely-additive
  probability measure. Essential for connecting to Lebesgue measure theory.

## Secondary Sources / Surveys

### Laczkovich (1990)
- **Title**: "Equidecomposability and discrepancy; a solution of Tarski's circle-squaring problem"
- **Venue**: Journal für die reine und angewandte Mathematik 404
- **Note**: Proved Tarski's circle-squaring conjecture (disk → square via congruent pieces,
  countably many). Uses Banach-Tarski-type arguments. Related to `erdos-1124` in gallery.

### Dougherty & Foreman (1994)
- **Title**: "Banach-Tarski decompositions using sets with the property of Baire"
- **Venue**: Journal of the American Mathematical Society 7(1), 75–124
- **Note**: Improves Banach-Tarski to use Baire-property sets (stronger than measurability).

## Lean 4 / Mathlib References

### Mathlib: SpecialOrthogonalGroup
- `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` — contains SO(n) definition
- Key types: `Matrix.SpecialOrthogonalGroup ℝ (Fin 3)` for SO(3)

### Mathlib: Free Groups
- `Mathlib.GroupTheory.FreeGroup.Basic` — free groups
- `Mathlib.GroupTheory.Subgroup.Basic` — subgroups

### Community Search
- Lean4 Zulip: search "Banach-Tarski" for any formalization attempts
- Mathlib4 GitHub: search for "paradox" or "Hausdorff paradox" in GroupTheory files
