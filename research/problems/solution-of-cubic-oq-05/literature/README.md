# Literature for solution-of-cubic-oq-05

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `solution-of-cubic` | Source: `SolutionOfCubic.lean` — Cardano's formula, `cardanoRoot`, `cardano_formula_is_root` |
| `general-quartic` | Target: `GeneralQuartic.lean` — `resolventCubic`, Ferrari's factorization |
| `solution-of-cubic-oq-03` | Vieta's formulas for cubic roots (root sum/product identities) |
| `solution-of-cubic-oq-03-oq-01` | Cubic discriminant analysis |

## Classical References

- **Ferrari (1545)**: Original method for reducing quartic to cubic via resolvent
- **Cardano, Ars Magna (1545)**: Cardano's formula for depressed cubic
- **Lang, Algebra (2002)**: Modern treatment, Ch. VI §9 — solving quartics by resolvent cubic
- **Roman, Field Theory (2006)**: Galois theory perspective on resolvent cubic

## Key Mathematical Facts

- The resolvent cubic for y⁴ + py² + qy + r is: `8m³ + 20pm² + (16p²-8r)m + (4p³-4pr-q²) = 0`
- Substitution m = n − 5p/6 depresses it to a cubic in n solvable by Cardano's formula
- Once m is known, the quartic factors as: `(y² + p/2 + m ± √(2m + p - q/√(2m+p)))`
- The discriminant condition ensures Ferrari's factorization succeeds

## Lean/Mathlib Resources

- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` — polynomial evaluation lemmas
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — complex powers and branches
