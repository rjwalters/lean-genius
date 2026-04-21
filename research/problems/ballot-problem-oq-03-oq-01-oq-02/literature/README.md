# Literature: Hook-Length Formula via LGV Lemma

## Key References

### Primary
- **Frame-Robinson-Thrall (1954)**: "The hook graphs of the symmetric group"
  — Original hook-length formula paper. Canadian J. Math. 6, 316-324.
- **Gessel-Viennot (1985)**: "Binomial determinants, paths, and hook length formulae"
  — The LGV approach to hook-length. Adv. Math. 58, 300-321.
- **Lindström (1973)**: "On the vector representations of induced matroids"
  — Original LGV lemma. Bull. London Math. Soc. 5, 85-90.

### Mathlib
- `Mathlib.Combinatorics.YoungDiagram`: YoungDiagram definition, arm/leg functions
- `Mathlib.Combinatorics.YoungTableaux`: StandardYoungTableaux (if available)
- Check: `Mathlib.Combinatorics.Hooklength` — may not exist yet

### Gallery
- `BallotProblemOQ03.lean` (2879 lines): 2×2 LGV lemma, lgvDet, Lindström involution
- `BallotProblemOQ03OQ02.lean` (2315 lines): General n×n LGV, lgv_universality
- `BallotProblemOQ03OQ03.lean` (188 lines): 2-row hook-length formula

## Notes

The Gessel-Viennot (1985) paper directly proves the hook-length formula via LGV.
The key step is encoding SYT of shape λ as non-intersecting lattice paths with
sources at $(0, \lambda_i' + r - i)$ and targets at $(n_i + r - i, 0)$ where
$\lambda'$ is the conjugate partition. The resulting determinant factors as ∏ h(u).
