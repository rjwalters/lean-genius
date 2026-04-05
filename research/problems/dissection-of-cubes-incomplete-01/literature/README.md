# Literature: dissection-of-cubes-incomplete-01

## Key References

### Primary Sources
- Brooks, R.L., Smith, C.A.B., Stone, A.H., Tutte, W.T., "The Dissection of Rectangles
  into Squares", Duke Math. J. 7 (1940), 312–340.
  - Original squared-square theory; foundation of the dissection literature

- Dehn, M. (1903) — classical geometric impossibility results for cube dissection
  - Key: cubes of all different sizes cannot tile a larger cube

### Lean Formalization Files
- `proofs/Proofs/DissectionOfCubes.lean` — core structure: `Cube`, `CubeDissection`,
  `CoversUnitCube`, `allDifferentSizes`
- `proofs/Proofs/DissectionOfCubesOQ03.lean` — file with the 2 target sorries

### Gallery Entry
- `src/data/proofs/dissection-of-cubes-oq-03/` — meta.json and annotations

## Strategy Notes

The descent argument (always a smaller cube above any non-top cube) is the standard
combinatorial proof of impossibility. The challenge is expressing this in Lean via:
1. Extracting covering cubes from `CoversUnitCube`
2. Using `allDifferentSizes` to derive strict size inequalities
3. `linarith`/`omega` to close arithmetic goals
