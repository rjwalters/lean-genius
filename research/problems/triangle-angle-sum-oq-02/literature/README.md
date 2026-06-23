# Literature for triangle-angle-sum-oq-02

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `triangle-angle-sum` | Foundation: Euclidean angle sum proof (sum = π) |
| `triangle-angle-sum-oq-01` | Converse: angle sum = π implies Euclidean |
| `triangle-angle-sum-oq-03` | Mathlib angle degenerate case analysis |
| `spherical-law-of-cosines` | Spherical geometry where angle sum > π |
| `spherical-law-of-sines` | Spherical geometry infrastructure |

## Classical References

- **Descartes, De Solidorum Elementis (~1630)**: First formulation of the angle defect theorem
- **Euler (1752)**: V - E + F = 2 for convex polyhedra
- **Gauss, Disquisitiones Generales (~1827)**: Gaussian curvature, total curvature theorem
- **Bonnet (1848)**: Generalization to arbitrary surfaces
- **Milnor, "Curvature of Left Invariant Metrics" (1976)**: Modern perspective

## Key Mathematical Facts

- Discrete Gauss-Bonnet: ∑_{v} angle_defect(v) = 2π · χ(P)
- For S² (sphere topology): χ = 2, so total defect = 4π
- Proof from Euler's formula: 4π = 2π(V - E + F) = 2πV - 2πE + 2πF
  = 2πV - (total interior angles) where each face contributes (f_i - 2)π per polygon
- Connection to smooth: Gaussian curvature K = angle_defect / area element

## Lean/Mathlib Resources

- `Mathlib.Combinatorics.SimplicialComplex.Basic` — simplicial complex definitions
- `Mathlib.Topology.EulerCharacteristic` — if available
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product angle
- `EuclideanGeometry.angle` — angle between points in Euclidean space
