# Literature: erdos-1151-oq-04

## Key References

### Primary
- **Erdos1151Problem.lean** (`proofs/Proofs/Erdos1151Problem.lean`)
  — Parent proof with `erdos_1941_divergence` axiom

### Classical Analysis
- Erdős, P. (1941): "On the convergence of trigonometric series"
  — Original divergence result for rational cosine points
- Natanson, I.P.: "Constructive Function Theory" Vol. III
  — Comprehensive treatment of Chebyshev interpolation and Lebesgue function
- Brutman, L. (1997): "Lebesgue Functions for Polynomial Interpolation — A Survey"
  — Survey of Lebesgue function bounds for various node systems

### Chebyshev Nodes
- Mason & Handscomb: "Chebyshev Polynomials" (2003, CRC Press)
  — Standard reference for Chebyshev polynomial and interpolation theory

### Lean 4 / Mathlib
- `Mathlib.Analysis.Polynomial.Chebyshev` — Chebyshev polynomial T_n, U_n
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — trigonometric functions
- `Mathlib.Topology.Algebra.Order` — filter tendsto, atTop
