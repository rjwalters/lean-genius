# Literature — sperner-simplicial-bridge-oq-01

Placeholder for downloaded papers / reference cards.

## Survey references (S1)

- De Longueville, M. (2013). *A Course in Topological Combinatorics*.
  Springer. Chapter 2 — Sperner's lemma on non-pure simplicial
  complexes via stratification; door-pairing is dimension-graded.
- Henle, M. (1979). *A Combinatorial Introduction to Topology*. Dover.
  Classical barycentric-subdivision framework for Sperner on
  triangulated manifolds with boundary.
- Mathlib reference: `Geometry.SimplicialComplex.facets` —
  the maximal-face encoding of a simplicial complex.

## Mathlib (v4.26.0) reference modules

- `Mathlib.Data.Finset.Filter` — `Finset.filter`, `Finset.mem_filter`,
  `Finset.filter_filter`, `Finset.filter_subset`,
  `Finset.filter_empty`, `Finset.card_filter_le`.
- `Mathlib.Geometry.SimplicialComplex.Basic` — Mathlib's
  `SimplicialComplex.facets` infrastructure (cf. parent OQ-02).
- (Parent) `Proofs.SpernerSimplicialBridge` — pure-pseudomanifold
  `exists_panchromatic`.
- (Parent) `Proofs.SpernerMathlib` — abstract door-counting
  framework.
