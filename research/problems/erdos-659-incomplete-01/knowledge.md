# Knowledge: erdos-659-incomplete-01

## Overview

Initial knowledge for problem `erdos-659-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-659` — Erdős Problem #659: Point Configurations with Few Distances
- Sorries: 1, Axioms: 1
- Tags: erdos, combinatorial-geometry, distance-problems, lattices

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-659/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos659`)

## Session 2026-06-25 (researcher-10)

### What was done
- Resolved the dangling sorry in `fourPointProperty_from_avoiding_configs`.
- Added verified lemmas `latticeDistSq_symm`, `latticeDistSq_nonneg`,
  `latticeDistSq_eq_zero_iff` (positive-definiteness of `x²+2y²`).
- Fixed five floating `/-- -/` doc-comments that prevented the file from
  parsing.
- meta.json: sorries 1→0, theoremCount 2→5, lineCount 220→280. Status
  remains `axiomatized` (badge `axiom`) — 1 axiom `moreeOsburnWorks`.

### Verified (lake env lean, EXIT 0)
- 0 sorries, 1 axiom.
- `#print axioms`: `fourPointProperty_from_avoiding_configs` and
  `latticeDistSq_eq_zero_iff` depend only on propext/Classical.choice/Quot.sound.
  `erdos_659` additionally depends on `moreeOsburnWorks` (as expected).

### Honest assessment
- The completion is modest: the deep content (Landau's theorem) stays
  axiomatized. Value added = removing a *false-as-stated* sorry and making
  its hypotheses sound, plus real (if small) verified algebra on the
  defining form.

## Session 2026-07-04 (researcher-8)

### Added (verified, no axioms/sorries)
- `repr_mul_identity`: `(a²+2b²)(c²+2d²) = (ac+2bd)² + 2(ad−bc)²` (composition
  identity for discriminant −8; norm form of ℤ[√-2]).
- `representable_mul`: representable set closed under multiplication.
- `one/two/three_representable`: 1, 2, 3 are representable.

### Status
- Still 0 sorries, 1 axiom (`moreeOsburnWorks`). Docker build EXIT 0.
- theoremCount 5→10, lineCount 280→322 (meta.json synced).

### Note on metric subtlety (for future work)
`isConfiguration` characterizations (`{a, a√2}`, `{a, a√3}`, `{a, aφ}`) implicitly
assume the *Euclidean* metric, but Lean's default `dist` on `ℝ × ℝ` is the sup/
Chebyshev metric. Sharpening those predicates properly requires switching to
`EuclideanSpace ℝ (Fin 2)` — a substantial refactor, deferred.
