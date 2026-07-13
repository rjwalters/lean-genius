# Selection Report: feuerbachs-theorem-defs-oq-04

**Date**: 2026-04-23
**Seeker Run**: batch-selections-2026-04-23 (second batch)
**Mode**: SELECT

## Selected Problem

- **ID**: feuerbachs-theorem-defs-oq-04
- **Name**: Feuerbach's Theorem: Connect to Mathlib Affine Geometry Framework
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY — highest priority tier)
- **Composite Score**: 77 (only EMPTY-knowledge candidate available)
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier — highest priority by algorithm**: No prior research has been
   logged for this problem. The composite scoring formula assigns knowledge-tier 0 a bonus
   of +0 (vs. –1000 for WEAK), making this the highest-scoring candidate regardless of
   tractability and significance values among the unselected pool.

2. **Tractability 7/10 — the math is done, this is API work**: The mathematical result
   (Feuerbach's theorem: the nine-point circle is internally tangent to the incircle) is
   fully proven in the gallery using a custom coordinate API. OQ-04 is a translation task:
   re-express the result in Mathlib's `EuclideanSpace ℝ (Fin 2)` / `Sphere` framework.
   This is primarily Lean engineering, not new mathematics.

3. **Mathlib contribution path**: A `toEuclidean : Point → EuclideanSpace ℝ (Fin 2)`
   bridge lemma, once proven, would benefit multiple gallery proofs using the same custom
   coordinate infrastructure. Potential upstream Mathlib PR.

4. **Domain diversity**: Current batch covers measure-theoretic geometry (dissection-of-cubes)
   and combinatorics/ergodic theory (Szemerédi). Classical Euclidean geometry/API bridging
   is a distinct subfield.

## Quality Gate

- Near-duplicate of recent completions? **No** — no Feuerbach-related problems completed
  recently; OQ-04 is specifically about API translation, distinct from OQ-01/OQ-03
- Shallow specialization? **No** — building `EuclideanSpace ℝ (Fin 2)` bridge has
  structural value for multiple gallery proofs
- One-off example check? **No** — the `toEuclidean` lemmas would form a reusable library
- Significance ≥ 3? **Yes** (7/10)
- Last 3 selections same domain? **No** — geometry, ergodic theory, and now API-bridging

## Rejection Summary

- **Candidates considered from unselected pool**: 9 (problems without selection-report.md)
- **Moonshots rejected (tractability ≤ 2)**: 3 — `sophie-germain-oq-01`,
  `twin-primes-special-oq-01`, `weak-goldbach-oq-01`
- **RICH knowledge rejected**: 3 — `lebesgue-measure-oq-06` (30 items), `sperner-ndim-oq-04`
  (63 items), `erdos-476-oq-05-wip-01` (17 items) — lower priority tier
- **WEAK but lower composite**: `szemeredi-full-oq-02` (tract 3, composite -962),
  `sqrt2-plus-sqrt3-irrational-oq-03` (tract 9, sig 6, composite -934 — close second)
- **Confidence**: High — EMPTY tier advantage is decisive (+1000 points over WEAK)

## Related Gallery Proofs

- `FeuerbachsTheoremDefs.lean`: Source of custom API to be bridged — primary reference
- `FeuerbachsTheoremDefsOQ03.lean`: Feuerbach point uniqueness using same custom API
- `FeuerbachsTheoremOQ01.lean`: Main tangency results — the theorems to re-express
- `sperner-ndim`: Example of `EuclideanSpace ℝ (Fin n)` usage in gallery

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/FeuerbachsTheoremDefs.lean` to map the custom API
   (`Point`, `dist2`, `Triangle`, `circlesInternallyTangent`); then browse
   `Mathlib.Geometry.Euclidean.Sphere.Basic` for the `Sphere` type definition and
   membership/tangency lemmas

2. **ORIENT**: Define `toEuclidean : Point → EuclideanSpace ℝ (Fin 2)` and prove the
   key bridge lemma `dist (toEuclidean P) (toEuclidean Q) = dist2 P Q`; verify
   `dist2` is actual distance (not squared despite the name)

3. **DECIDE**: Assess whether to use the bridge to lift existing theorems or reformulate
   from scratch in Mathlib types; check if Mathlib's `circumcenter` API matches the
   gallery's explicit coordinate formulas well enough for a bridge approach

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 31 |
| In Progress | 559 |
| Completed | 1401 |
| Graduated | 3 |
| Blocked | 2 |
| **Total** | **1996** |

## Candidate Pool Health

- **Pool depth**: adequate (31 available, threshold = 15)
- **Recommendation**: Pool healthy; 3 moonshot problems (tractability ≤ 2) are
  occupying available slots but should not be selected — consider marking them
  `blocked` to reduce noise in availability counts
- **Next refresh recommended**: When available drops below 20

## Initialized

- [x] Research workspace exists (problem.md, state.md)
- [x] knowledge.md created (empty, tier 0)
- [x] Database registered (available)
- [x] Pool JSON synced
- [ ] Ready for /researcher
