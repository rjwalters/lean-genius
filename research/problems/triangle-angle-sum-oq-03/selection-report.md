# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 27 available, 559 in-progress, 1406 completed, 3 graduated, 1 blocked

## Selected Problem

- **ID**: triangle-angle-sum-oq-03
- **Name**: Triangle Angle Sum: Mathlib Angle Function Degenerate Cases
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among fresh candidates**: Composite score of 76 (tractability
   7 × 10 + significance 6) — top among unclaimed, un-previously-selected EMPTY problems
   after filtering recently selected problems and the pre-selected
   `minkowski-fundamental-theorem-oq-04` (already selected 2026-04-22, workspace exists).

2. **EMPTY knowledge tier**: No prior research notes exist; the investigation starts from
   scratch and will yield novel insights about Mathlib's angle function API.

3. **High tractability**: The question is directly investigatable by reading Lean source code
   and running examples. No novel mathematics is required — the research produces a precise
   API characterization with concrete examples.

4. **Formalization value**: Understanding how `Real.angle` and `EuclideanGeometry.angle`
   handle degenerate (collinear) configurations is necessary for anyone extending triangle
   angle sum results to pathological cases. Gaps here could silently break downstream proofs.

5. **Domain diversity**: Mathlib API / edge-case geometry is distinct from the five problems
   selected in this batch: ergodic theory, minimal polynomials, hypergraph combinatorics,
   n-dim topology, and group theory.

## Rejection Summary

- **Candidates considered**: 27 available
- **Candidates rejected**: 26
  - `minkowski-fundamental-theorem-oq-04` (composite 77): Already selected 2026-04-22 —
    workspace and selection report exist; skipped to avoid redundant re-selection
  - `sqrt2-minpoly-oq-01` (composite 97): Domain penalty — same problem family as
    `sqrt2-minpoly-oq-02` selected this batch
  - `lebesgue-measure-oq-06` (composite −2,932): RICH knowledge (27 items), de-prioritized
  - `szemeredi-regularity-oq-02`, `szemeredi-full-oq-02`: Szemerédi domain, 2 already selected
    this batch (szemeredi-full-oq-01, szemeredi-counting-oq-02)
  - `sperner-ndim-oq-02`, `sylow-theorem-oq-02`, `szemeredi-counting-oq-02`,
    `sqrt2-minpoly-oq-02`, `szemeredi-full-oq-01`: Selected this batch
  - `erdos-476-oq-05-wip-01`: Active claim lock present
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`:
    Tractability ≤ 2 — open conjectures unsuitable for autonomous research
  - Remaining at composite 67: Lower score than selected candidate
- **Confidence**: high (9-point gap over the next tier of candidates)

## Related Gallery Proofs

- `triangle-angle-sum`: Parent proof — triangle angle sum π for Euclidean triangles using
  Mathlib's `EuclideanGeometry` and `Real.angle`; the proof to inspect for degenerate
  behavior
- `napoleons-theorem`: Uses similar angle arithmetic in Euclidean geometry context
- `ptolemys-theorem-oq-01`: Related geometric angle relationships

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/TriangleAngleSum.lean` and identify every usage of
   `Real.angle` and `EuclideanGeometry.angle` — note whether degenerate cases (collinear
   points) are mentioned or guarded against.
2. **ORIENT**: Search Mathlib for `Real.angle` documentation and `angle_eq_zero_iff`,
   `angle_comm`, `angle_add_angle_eq_pi_of_collinear` — determine what Mathlib asserts
   for collinear configurations.
3. **DECIDE**: Characterize the three cases: (a) all three points equal, (b) two points
   equal, (c) three distinct collinear points — and record what `EuclideanGeometry.angle`
   returns for each, with a Lean example or reference to existing theorems.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 27 |
| In Progress | 559 |
| Completed | 1406 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

Pool is healthy and well above the threshold of 15.

- Pool depth: **adequate** (27 available)
- Recommendation: Pool healthy — no replenishment needed
- Next refresh recommended: when available count drops below 15
