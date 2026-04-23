# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 30 available, 556 in-progress, 1407 completed, 7 graduated, 4 blocked

## Selected Problem

- **ID**: triangle-angle-sum-oq-03
- **Name**: Triangle Angle Sum: Mathlib Angle Function Degenerate Cases
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among fresh, unclaimed candidates**: Composite score of 76
   (tractability 7 × 10 + significance 6) — tied with `cauchy-schwarz-integral-oq-01-oq-03-oq-01`
   (just selected in the previous commit), after rejecting `minkowski-fundamental-theorem-oq-04`
   (composite 77, stuck — selected 5+ times with no researcher pickup).

2. **EMPTY knowledge tier**: No prior research notes exist; the investigation starts from
   scratch and will yield novel insights about Mathlib's `Real.angle` / `EuclideanGeometry.angle` API.

3. **High tractability (7/10)**: The question is directly investigatable by reading Lean source
   code and running examples. No novel mathematics required — the research produces a precise
   API characterization with concrete examples and proofs.

4. **Formalization value**: Understanding how Mathlib's angle function handles degenerate
   (collinear) configurations is necessary for downstream proofs extending triangle results to
   pathological cases. Undocumented behavior here can silently break proofs.

5. **Domain diversity**: Geometry/Mathlib API edge cases is distinct from the five most recent
   selections: harmonic series (Erdős #268), exponential sums (Erdős #512), Hölder inequality
   (Cauchy-Schwarz), directed Eulerian circuits (Königsberg), and Szemerédi weak regularity.

## Rejection Summary

- **Candidates considered**: 30 available
- **Candidates rejected**: 29
  - `minkowski-fundamental-theorem-oq-04` (composite 77): STUCK — selected 5+ consecutive
    times with no researcher pickup; skipped to break loop
  - `cauchy-schwarz-integral-oq-01-oq-03-oq-01` (composite 76): Selected in previous commit
    (b900ba6076) — too recent, cooldown applied
  - `szemeredi-regularity-oq-02` (composite 68): Recently selected (c9f0f0f243)
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: T ≤ 2
    (open conjectures, unsuitable for autonomous research)
  - `szemeredi-full-oq-01` (composite 49), `szemeredi-full-oq-02` (composite 38): Szemerédi
    domain recently covered; lower tractability
  - All other candidates: lower composite score (≤ 68) than selected candidate
- **Confidence**: high (clear top candidate after applying quality gate)

## Related Gallery Proofs

- `triangle-angle-sum`: Parent proof — triangle angle sum = π for Euclidean triangles using
  Mathlib's `EuclideanGeometry` and `Real.angle`; the existing proof to inspect for how
  degenerate cases are handled or sidestepped
- `napoleons-theorem`: Uses similar angle arithmetic in Euclidean geometry context
- `ptolemys-theorem-oq-01`: Related geometric angle relationships

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/TriangleAngleSum.lean` — identify every usage of
   `Real.angle` and `EuclideanGeometry.angle`, note whether collinear/degenerate cases
   are mentioned or guarded against.
2. **ORIENT**: Search Mathlib for `Real.angle` docs and `angle_eq_zero_iff`,
   `angle_comm`, `angle_add_angle_eq_pi_of_collinear` — determine what Mathlib asserts
   for collinear configurations.
3. **DECIDE**: Characterize three degenerate cases: (a) all three points equal,
   (b) two points equal, (c) three distinct collinear points — record what
   `EuclideanGeometry.angle` returns for each, supported by Lean examples or existing theorems.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 30 |
| In Progress | 556 |
| Completed | 1407 |
| Graduated | 7 |
| Blocked | 4 |

## Candidate Pool Health

Pool is healthy and well above the threshold of 15.

- Pool depth: **adequate** (30 available)
- Recommendation: Pool healthy — no replenishment needed
- Next refresh recommended: when available count drops below 15
