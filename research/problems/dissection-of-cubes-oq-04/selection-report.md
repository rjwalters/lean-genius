# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 31 available, 1309 in-progress, 1408 completed

## Selected Problem

- **ID**: dissection-of-cubes-oq-04
- **Name**: Dissection of Cubes: Connection to Dehn Invariant Impossibility
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 57
- **Status**: available

## Selection Rationale

1. **Only uninitiated available problem**: All 30 other available problems already had
   initialized workspaces in OBSERVE or NEW phase. This was the sole remaining problem
   with no workspace — genuinely adding new coverage to the pipeline.

2. **Mathematical substance**: Dehn invariants connect to Hilbert's Third Problem, K-theory
   (Dupont-Sah: 𝒫(ℝ³) ≅ K₃(ℝ)), and Niven's irrationality method. The two remaining
   axioms have clear proof paths via Mathlib's Module.Flat API and the established
   Chebyshev sequence pattern.

3. **Domain diversity**: Previous seeker selection in this batch was Szemerédi/combinatorics
   (`szemeredi-full-oq-01`). This problem is in geometry/algebra — good diversity.

4. **Concrete completion path**: The parent proof has 2 axioms; both have identifiable
   Mathlib routes. This is a completion task, not open-ended research.

## Rejection Summary

- **Candidates considered**: 31 available in pool
- **Candidates with workspaces already**: 30 (all in OBSERVE/NEW phase, previously selected)
- **Moonshots rejected**: 3 (sophie-germain-oq-01, twin-primes-special-oq-01, weak-goldbach-oq-01; tractability ≤ 2)
- **Already claimed**: 3 (erdos-476-oq-05-wip-01, solution-of-cubic-oq-05, sqrt2-minpoly-oq-01)
- **Already selected this batch**: 1 (szemeredi-full-oq-01, sqrt2-minpoly-oq-02)
- **Confidence**: high (sole uninitiated problem; clear distinction)

## Related Gallery Proofs

- `dissection-of-cubes-oq-04`: Immediate parent — Platonic solid Dehn invariant classification
- `dissection-of-cubes`: Original Dehn impossibility (cube ≇ tetrahedron)
- `dissection-of-cubes-oq-01–03`: Scissors congruence group, rational arccos, K-theory

## Suggested First Steps

1. **OBSERVE**: Read the parent gallery proof (`src/data/proofs/dissection-of-cubes-oq-04/`)
   to understand the existing proof structure and which axioms remain
2. **ORIENT**: Search Mathlib for `Module.Flat` — check `Flat.iff_liftingProperty` and
   related lemmas; also search for `TensorProduct` torsion lemmas
3. **DECIDE**: If `Module.Flat` yields the flatness axiom easily, prove that first. Then
   assess the Chebyshev extension for `icoAngle_irrational` by adapting the octahedron proof.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 31 |
| In Progress | 1309 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 4 |
| **Total** | **1996** |

## Candidate Pool Health

- Pool depth: **adequate** (31 available, threshold 15)
- All 31 available problems have initialized workspaces in OBSERVE/NEW phase
- Pipeline is well-stocked; researchers have 31 problems to claim
- **Note**: Database showed `sperner-ndim-oq-04` as "available" but it has an ACT-phase
  workspace — DB sync lag. This should self-correct when the researcher completes it.
- Next refresh recommended: when available count drops below 15

## Initialized

- [x] Research workspace created: `research/problems/dissection-of-cubes-oq-04/`
- [x] problem.md populated with formal statement, approaches, and references
- [x] state.md set to OBSERVE phase
- [x] Pool synced (research/candidate-pool.json → .lean/state/candidate-pool.json)
- [x] Ready for /researcher
