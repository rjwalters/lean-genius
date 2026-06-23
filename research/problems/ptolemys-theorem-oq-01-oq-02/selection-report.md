# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 27 available, 559 in-progress, 1406 completed

## Selected Problem

- **ID**: ptolemys-theorem-oq-01-oq-02
- **Name**: Ptolemy Theorem: Extension to Spherical and Hyperbolic Geometry Metrics
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Tied for highest composite score among remaining candidates**: Score = 67 (T=6, S=7, EMPTY knowledge tier), selected immediately after ptolemys-complex-proof-oq-02 (same score).
2. **EMPTY knowledge tier**: No prior research in workspace — highest priority tier.
3. **Natural generalization**: Extends `ptolemys-theorem-oq-01` to non-Euclidean geometry using Mathlib's metric geometry infrastructure (`EMetricSpace`, `Metric.sphere`). A concrete and tractable extension target.
4. **Companion problem**: Pairs well with ptolemys-complex-proof-oq-02 (sine addition formula connection) — both enrich the Ptolemy theorem family with different proof techniques.

## Rejection Summary

- **Candidates considered**: 3 remaining after ptolemys-complex-proof-oq-02 selection
- **No candidates rejected** at this tier
- **Confidence**: high (clear score advantage over remaining candidates at score=67 vs 66/56/47)

## Related Gallery Proofs

- `ptolemys-theorem-oq-01`: Parent proof — Ptolemy's inequality and concyclicity characterization in Euclidean plane
- `ptolemys-complex-proof`: Complex-number approach to Ptolemy inequality
- `isoperimetric-theorem-oq-03`: Non-Euclidean geometry companion — best constants in non-Euclidean spaces (already selected in this batch)

## Suggested First Steps

1. **OBSERVE**: Study `ptolemys-theorem-oq-01` Lean source for the existing Euclidean inequality formulation; identify which parts are metric-agnostic
2. **ORIENT**: Survey Mathlib's spherical geometry (`Metric.sphere`, `EuclideanGeometry`) and hyperbolic geometry libraries for Ptolemy-relevant lemmas
3. **DECIDE**: Whether to tackle spherical and hyperbolic cases together via unified metric axioms, or tackle spherical first as a simpler extension

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 27 |
| In Progress | 559 |
| Completed | 1406 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

- Pool depth: **adequate**
- Remaining quality candidates: fair-games-theorem-oq-02-oq-01-oq-01 (score=66), divisibility-truncation-general-oq-03 (score=56), hurwitz-theorem-oq-04 (score=47)
- Moonshots excluded: twin-primes, Goldbach, Sophie Germain

## Initialized

- [x] Research workspace created (2026-04-22, exists)
- [x] problem.md populated with formal statement and context
- [x] state.md set to OBSERVE phase
- [x] Ready for /researcher
