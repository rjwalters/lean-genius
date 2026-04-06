# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 533 in-progress, 1238 completed, 0 graduated

## Selected Problem

- **ID**: buffons-needle-oq-01-oq-04
- **Name**: Generalize Buffon's needle to Buffon's coin (2D object) and beyond
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among fresh (never-selected) candidates**: Composite = 66 =
   (tractability 6 × 10) + significance 6, with knowledge_tier=0 (EMPTY). The 11 other
   available problems with higher individual composites have all been selected recently
   (within the last 9 seeker commits) and are being held in limbo awaiting researcher
   claims. Selecting a fresh problem avoids redundancy and diversifies the queue.

2. **Rich gallery chain**: The problem sits on the `buffons-needle-oq-01` branch
   ("Buffon-Barbier for C¹ Curves: Smooth Noodle Theorem") and `buffons-needle-oq-02`
   ("3D Buffon's Noodle"). The oq-04 variant extends into 2D objects (coins, convex bodies)
   via Cauchy's integral formula for mean width, a bridge from classical integral geometry
   to Mathlib's measure theory.

3. **Domain diversity**: Recent selections covered number theory (wolstenholme-theorem-oq-03),
   analysis (taylor-sincos-convergence-oq-01, triangular-reciprocals-oq-02), and
   combinatorics (burnside-counting-oq-01, unit-distance-independence-oq-02).
   Probability/integral geometry is a fresh domain not recently explored.

4. **EMPTY knowledge tier** — maximum priority for exploration.

## Rejection Summary

- **Candidates considered**: 15 available problems
- **Candidates rejected**: 14
  - **11 recently selected** (within last 9 seeker commits, still unclaimed):
    mean-value-theorem-oq-04, euler-identity-oq-01-oq-04, wolstenholme-theorem-oq-03,
    taylor-sincos-convergence-oq-01, triangular-reciprocals-oq-02, burnside-counting-oq-01,
    unit-distance-independence-oq-02, vietas-formulas-oq-02, taylor-theorem-oq-02,
    factor-remainder-nullstellensatz-oq-02, erdos-szekeres-oq-01
  - **prime-gap-bounds-oq-03**: MODERATE knowledge (9 items) → penalized (-1923 composite)
  - **taylor-sincos-convergence-oq-01**: RICH knowledge (18 items) → penalized (-2925 composite)
  - **erdos-ko-rado-oq-04**: fresh (57), brouwer-fixed-point-oq-04-oq-04 (56),
    szemeredi-theorem-oq-01 (48) — outscored by buffons-needle-oq-01-oq-04 (66)
- **Confidence**: high (clear gap between selected candidate and fresh alternatives)

## Related Gallery Proofs

- `buffons-needle`: Buffon's Needle Problem — the foundational classical result
- `buffons-needle-oq-01`: Buffon-Barbier for C¹ Curves (Smooth Noodle) — intermediate step
- `buffons-needle-oq-02`: 3D Buffon's Noodle (Parallel Planes) — dimensional extension
- `buffons-needle-oq-01-oq-01`: likely further extension in the chain — check content

## Suggested First Steps

1. **OBSERVE**: Survey `src/data/proofs/buffons-needle-oq-01/` and `buffons-needle-oq-02/`
   for what Lean infrastructure already exists (measure-theoretic setup, integral notation).
   Determine whether Crofton's formula or Cauchy's mean width formula appears in Mathlib.

2. **ORIENT**: Run Scout on `Mathlib.MeasureTheory.Measure.Haar` and
   `Mathlib.Analysis.InnerProductSpace.Basic` to find Cauchy/Crofton-adjacent lemmas.
   The key identity is: for a convex body K, `E[crossings] = perimeter(K) / (π·d)`.

3. **DECIDE**: Choose between (a) direct proof via discretization of the 2D object into
   many needles and applying linearity of expectation, or (b) direct formalization of
   Cauchy's formula `perimeter = π · mean_width` via Mathlib's convex geometry API.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 533 |
| Completed | 1238 |
| Graduated | 0 |
| **Total** | **1787** |

## Candidate Pool Health

The pool's 15 available problems contain many problems that have been selected in recent
seeker runs but not yet claimed by researchers. This is a researcher-throughput issue, not
a pool depth issue. Only 4 problems have never been selected before.

- **Pool depth**: adequate (15 available above threshold of 5)
- **Fresh candidate depth**: low (4 never-selected problems remaining)
- **Recommendation**: Pool is functional but the backlog of unclaimed available problems
  suggests researchers may be saturated. Consider monitoring researcher claim rate.
- **Next refresh recommended**: After the remaining 3 fresh candidates are selected, or
  if researcher claim rate picks up and available count drops below 5.
