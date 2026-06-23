# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 1211 in-progress, 545 completed

## Selected Problem

- **ID**: unit-distance-independence-oq-02
- **Name**: Prove Hadwiger-Nelson upper bound χ(ℝ²) ≤ 7 via hexagonal 7-coloring
- **Tier**: B
- **Significance**: 8/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top composite score among valid candidates**: Score = 78 (EMPTY knowledge tier: 0 penalty + tractability×10=70 + significance=8). Highest among the 15 truly-available problems after pool/DB sync.
2. **EMPTY knowledge tier**: No prior research — first-exploration problems get highest priority.
3. **Domain diversity**: Recent selections include analysis (mean-value-theorem-oq-04, euler-identity-oq-01-oq-04, lhopital-oq-02) and number theory/combinatorics (erdos-109). This problem is combinatorial geometry — the chromatic number of the plane — a different area.
4. **Tractability 7**: The hexagonal 7-coloring argument is elementary: tile the plane with regular hexagons of diameter just under 1 and assign 7 colors periodically. The key Lean challenge is formalizing the tiling and the distance bound, but Mathlib has substantial geometry infrastructure (Metric.sphere, EuclideanSpace, etc.).
5. **Significance 8**: The Hadwiger-Nelson problem (χ(ℝ²) ∈ {4,5,6,7}) is a famous open problem; the upper bound of 7 is the classical result. Formalizing it connects graph coloring, geometry, and periodicity arguments.

## Rejection Summary

- **Candidates considered**: 15 available (after pool sync corrected stale data)
- **Candidates rejected**: 14
  - `mean-value-theorem-oq-04` (score 77): SKIP — already selected in the immediately preceding seeker run (selection-report.md dated today).
  - `euler-identity-oq-01-oq-04` (score 76): SKIP — selected in a prior seeker run today (DB status available but selection-report exists).
  - `erdos-szekeres-oq-01`, `taylor-theorem-oq-02`, `vietas-formulas-oq-02` (score 76 each): Valid but lower significance (6 vs 8); diversity penalty applies for algebra/combinatorics domain overlap with prior batch.
  - `triangular-reciprocals-oq-02`, `taylor-sincos-convergence-oq-01` (score 75): C-tier, significance 5 — not above quality threshold relative to alternatives.
  - `factor-remainder-nullstellensatz-oq-02` (score 67), `erdos-ko-rado-oq-04` (score 57): lower tractability×significance composite.
  - `wolstenholme-theorem-oq-03`, `buffons-needle-oq-01-oq-04` (score 66): lower.
  - `brouwer-fixed-point-oq-04-oq-04` (score 56): lowest tractability among fresh candidates.
  - `szemeredi-theorem-oq-01` (score 48): tractability 4 — very hard, research-frontier problem.
  - `prime-gap-bounds-oq-03`: RICH knowledge (16 items) → score -2923; only revisit if new approach found.
- **Confidence**: high (8-point gap between top candidate score 78 and next tier at 76-77, itself skipped; clear winner)

## Related Gallery Proofs

- `unit-distance-independence`: Base proof — "Unit Distance Graph Independence Numbers and Hadwiger-Nelson Bounds"; the direct parent of this open question.
- `four-color-theorem`: Four-color theorem formalization — related graph coloring infrastructure.
- `four-color-theorem-oq-01`, `four-color-theorem-oq-02`: Open questions extending the 4CT; similar combinatorial geometry setting.

## Suggested First Steps

1. **OBSERVE**: Survey Mathlib for hexagonal tiling primitives — `Mathlib.Geometry.Euclidean`, `EuclideanSpace ℝ (Fin 2)`, distance lemmas, periodic colorings. Check what `unit-distance-independence` already formalizes.
2. **ORIENT**: Identify the exact statement: define the hexagonal coloring function `f : ℝ² → Fin 7`, prove it is a proper coloring (i.e., `dist x y = 1 → f x ≠ f y`). The key bound: hexagon diameter < 1 ensures unit-distance pairs get different colors.
3. **DECIDE**: Choose between (a) explicit coordinate-based coloring with verified distance bounds, or (b) abstract lattice/periodicity argument. Option (a) is more tractable for Lean verification.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 1211 |
| Completed | 545 |
| Blocked | — |
| **Total** | **1771** |

## Candidate Pool Health

Pool was significantly out of sync prior to this run. The database had 12 fresh problems from the recent batch commit that were absent from `.lean/state/candidate-pool.json`. The sync corrected this, revealing a healthy pool.

- Pool depth: **adequate** (15 available)
- Recommendation: Pool is healthy. Next refresh when available count drops below 5.
- Next refresh recommended: when available < 5 (currently 15)
