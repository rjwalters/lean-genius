# Problem: erdos-100-oq-01-wip-01

## Summary

Proving the Anning–Erdős theorem: any non-collinear planar integer-distance set
with all distances ≤ d has at most 2d²+2 points.

**Status**: ACT — core lemmas proved, one fiber-counting sorry remains.

**File**: `Proofs/Erdos100OQ01WIP01.lean` (214 lines, 1 sorry)

## Session 2026-05-04 (Session 1) — Core lemma development

**Mode**: FRESH
**Outcome**: progress — 3 of 4 theorems fully proved

### What I Did

- Created `Proofs/Erdos100OQ01WIP01.lean` with complete proof infrastructure
- Proved `quadratic_at_most_two_roots`: nonzero quadratic ax²+bx+c has ≤ 2 roots
  - Uses ring identity `(p-q)*(a*(p+q)+b) = (ax²+bx+c) - (ay²+by+c)`, avoids Polynomial API
  - `linear_combination` closes the key steps
- Proved `three_pts_two_circles_contra` (fully, no sorry):
  - Subtract circle equations → radical axis: 2*dx*x + 2*dy*y = K
  - Case split: dx=0 (all points share y, quadratic in x) vs dx≠0 (radical axis gives x=f(y), quadratic in y)
  - Key step: `linear_combination (2*dx)^2 * hp1` proves the circle×(2dx)² = quadratic identity
  - `quadratic_at_most_two_roots` gives contradiction from 3 distinct roots
- Proved `anning_erdos_finiteness` assuming `int_dist_card_le` (modulo 1 sorry)
- Created gallery entry at `src/data/proofs/erdos-100-oq-01-wip-01/`
- Docker build failed due to git network error (infrastructure, not code)

### Key Findings

- `linear_combination` tactic is the right tool for circle/quadratic algebra
- The dx=0 / dx≠0 case split cleanly handles both orientations of the radical axis
- Three distinct roots of a degree-2 polynomial contradicts `quadratic_at_most_two_roots`
- `pow_eq_zero_iff (by norm_num) |>.mp h3` closes `A ≠ 0` (where A = (2dy)² + (2dx)²)

### Remaining Sorry

`int_dist_card_le` line ~180:
```
-- Partition T = S \ {P₁,P₂} by distance pairs (k₁,k₂) ∈ {1..d}²
-- Each fiber has ≤ 2 elements by three_pts_two_circles_contra
-- |T| ≤ 2*d²
sorry
```

**Why hard**: Lean 4 Finset cardinality partition arguments require either:
- `Finset.card_biUnion` with explicit disjointness proof
- An explicit injection T → {1..d}² × Fin 2 (requires constructing the "which of the 2 intersection points" index)

**Submit to Aristotle**: This is a HARD sorry with a clear mathematical argument. Good candidate.

### Files Modified

- `proofs/Proofs/Erdos100OQ01WIP01.lean` (created, 214 lines)
- `src/data/proofs/erdos-100-oq-01-wip-01/meta.json` (created)
- `src/data/proofs/erdos-100-oq-01-wip-01/index.ts` (created)
- `src/data/proofs/erdos-100-oq-01-wip-01/annotations.json` (created)
- `src/data/research/problems/erdos-100-oq-01-wip-01.json` (updated)

### Next Steps

1. Submit the fiber-counting sorry in `int_dist_card_le` to Aristotle
2. If Aristotle proves it, merge and update `Erdos100OQ01.lean` to import from this file
3. Alternatively: prove fiber counting manually using `Finset.card_biUnion`
