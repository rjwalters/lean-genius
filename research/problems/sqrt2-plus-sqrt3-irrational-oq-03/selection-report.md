# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 31 available, 559 in-progress, 1401 completed

## Selected Problem

- **ID**: sqrt2-plus-sqrt3-irrational-oq-03
- **Name**: Minimal Polynomial of √2+√3 over ℚ
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 9/10
- **Knowledge Score**: 4 (WEAK)
- **Status**: available

## Selection Rationale

1. **Highest composite score**: −904 = −1000 + 9×10 + 6. Tractability of 9/10 reflects that the polynomial x⁴−10x²+1 is known explicitly and irreducibility is an elementary check.
2. **WEAK knowledge tier**: 4 knowledge items — problem.md, state.md, and two literature entries — so the workspace is initialized but unexplored. Research value is high.
3. **Domain diversity**: Last three selections were geometry (feuerbach), dissection/invariant theory (dissection-of-cubes), and combinatorics (szemeredi-full). This problem is algebra/field theory — good rotation.
4. **No near-duplicates recently completed**: `cube-root-3-irrational-oq-02` (Eisenstein for ∛3) was completed recently, but that is structurally distinct — this problem uses quadratic irreducibility analysis, not Eisenstein directly.

## Rejection Summary

- **Candidates considered**: 28 (31 available minus 3 with active claim locks)
- **Candidates rejected**: 27
  - All Tier-A problems (significance ≥ 8, tractability ≤ 6): outscored by high-tractability B-tier candidates
  - `sqrt2-minpoly-oq-02` (−913): similar minimal-polynomial domain to sibling `sqrt2-minpoly-oq-01` (currently claimed); diversity penalty applied
  - `sqrt2-minpoly` (−914): potential crowding with two sibling problems in same cluster
  - `feuerbachs-theorem-defs-oq-04` (−923): geometry — recently selected (last commit); diversity penalty
  - Remaining: lower composite scores
- **Confidence**: high — gap between top candidate (−904) and second-place (−913) is 9 points

## Related Gallery Proofs

- `sqrt2-plus-sqrt3-irrational`: direct predecessor — irrationality via squaring argument
- `cube-root-2-irrational`: structural analogue — minimal polynomial of ∛2 is x³−2
- `algebraic-numbers-countable`: context — algebraic numbers as roots of integer polynomials

## Suggested First Steps

1. **OBSERVE**: Locate `sqrt2-plus-sqrt3-irrational` gallery entry and its Lean source; extract the `Real.sqrt` API used there as scaffolding
2. **ORIENT**: Check Mathlib's `Polynomial.minpoly` and irreducibility lemmas; confirm `algebraMap ℚ ℝ` chain is available
3. **DECIDE**: Choose between (a) direct `minpoly` API proof or (b) elementary: show f(α)=0 + rational-root check + no-quadratic-factor argument; approach (b) is safer given tractability rating

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 31 |
| In Progress | 559 |
| Completed | 1401 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

Pool has 31 available problems against a threshold of 15 — **adequate**.

- Pool depth: adequate
- Recommendation: Pool healthy; no replenishment needed this cycle
- Next refresh recommended: when available drops below 15
