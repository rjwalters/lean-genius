# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT + POOL REPLENISHMENT
**Pool Status**: 15 available (at threshold) → 23 available after selection

## Selected Problem

- **ID**: law-of-cosines-oq-06
- **Name**: Formalize Law of Sines using InnerProductGeometry.angle
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 8/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score** (87 = 0 + 80 + 7) among all candidates considered. Tractability 8 reflects that Mathlib already provides `InnerProductGeometry.angle` and the circumradius API; the proof is a formalization task with a clear path using existing infrastructure.
2. **EMPTY knowledge tier**: No prior research exists for this problem — first-exploration bonus puts it at maximum priority tier.
3. **Domain diversity**: Recent selections (arithmetic-series, szemeredi, erdos-szekeres) concentrated on combinatorics and number theory. This problem is from Euclidean geometry, an underrepresented domain in the current available pool.
4. **Concrete Lean target**: The problem explicitly names `InnerProductGeometry.angle` and `cos_from_sides` as entry points, making the research path tractable without open-problem risk.

## Rejection Summary

- **Candidates considered**: 23 available (15 pre-existing + 8 new)
- **Rejected (MODERATE knowledge)**: unit-distance-independence-oq-02 (score -1922, already researched)
- **Rejected (domain overlap with existing pool)**: euler-identity-oq-04 (similar to euler-identity-oq-01-oq-04 already in pool; selected as replenishment instead)
- **Rejected (open problem, low tractability)**: infinitude-primes-oq-05, prime-number-theorem-oq-01, bertrands-postulate-oq-01/02
- **Rejected (recently selected)**: mean-value-theorem-oq-04, erdos-szekeres-oq-01 (selected within last 7 days)
- **Confidence**: high (12-point spread between top candidates; law-of-cosines-oq-06 and euler-identity-oq-04 tied at 87 with law-of-cosines winning on domain diversity)

## Related Gallery Proofs

- `law-of-cosines`: Direct parent — formalization uses `inner_mul_le_norm_mul_norm`, `cos_angle_of_inner`
- `pythagorean-theorem`: Degenerate case (C=π/2) — the Law of Sines reduces to Pythagoras when C is right
- `mean-value-theorem`: Shares the `InnerProductGeometry` API surface used for angle formalization

## Suggested First Steps

1. **OBSERVE**: Read `src/data/proofs/law-of-cosines/meta.json` and the Lean source to understand what's already formalized. Run `#check InnerProductGeometry.angle` and `#check Real.sin_angle_of_inner` in Lean to see what Mathlib provides.
2. **ORIENT**: Search Mathlib for `circumradius`, `sin_rule`, `law_of_sines`. Check if `EuclideanGeometry.circumradius` exists or if it must be defined. Scout survey of trigonometric triangle lemmas in Mathlib.
3. **DECIDE**: Determine whether to (a) prove Law of Sines via area = ½ab·sin C and circumradius R = abc/(4·Area), or (b) use the inscribed angle theorem approach.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 23 |
| In Progress | 533 |
| Completed | 1239 |
| Blocked | 1 |
| **Total (DB)** | **1796** |

## Pool Replenishment Summary

8 new problems added to reach 23 available (above threshold of 15):

| Problem ID | Domain | Significance | Tractability |
|-----------|--------|-------------|-------------|
| law-of-cosines-oq-06 | Geometry | 7 | 8 |
| euler-identity-oq-04 | Complex Analysis | 7 | 8 |
| pythagorean-theorem-oq-01 | Geometry/Analysis | 7 | 7 |
| divisibility-rules-oq-02 | Number Theory | 6 | 7 |
| fundamental-arithmetic-oq-03 | Number Theory | 7 | 6 |
| sylow-theorems-oq-05 | Algebra | 7 | 6 |
| randomized-maxcut-oq-04 | Combinatorics/Prob | 7 | 6 |
| collatz-cycles-oq-04 | Number Theory | 6 | 6 |

## Candidate Pool Health

- **Pool depth**: adequate (23 available, up from 15)
- **Domain diversity**: good — geometry (2), analysis (2), number theory (3), algebra (1), combinatorics (1)
- **Next refresh recommended**: when available drops below 15 (≈ after next 8 researcher claims)
- **Recommendation**: Pool healthy. No immediate action needed.
