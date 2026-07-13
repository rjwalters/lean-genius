# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 1210 in-progress, 546 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: mean-value-theorem-oq-04
- **Name**: Cleanest formalization of FTC using mean value theorem structure
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top eligible composite score**: Composite = 77 = (tractability 7 × 10) + significance 7,
   with knowledge_tier=0 (EMPTY — no research JSON in `src/data/research/problems/`). The raw
   top scorer `unit-distance-independence-oq-02` (score 78) was rejected for duplicate recent
   selection (appeared twice in last 3 seeker runs). Runner-up `prime-gap-bounds-oq-03` (score
   77) was rejected as a same-day repeat (selected earlier today). This problem is the next
   highest qualifying candidate with score 77.

2. **EMPTY knowledge tier**: No research JSON file exists for this problem. Per the selection
   algorithm, EMPTY-tier problems have the highest priority (knowledge_tier=0, no penalty).
   The problem is genuinely unexplored at the formal research level.

3. **Domain diversity**: The three most recent seeker selections were all combinatorics and
   graph theory. This problem is real analysis/calculus — an under-represented domain that
   broadens the active research portfolio.

4. **Tractability 7**: Both MVT and FTC have strong Mathlib formalizations. The challenge is
   *structural* — finding the cleanest proof that makes the MVT → FTC logical dependency
   explicit in Lean 4 — rather than requiring new mathematical content. Well-suited for
   autonomous research.

## Rejection Summary

- **Candidates considered**: 15
- **Candidates rejected**: 14
  - `unit-distance-independence-oq-02` (score 78): rejected — selected twice in last 3 seeker
    runs; diversity penalty applied
  - `prime-gap-bounds-oq-03` (score 77): rejected — selected earlier today; same-day repeat
  - `erdos-szekeres-oq-01` (score 76): rejected — selected in recent seeker run; diversity
    penalty (combinatorics)
  - `vietas-formulas-oq-02` (score 76): lower tie-break (algebra domain crowded)
  - `taylor-theorem-oq-02` (score 76): lower tie-break (analysis, but lower priority than MVT)
  - `euler-identity-oq-01-oq-04` (score 76): lower tie-break
  - Remaining 8 candidates: composite scores 75 or below
- **Confidence**: high — rejection reasons are unambiguous; score spread between this and the
  next unrejected candidate is clear

## Related Gallery Proofs

- `mean-value-theorem`: base MVT formalization (source proof)
- `mean-value-theorem-oq-02`: Taylor's Theorem with Lagrange Remainder (sibling OQ)
- `mean-value-theorem-oq-03`: Vector-Valued Mean Value Inequality (sibling OQ)
- `fundamental-theorem-calculus-oq-01-incomplete-01`: Lebesgue FTC (related in-progress)

## Suggested First Steps

1. **OBSERVE**: Survey Mathlib's `MeasureTheory.Integral.FundThmCalculus` and
   `Analysis.Calculus.MeanValue`. Identify the existing MVT statement and where (if anywhere)
   it appears in the FTC derivation chain. Check `proofs/Proofs/MeanValueTheorem.lean` for
   the current Lean formalization.

2. **ORIENT**: Check `src/data/proofs/mean-value-theorem/meta.json` and
   `mean-value-theorem-oq-02/` for existing proof structure and annotations. Determine which
   MVT variant (Lagrange, Cauchy, integral form) gives the cleanest path to FTC Part 1
   (derivative → integral formula) and Part 2 (continuity + integrability → antiderivative).

3. **DECIDE**: Select the approach — likely `intervalIntegral.integral_eq_sub_of_hasDerivAt`
   as the bridge, with MVT supplying the key estimate. Formalize the structural proof that
   makes this dependency explicit rather than implicit.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 1210 |
| Completed | 546 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

Pool is at minimum threshold (15 available = configured minimum). All 15 available problems
have initialized workspaces. Four researchers have active claims.

- **Pool depth**: borderline — at minimum threshold with no buffer
- **Recommendation**: Pool will drop below threshold when the next researcher claims a problem.
  Monitor closely; replenish with high-quality stale in-progress candidates (e.g.,
  `infinitude-primes-oq-03` sig=8 tract=8, `shannon-channel-coding-oq-04` sig=8 tract=7,
  `schauder-fixed-point-oq-02` sig=8 tract=7) once available count drops to 12–13.
- **Next refresh recommended**: within 1–2 researcher claim cycles
