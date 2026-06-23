# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 27 available, 559 in-progress, 1406 completed

## Selected Problem

- **ID**: sqrt2-minpoly-oq-02
- **Name**: Minimal Polynomial of k-th Roots: minpoly ℚ (n^(1/k)) = Xᵏ - n via Eisenstein
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 8/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 87
- **Status**: available

## Selection Rationale

1. **Highest composite score among unselected problems** (87): tractability 8 drives the
   ranking. The proof strategy is known — Eisenstein criterion + `minpoly.eq_of_irreducible_of_monic`
   — and Mathlib has all required ingredients. This problem can realistically be closed.

2. **EMPTY knowledge tier**: No research has been done yet, making any progress high-value.
   The scratch space is clean.

3. **Direct continuation of gallery work**: `sqrt2-minpoly` (verified) proves the k=2, n=2
   case. This generalizes to all (n, k) satisfying the Eisenstein prime condition. The
   sibling problem `sqrt2-minpoly-oq-01` handles the √n case (k=2 general); this handles
   the k-th root case. Both are natural extensions — not shallow specializations.

4. **Diversity**: Recent selections covered analysis (cauchy-schwarz), number theory/algorithms
   (chinese-remainder-constructive), and graph theory (erdos-73). Algebraic number theory
   is an appropriate new domain entry in the current cycle.

## Rejection Summary

- **Candidates considered**: 27 available (excluding 2 with active claims)
- **Top 13 already have selection reports** from the April 23 batch — not re-selected
- **`erdos-476-oq-05-wip-01`**: Skipped — active claim lock exists
- **`lebesgue-measure-oq-06`**: Skipped — active claim + RICH knowledge (27 items, score −2932)
- **`sophie-germain-oq-01`, `twin-primes-special-oq-01`, `weak-goldbach-oq-01`**: Open
  conjectures with tractability 2 — not suitable for autonomous research
- **`szemeredi-full-oq-01`** (sig=9, tract=4, score=49): High significance but low
  tractability pulls it below `sqrt2-minpoly-oq-02`
- **Confidence**: high — score gap between #1 (87) and #2 (67) is 20 points

## Related Gallery Proofs

- `sqrt2-minpoly`: Direct predecessor — minpoly ℚ √2 = X² - 2; same proof architecture
- `cube-root-2-irrational`: Related irrationality result using degree argument
- `sqrt2-irrational`: Companion proof using minimal polynomial degree

## Suggested First Steps

1. **OBSERVE**: Check `Mathlib.RingTheory.Eisenstein.Basic` for
   `Polynomial.irreducible_of_eisenstein_criterion` — confirm it covers arbitrary degree k.
   Read the existing `sqrt2-minpoly` Lean source to extract the template proof structure.

2. **ORIENT**: Identify the gap: expressing `Real.rpow (n : ℝ) (1/k : ℝ)` so that Lean
   can verify `aeval (n^(1/k)) (X^k - C n) = 0`. The `Real.rpow_natCast` lemma family
   and `Real.rpow_mul` may bridge this. Check if `NNReal.rpow` is cleaner.

3. **DECIDE**: Start with a concrete stepping stone — prove minpoly ℚ (∜2) = X⁴ - 2
   (n=2, k=4) before generalizing. If `Real.rpow` is too cumbersome, consider using
   `Polynomial.roots` over an algebraic closure, or work with `AdjoinRoot (X^k - C n)`.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 27 |
| In Progress | 559 |
| Completed | 1406 |
| Surveyed | 0 |
| Skipped | 0 |
| Blocked | 1 |

## Candidate Pool Health

Pool is healthy and well above threshold.

- **Pool depth**: adequate (27 available vs threshold 15)
- **Recommendation**: Pool healthy — no replenishment needed
- **Next refresh recommended**: when available drops below 15
