# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 17 available, 498 in-progress, 1233 completed

## Selected Problem

- **ID**: `prime-gap-bounds-oq-03`
- **Name**: Connect the exponential bound to Chebyshev functions theta(x) and psi(x)
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available
- **Composite Score**: 77 (tied with `mean-value-theorem-oq-04`)

## Selection Rationale

1. **Bridges two verified gallery proofs**: `PrimeGapBounds` (p_n ≤ 2^(n+1)) and
   `ChebyshevBounds` (θ(n) ≤ n·log 4) are both complete; this problem formalizes
   the classical connection between them.
2. **EMPTY knowledge tier**: No prior research attempts — highest priority tier.
3. **PNT infrastructure**: Defining ψ(x) and proving θ(x) ≤ ψ(x) is a necessary
   step toward any Prime Number Theorem formalization in the gallery.
4. **Tie-break**: Both `prime-gap-bounds-oq-03` and `mean-value-theorem-oq-04` scored
   77. Selected prime-gap-bounds-oq-03 for its more concrete mathematical structure
   (bridging two specific existing proofs with a classical analytic number theory result).

## Rejection Summary

- **Candidates considered**: 17
- **Candidates rejected**: 16
  - `derangements-convergence-oq-03`: MODERATE knowledge (81 lines) → composite -1913, deprioritized
  - `central-limit-theorem-oq-02-oq-02`: template-only knowledge file, score 76 (below top)
  - `mean-value-theorem-oq-04`: Score 77 (tied), rejected on tie-break — less concrete bridging opportunity
  - All others: score ≤ 76 (lower tractability or significance)
- **Confidence**: medium (tied top candidates; selection based on structural assessment)

## Related Gallery Proofs

- `prime-gap-bounds`: Source of `nth_prime_le_two_pow_succ` — the exponential bound
- `chebyshev-bounds`: Source of `chebyshevTheta` — the theta function to connect
- `bounded-prime-gaps`: Related prime counting infrastructure
- `prime-number-theorem-oq-03`: Downstream target — ψ definition is PNT infrastructure

## Suggested First Steps

1. **OBSERVE**: Check if `Mathlib.NumberTheory.vonMangoldt` (Λ function) exists;
   read all theorem signatures in `ChebyshevBounds.lean` and `PrimeGapBounds.lean`.
2. **ORIENT**: Prove `theta_lower_from_exp_bound` — the direct bridge from
   `nth_prime_le_two_pow_succ` to a θ lower bound on 2^n.
3. **DECIDE**: Determine whether to define ψ via von Mangoldt (if Mathlib has it)
   or via `Nat.factorization`; then prove `chebyshevTheta_le_psi`.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 17 |
| In Progress | 498 |
| Completed | 1233 |
| Blocked | 1 |
| **Total** | **1749** |

## Candidate Pool Health

Pool is healthy at 17 available problems.

- Pool depth: adequate (17 available ≥ threshold of 5)
- Recommendation: Pool healthy — no immediate refresh needed
- Next refresh recommended: when available count drops below 5
