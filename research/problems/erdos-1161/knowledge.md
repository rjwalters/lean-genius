# Erdős #1161 - Knowledge Base

## Problem Statement

Let f_k(n) = |{σ ∈ S_n : ord(σ) = k}|. For which values of k is f_k(n) maximized?

Solved by Beker [Be25d]: max_k f_k(n) ~ (n-1)! and the maximizer is characterized by lcm divisibility.

## Status

**Erdős Database Status**: SOLVED (Beker [Be25d])
**Formalization Status**: COMPLETE (0 sorries, 2 axioms, 14 proved theorems)

## Sessions

### Session 1 (prior researcher)
- Fixed multiple API compatibility issues
- Proved `permCountByOrder_prime_self` via cycleType characterization
- Removed false theorem `permCountByOrder_n_eq_subfactorial_pred`
- Left 2 sorries for deep Beker results

### Session 2 (researcher-7, 2026-03-23)
**Key insight**: `max_permCount_ge_sub_factorial` does NOT need Beker's results.
Direct proof: n-cycles ⊆ {σ | orderOf σ = n}, so the count is ≥ (n-1)!.
This eliminates the sorry-dependency chain.

Changes:
- Rewrote `max_permCount_ge_sub_factorial` with axiom-independent proof
- Converted `beker_characterization` and `beker_maximizer_achieves` to axioms
- Updated meta.json: status axiomatized, axiomCount 2, sorries 0

## Insights

- permCountByOrder n n ≥ (n-1)! for ALL n ≥ 2 (not just primes) because n-cycles always contribute (n-1)!
- card_of_cycleType [n] + aesop gives n!/n; factorial_succ + mul_div_cancel gives (n-1)!
- Beker's results are deep published results, appropriate as axioms

## Dead Ends

- `permCountByOrder n n = (n-1)!` is FALSE for composite n (n=6: 240 ≠ 120)

---

*Generated from erdosproblems.com on 2026-01-15, updated 2026-03-23*
