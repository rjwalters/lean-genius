# Problem: Can the Truncation Method Be Generalized?

**ID**: divisibility-by-3-oq-01-oq-01
**Status**: COMPLETE
**Tier**: B
**Significance**: 6/10 | **Tractability**: 6/10

## Problem Statement

Can the truncation method (remove last digit, add/subtract a multiple of it) be
generalized to a single parametric theorem covering all divisors coprime to 10?

**Answer: YES.** Two general theorems completely characterize all truncation rules.

## Proof Location

**File**: `proofs/Proofs/DivisibilityTruncationGeneral.lean`
**Gallery**: `src/data/proofs/divisibility-truncation-general/`
**Status**: 0 sorries, 0 axioms, builds in Docker (Mathlib v4.26.0, 3058 jobs)

## Key Mathematical Content

### Positive Osculator Theorem
For d coprime to 10 and d | 10c - 1:
```
d | n  ↔  d | (n/10 + c·(n%10))
```
Examples: d=13 c=4 (39=3·13), d=19 c=2 (19=1·19), d=3 c=1 (9=3·3)

### Negative Osculator Theorem
For d coprime to 10 and d | 10c + 1:
```
d | n  ↔  d | (n/10 - c·(n%10))
```
Examples: d=7 c=2 (21=3·7), d=11 c=1 (11=1·11), d=17 c=5 (51=3·17)

## Session 2026-02-21 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Identified the algebraic core: `10*(n/10 + c*(n%10)) = n + (10c-1)*(n%10)`
2. Proved this via `linear_combination -hdiv` where `hdiv : n = 10*(n/10) + n%10`
3. Used `IsCoprime.dvd_of_dvd_mul_left` to transfer divisibility through 10
4. Created both positive and negative osculator variants
5. Proved 11 corollaries for d ∈ {3,7,9,11,13,17,19,23,29,31,37}
6. Built successfully in Docker (3058 jobs, 2.1s for target)

### Key Insights

- The key algebraic identity is: `10*(q + cr) = n + (10c-1)*r` where n=10q+r
- `linear_combination -hdiv` elegantly proves this identity
- `IsCoprime.dvd_of_dvd_mul_left` is the critical Mathlib lemma
- The positive osculator c = (10⁻¹ mod d), negative c = ((-10)⁻¹ mod d)
- Every d coprime to 10 has both positive and negative osculators
- Type annotation: use `(d : ℤ) ∣ n` (not `d ∣ n`) to avoid ℕ/ℤ coercion issues

### Files Modified

- `proofs/Proofs/DivisibilityTruncationGeneral.lean` (created, 285 lines)
- `src/data/proofs/divisibility-truncation-general/` (gallery entry created)

### Next Steps

None - proof is complete. Extension ideas:
- Unified single theorem with signed c ∈ ℤ (can subsume both cases)
- Extension to multi-digit truncation (see DivisibilityByThreeOQ02.lean)
- Extension to other bases
