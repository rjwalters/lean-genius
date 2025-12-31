# Knowledge Base: weak-goldbach

## Progress Summary

**Date**: 2025-12-31
**Phase**: ACT
**Milestone achieved**: Initial formalization with small case verification

## What We've Built

### Formal Definitions (proven)
- `IsSumOfThreePrimes (n : ℕ)` - predicate for n = p + q + r
- `WeakGoldbachConjecture` - formal statement of the conjecture

### Verified Cases (proven in Lean)
- 7 = 2 + 2 + 3 ✓
- 9 = 3 + 3 + 3 ✓
- 11 = 3 + 3 + 5 ✓
- 13 = 3 + 3 + 7 ✓
- 15 = 3 + 5 + 7 ✓
- 17 = 5 + 5 + 7 ✓
- 19 = 3 + 5 + 11 ✓
- 21 = 7 + 7 + 7 ✓

### Axioms Stated
- `vinogradov_ternary_goldbach`: ∃ N₀, ∀ n > N₀, odd n → sum of 3 primes
- `helfgott_weak_goldbach`: Full conjecture (every odd n > 5)

## Technical Insights

### Proving Small Cases

Pattern that works:
```lean
theorem goldbach_N : IsSumOfThreePrimes N := by
  use p, q, r
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide
```

For small primes (2, 3), use `Nat.prime_two`, `Nat.prime_three`.
For larger primes, `decide` computes primality.

### Mathlib Dependencies
- `Mathlib.Data.Nat.Prime.Basic` - `Nat.Prime`, `Nat.prime_two`, `Nat.prime_three`
- `Mathlib.Tactic` - `decide`, `refine`

### What Mathlib Lacks
- Circle method infrastructure
- L-function machinery for primes
- Exponential sum bounds
- Explicit prime-counting bounds (Dusart-type)

## Next Steps (Increasing Difficulty)

1. **Extend verification** to n ≤ 100 (automation needed)
2. **Prove for n ≡ 3 (mod 6)** - all such n have 3 + 3 + (n-6) as candidate
3. **Formalize Vinogradov's existential** with explicit (huge) bound
4. **Circle method basics** - would need significant Mathlib development

## Partial Progress Value

Even without full proof, this formalization:
- Provides canonical Lean statement of the conjecture
- Demonstrates verification approach
- Documents what Mathlib needs for full proof
- Could be extended incrementally

## File Location

`proofs/Proofs/WeakGoldbach.lean`
