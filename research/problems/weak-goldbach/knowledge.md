# Knowledge Base: weak-goldbach

## Progress Summary

**Date**: 2025-12-31
**Phase**: ACT
**Milestone achieved**: Extended verification to n ≤ 51 (23 odd cases)

## What We've Built

### Formal Definitions (proven)
- `IsSumOfThreePrimes (n : ℕ)` - predicate for n = p + q + r
- `WeakGoldbachConjecture` - formal statement of the conjecture

### Verified Cases (proven in Lean)
All odd n from 7 to 51:
- 7 = 2 + 2 + 3 ✓
- 9 = 3 + 3 + 3 ✓
- 11 = 3 + 3 + 5 ✓
- 13 = 3 + 3 + 7 ✓
- 15 = 3 + 5 + 7 ✓
- 17 = 5 + 5 + 7 ✓
- 19 = 3 + 5 + 11 ✓
- 21 = 7 + 7 + 7 ✓
- 23 = 5 + 7 + 11 ✓
- 25 = 5 + 7 + 13 ✓
- 27 = 5 + 11 + 11 ✓
- 29 = 5 + 7 + 17 ✓
- 31 = 7 + 7 + 17 ✓
- 33 = 3 + 7 + 23 ✓
- 35 = 5 + 7 + 23 ✓
- 37 = 7 + 13 + 17 ✓
- 39 = 7 + 13 + 19 ✓
- 41 = 11 + 13 + 17 ✓
- 43 = 7 + 17 + 19 ✓
- 45 = 5 + 17 + 23 ✓
- 47 = 5 + 11 + 31 ✓
- 49 = 3 + 17 + 29 ✓
- 51 = 7 + 7 + 37 ✓

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

## Session Log

### 2025-12-31 Session 2

**What we did**:
- Literature search confirmed Helfgott's proof requires deep analytic number theory
- Extended verification from 8 cases (7-21) to 23 cases (7-51)
- Added 15 new verified decompositions with explicit witnesses

**Outcome**:
- All odd n from 7 to 51 now verified in Lean
- Pattern `refine ⟨?_, ?_, ?_, rfl⟩ <;> decide` continues to work well

**Next steps for future sessions**:
1. **Extend to n ≤ 101** - continue mechanical verification
2. **Try decidable instance** - could we build a `Decidable (IsSumOfThreePrimes n)` for computable verification?
3. **Structural theorem** - prove that every n can use 3 as one summand (reduces to binary Goldbach)

## Next Steps (Increasing Difficulty)

1. **Extend verification** to n ≤ 101 (15 more cases)
2. **Build decidable instance** for `IsSumOfThreePrimes` to enable `native_decide`
3. **Prove structural lemma**: n odd > 5 → ∃ even m, n = 3 + m (trivial but connects to binary Goldbach)
4. **Formalize Vinogradov bound** with explicit N₀ ≈ 10^1346
5. **Circle method basics** - would need significant Mathlib development

## Partial Progress Value

Even without full proof, this formalization:
- Provides canonical Lean statement of the conjecture
- Demonstrates verification approach for 23 cases
- Documents what Mathlib needs for full proof
- Could be extended incrementally

## File Location

`proofs/Proofs/WeakGoldbach.lean`
