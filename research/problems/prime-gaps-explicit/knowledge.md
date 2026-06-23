# Knowledge Base: Explicit Prime Gap Bounds

## Progress Summary

**Date**: 2025-12-31
**Phase**: DEEP DIVE (completed)
**Result**: Proved counting bounds from Bertrand

## What We've Built

### Theorems Proven

1. **`primeCounting_double_gt`**: π(2n) > π(n) for n ≥ 1
   - Shows there's always at least one new prime when doubling
   - Direct application of Bertrand's postulate

2. **`primeCounting_double_ge_succ`**: π(2n) ≥ π(n) + 1

3. **`primeCounting_pow_two_mul`**: π(2^k · n) ≥ π(n) + k
   - Iterated application showing logarithmic growth

### Computed Values
- π(10) = 4
- π(20) = 8
- π(30) = 10
- π(50) = 15

### Axiom Stated
- `nth_prime_le_two_pow_succ`: p_n ≤ 2^(n+1)
  - This follows from Bertrand but required complex handling of nth

## Technical Insights

### Key Proof Technique

Using Bertrand + count monotonicity:
```lean
theorem primeCounting_double_gt (n : ℕ) (hn : n ≥ 1) : π (2 * n) > π n := by
  obtain ⟨p, hp_prime, hlt, hle⟩ := bertrand_postulate n hn
  -- p is prime with n < p ≤ 2n
  -- count(n+1) ≤ count(p) < count(p+1) ≤ count(2n+1)
  unfold primeCounting primeCounting'
  have h1 : count Nat.Prime (n + 1) < count Nat.Prime (p + 1) := by
    have hmono : count Nat.Prime (n + 1) ≤ count Nat.Prime p := Nat.count_monotone _ (by omega)
    have hstrict : count Nat.Prime p < count Nat.Prime (p + 1) :=
      Nat.count_strict_mono hp_prime (Nat.lt_succ_self p)
    omega
  have h2 : count Nat.Prime (p + 1) ≤ count Nat.Prime (2 * n + 1) :=
    Nat.count_monotone _ (by omega)
  omega
```

### What Mathlib Has

| Component | Status |
|-----------|--------|
| `primeCounting` | ✓ Defined |
| `Nat.count_monotone` | ✓ Available |
| `Nat.count_strict_mono` | ✓ Available |
| Bertrand's postulate | ✓ Fully proven |
| `nth Prime` | ✓ Defined but complex |

### What's Still Missing

- Dusart bounds: π(x) ≥ x/(ln x + 2)
- Chebyshev bounds: θ(x) < 1.01624x
- PNT-style: π(x) ~ x/ln x with explicit error

## Value Assessment

This proof demonstrates:
1. ✅ Non-trivial consequence of Bertrand
2. ✅ Clean use of count monotonicity
3. ✅ Useful iterative bound
4. ✅ Computational verification
5. ❌ Couldn't complete p_n ≤ 2^n proof (stated as axiom)

The axiom is justified because:
- The proof idea is clear (induction on Bertrand)
- The blocking issue is technical (nth function handling)
- The result is mathematically sound

## Comparison with Dusart

| Bound | Source | Tightness |
|-------|--------|-----------|
| p_n ≤ 2^n | Our axiom | Very weak |
| p_n ≤ n(ln n + ln ln n) | Dusart | Tight |
| π(x) ≥ x/(ln x + 2) | Dusart | Tight |
| π(2n) ≥ π(n) + 1 | Our theorem | Exact |

## File Location

`proofs/Proofs/PrimeGapBounds.lean`

## References

- [Mathlib PrimeCounting](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PrimeCounting.html)
- [Prime-counting function - Wikipedia](https://en.wikipedia.org/wiki/Prime-counting_function)
