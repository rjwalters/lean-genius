# Knowledge Base: Collatz for Structured Starting Values

## Progress Summary

**Date**: 2025-12-31
**Phase**: DEEP DIVE (completed)
**Result**: Successfully proved Collatz for powers of 2 and closure properties

## What We've Built

### Definitions

1. **Collatz function**
   ```lean
   def collatz (n : ℕ) : ℕ :=
     if n % 2 = 0 then n / 2 else 3 * n + 1
   ```

2. **Iteration and ReachesOne**
   ```lean
   def collatzIter (k : ℕ) (n : ℕ) : ℕ := collatz^[k] n

   def ReachesOne (n : ℕ) : Prop :=
     ∃ k : ℕ, collatzIter k n = 1
   ```

### Key Theorems Proven

| Theorem | Statement | Proof Technique |
|---------|-----------|-----------------|
| `collatz_two_mul` | collatz(2n) = n | Direct from mod definition |
| `collatz_pow_two` | 2^k reaches 1 in k steps | Induction on k |
| `pow_two_reaches_one` | 2^k reaches 1 | Corollary |
| `reaches_one_double` | n reaches 1 → 2n reaches 1 | One extra halving step |
| `reaches_one_pow_two_mul` | n reaches 1 → 2^m·n reaches 1 | Induction on m |

### Verified Values (by computation)

| n | Steps to 1 | Verification |
|---|-----------|--------------|
| 3 | 7 | native_decide |
| 5 | 5 | native_decide |
| 6 | 8 | native_decide |
| 7 | 16 | native_decide |
| 9 | 19 | native_decide |
| 27 | 111 | native_decide (famous!) |

## Technical Insights

### Key Proof Technique: Powers of 2

The core insight for powers of 2:
```lean
theorem collatz_pow_two (k : ℕ) (hk : k ≥ 1) : collatzIter k (2^k) = 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [collatzIter, collatz]  -- 2^1 = 2 → 1
    | succ m =>
      -- 2^(m+2) = 2 * 2^(m+1) → 2^(m+1) → ... → 1
      have h2 : 2^(m + 2) = 2 * 2^(m + 1) := by ring
      conv_lhs => rw [h2]
      rw [Function.iterate_succ_apply, collatz_two_mul]
      exact ih (by omega)
```

### Function.iterate API

Key lemmas for iteration:
- `Function.iterate_succ_apply`: f^[n+1] x = f^[n] (f x)
- `Function.iterate_succ_apply'`: f^[n+1] x = f (f^[n] x)

We used the first form which puts the new step at the end, allowing us to peel off the first halving.

### What Remains Hard

**2^n - 1 pattern**: These are all odd, so:
- 2^n - 1 → 3(2^n - 1) + 1 = 3·2^n - 2 = 2(3·2^(n-1) - 1)

The pattern doesn't simplify nicely like powers of 2. Would need:
- Careful case analysis
- Possibly a different invariant
- Or brute-force verification for small n

## Value Assessment

This proof is valuable because:

1. ✅ First Collatz formalization in our codebase
2. ✅ Non-trivial induction on iteration
3. ✅ Useful closure property (2x inheritance)
4. ✅ Computational verification of famous examples
5. ✅ Clean API for future work

## Comparison with Other Problems

| Problem | Difficulty | What We Proved |
|---------|-----------|----------------|
| Twin Primes | Medium | Mod 6 structure |
| Prime Gaps | Medium | π(2n) > π(n) |
| RH Consequences | Easy | Definitions + axioms |
| **Collatz** | Medium | Powers of 2 + closure |

Collatz was at a similar difficulty level to Twin Primes, with the induction on iteration being the key challenge.

## File Location

`proofs/Proofs/CollatzStructured.lean`

## References

- [Collatz conjecture - Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
- Lagarias, "The 3x+1 Problem and Its Generalizations" (1985)
- Tao, "Almost all orbits of the Collatz map attain almost bounded values" (2019)
