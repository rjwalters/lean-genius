# Knowledge Base: Twin Primes in Special Forms

## Progress Summary

**Date**: 2025-12-31
**Phase**: DEEP DIVE (completed)
**Result**: Successful - proved structure theorem

## What We've Built

### Formal Definitions
- `IsTwinPrimePair p` - p and p+2 are both prime
- `TwinPrimeConjecture` - infinitely many twin prime pairs exist

### Verified Examples (in Lean)
- (3, 5) ✓
- (5, 7) ✓
- (11, 13) ✓
- (17, 19) ✓
- (29, 31) ✓
- (41, 43) ✓

### Theorems Proven

1. **`prime_mod_six`**: For p > 3 prime, p ≡ 1 or 5 (mod 6)

2. **`twin_prime_mod_six`** (Main result):
   For p > 3, if (p, p+2) are both prime, then p ≡ 5 (mod 6)

3. **`twin_prime_form`** (Corollary):
   Twin primes > 3 have the form (6k-1, 6k+1) for some k ≥ 1

4. **Non-twin proofs**: 0, 1, 2 cannot start twin prime pairs

### Axiom Stated
- `twin_prime_conjecture` - the unsolved conjecture

## Technical Insights

### The Proof Strategy

The structure theorem follows from modular arithmetic:

1. All primes > 3 satisfy p ≡ 1 or 5 (mod 6)
2. If p ≡ 1 (mod 6), then p + 2 ≡ 3 (mod 6)
3. But 3 | (p + 2) means p + 2 can't be prime (unless = 3)
4. Therefore p ≡ 5 (mod 6)

### Key Lemmas Used
- `Nat.Prime.eq_one_or_self_of_dvd` - if p prime and d | p, then d = 1 or d = p
- `Nat.dvd_of_mod_eq_zero` - divisibility from mod = 0

### Proof Pattern for Divisibility Exclusion
```lean
theorem prime_gt_three_not_div_three (p : ℕ) (hp : Nat.Prime p) (h3 : p > 3) : ¬ 3 ∣ p := by
  intro hdiv
  have h3' : 3 = p := (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdiv).resolve_left (by decide)
  omega
```

## What Mathlib Has vs. Lacks

| Component | Status |
|-----------|--------|
| `Nat.Prime` | ✓ In Mathlib |
| `Nat.Prime.eq_one_or_self_of_dvd` | ✓ In Mathlib |
| Modular arithmetic | ✓ In Mathlib |
| `Bertrand.exists_prime_lt_and_le_two_mul` | ✓ In Mathlib |
| Twin prime definition | ✗ Defined by us |
| Twin prime structure theorem | ✗ Proved by us |
| Twin prime conjecture | ✗ Unsolved |

## Value Assessment

This proof is valuable because:
1. **Non-trivial structure theorem** - genuinely interesting result
2. **Clean modular arithmetic** - showcases proof technique
3. **Complete examples** - verified 6 twin prime pairs
4. **Proper formalization** - twin prime definition for future use
5. **Documents the unsolved** - conjecture stated as axiom

## Comparison: SURVEY vs DEEP DIVE

| Aspect | If we did SURVEY | What we did (DEEP DIVE) |
|--------|------------------|-------------------------|
| Definition | ✓ | ✓ |
| Examples | Maybe 1-2 | 6 verified |
| Structure theorem | Stated only | **Fully proved** |
| Time spent | ~30 min | ~1 hour |
| Mathematical value | Low | **Medium** |

The DEEP DIVE was worthwhile because the structure theorem is a real result, not just bookkeeping.

## File Location

`proofs/Proofs/TwinPrimes.lean`

## References

- [Twin prime conjecture - Wikipedia](https://en.wikipedia.org/wiki/Twin_prime)
- [Google DeepMind Formal Conjectures](https://reservoir.lean-lang.org/@google-deepmind/formal_conjectures)
