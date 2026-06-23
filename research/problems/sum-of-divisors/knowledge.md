# Knowledge Base: Sum of Divisors Properties

## Status: Covered Elsewhere

This problem is marked **SKIPPED** because related content already exists in the proof gallery.

## What We Have

### In PerfectNumbers.lean (~317 lines)

The `PerfectNumbers.lean` file formalizes the sum-of-divisors function and its properties:

**Definitions**:
- Uses Mathlib's `Nat.divisors` and summation

**Key Theorems**:
- `sigma_prime_power`: σ(p^k) = (p^{k+1} - 1)/(p - 1)
- `sigma_two_power`: σ(2^k) = 2^{k+1} - 1
- `perfect_iff_sigma_2n`: n is perfect ⟺ σ(n) = 2n
- `euclid_euler_perfect`: Euclid-Euler theorem for even perfect numbers

**Concrete Examples**:
- 6 is perfect (1 + 2 + 3 = 6)
- 28 is perfect (1 + 2 + 4 + 7 + 14 = 28)
- 496 is perfect
- 8128 is perfect

### In Mathlib

The divisor sum function is `Nat.sigma` in Mathlib:
- `Nat.sigma 1 n` = σ(n) = sum of divisors of n
- `Nat.sigma k n` = σ_k(n) = sum of k-th powers of divisors

## Why This Problem Is Marked Skipped

The original problem statement was general "sum of divisors properties" without specific goals. Since our PerfectNumbers.lean already covers:
1. The σ function behavior
2. Perfect number characterization
3. Euclid-Euler theorem

...there's no clear additional target that would justify a separate research track.

## Related Open Problems

If we wanted to extend this work, possible directions include:

### 1. Odd Perfect Numbers
**Status**: Open for 2000+ years!

No odd perfect number is known. If one exists, it must:
- Be greater than 10^1500
- Have at least 101 prime factors (counting multiplicity)
- Have a special form involving prime powers

### 2. Mersenne Primes Connection

A number 2^{p-1}(2^p - 1) is perfect iff 2^p - 1 is prime (Mersenne prime).

Known: M_2, M_3, M_5, M_7, M_13, M_17, M_19, M_31, ...

### 3. Aliquot Sequences

For a number n, define a(n) = σ(n) - n (sum of proper divisors).
The sequence n → a(n) → a(a(n)) → ...

- Perfect numbers: fixed points
- Amicable numbers: 2-cycles
- Sociable numbers: longer cycles
- Open: Does every sequence eventually cycle or reach 1?

### 4. Abundancy Index

The abundancy index σ(n)/n measures how "abundant" n is:
- σ(n)/n < 2: deficient
- σ(n)/n = 2: perfect
- σ(n)/n > 2: abundant

Open questions about the distribution of abundancy.

## References

- Dickson, L.E. (1919). "History of the Theory of Numbers" Vol I
- Guy, R.K. (2004). "Unsolved Problems in Number Theory" Section B
- Ochem, P., Rao, M. (2012). "Odd perfect numbers are greater than 10^1500"

## Scouting Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - Related work exists in PerfectNumbers.lean

**Decision**: Mark as SKIPPED since core σ function properties are already formalized. No specific open problem identified that would benefit from additional research effort.

**If Revisiting**: Consider odd perfect number bounds or aliquot sequence properties as potential targets.
