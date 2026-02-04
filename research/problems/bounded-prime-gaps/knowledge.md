# Knowledge Base: bounded-prime-gaps

## Problem Summary

Prove that there are infinitely many prime gaps bounded by some constant (Zhang/Polymath result).

## Current State

**Status**: SURVEYED (upgraded from SKIPPED)

### Previous Assessment
Previously marked SKIPPED due to sieve theory infrastructure gap. However, meaningful formalization
work is possible without proving the theorem itself.

### What Was Built (2026-01-27)

**New file**: `proofs/Proofs/BoundedPrimeGaps.lean` (~370 lines)

#### Definitions
- `IsAdmissible`: Formal definition of admissible k-tuples (the combinatorial core of Zhang/Maynard-Tao)
- `DicksonConjecture`: Formal statement of the Dickson conjecture for admissible tuples
- `MaynardTaoDensity`: Formal statement of the Maynard-Tao density result
- `nthPrime`, `primeGap`: Basic prime gap infrastructure

#### Proved Theorems (no sorries, 0 sorry count)
1. `admissible_empty`: Empty set is admissible
2. `admissible_singleton`: Singleton sets are admissible
3. `admissible_subset`: Subsets of admissible sets are admissible
4. `admissible_of_card_lt_two`: Small sets are automatically admissible
5. `admissible_twin`: {0, 2} is admissible (twin prime tuple)
6. `admissible_triple_0_2_6`: {0, 2, 6} is admissible
7. `admissible_triple_0_4_6`: {0, 4, 6} is admissible
8. `admissible_quadruple_0_2_6_8`: {0, 2, 6, 8} is admissible (prime quadruplet)
9. `not_admissible_0_1_2`: {0, 1, 2} is NOT admissible (covers all residues mod 3)
10. `not_admissible_0_1`: {0, 1} is NOT admissible (covers all residues mod 2)
11. `infinitely_many_small_gaps`: From Polymath axiom
12. `liminf_prime_gaps_finite`: liminf of prime gaps <= 246
13. `bounded_intervals_k_primes`: From Maynard-Tao axiom
14. `maynard_tao_implies_twin_primes`: Maynard-Tao density for {0,2} implies twin prime conjecture
15. `nthPrime_prime`: The nth prime is prime
16. `nthPrime_strictMono`: Primes are strictly increasing
17. `primeGap_pos`: Prime gaps are positive
18. `primeGap_even`: Prime gaps for n >= 1 are even

#### Axioms (deep results, not provable from Mathlib)
1. `zhang_bounded_gaps_70M`: Zhang's original bound (2013)
2. `polymath_bounded_gaps_246`: Polymath 8b optimization (2014)
3. `maynard_tao_m_tuples`: Maynard-Tao generalization to m-tuples (2015)
4. `bounded_gaps_conditional_EH`: Conditional result assuming Elliott-Halberstam
5. `exists_admissible_50_tuple_246`: Existence of Polymath's specific admissible tuple

### Key Insights
- Admissible tuples are the right abstraction for bounded gaps work
- The formal definition (for all p prime, |image mod p| < p) is clean and computable for small examples
- `decide` handles small prime verification beautifully in Lean 4
- The connection between Maynard-Tao density and twin primes is a clean formal argument
- Not all pairs are admissible (e.g., {0,1} covers all residues mod 2)
- Even prime gaps (for n >= 1) follows from both p_n, p_{n+1} being odd primes

### What Would Be Needed for Full Proof
1. Selberg sieve formalization (major infrastructure)
2. GPY sieve (Goldston-Pintz-Yildirim)
3. Bombieri-Vinogradov theorem
4. Zhang's improvements to GPY
5. Polymath8 optimizations

### Related Work
- `PrimeGapBounds.lean` - Bertrand-based gap bounds
- `Erdos5PrimeGaps.lean` - Prime gap limit points (uses similar nthPrime/primeGap)
- `TwinPrimes.lean` - Twin prime structure

## Session Log

### Backfill Session (2026-01-01)
**Mode**: BACKFILL - Skipped problem documentation

### Research Session (2026-01-27)
**Mode**: FRESH (researcher-1)
**Decision**: DEEP DIVE - Build admissible tuple framework
**Outcome**: Created comprehensive formalization with 18 proved theorems, 5 axioms, 0 sorries
**Status upgraded**: SKIPPED -> SURVEYED (meaningful infrastructure built)
