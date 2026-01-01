# Knowledge Base: bounded-prime-gaps

## Problem Summary

Prove that there are infinitely many prime gaps bounded by some constant (Zhang/Polymath result).

## Current State

**Status**: SKIPPED

### Why Skipped

Requires sieve theory (Selberg sieve, GPY sieve) not in Mathlib. The Bombieri-Vinogradov theorem (equidistribution of primes in arithmetic progressions) is missing. This would be a multi-year effort.

### What Would Be Needed

1. Selberg sieve formalization
2. GPY sieve (Goldston-Pintz-Yildirim)
3. Bombieri-Vinogradov theorem
4. Zhang's improvements to GPY
5. Polymath8 optimizations (gap bound of 246)

### Related Work

- `PrimeGapBounds.lean` - Has simpler gap bounds (Bertrand, Chebyshev-type)
- Mathlib has basic sieve theory but not the heavy machinery needed here

## Session Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - Skipped problem documentation
