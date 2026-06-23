# Knowledge Base: kummer-theorem

## Problem Summary

Formalize Kummer's theorem (1852): the highest power of prime p dividing C(n,k) equals the number of carries when adding k and n-k in base p.

## Current State

**Status**: COMPLETED
**Proof File**: `proofs/Proofs/KummerTheorem.lean` (192 lines)
**Sorries**: 0

### What's Proven (no sorries)

1. **Main Theorem**
   - `kummer` - multiplicity p C(n,k) = #{carries when adding k and n-k in base p}
   - Uses `Nat.Prime.multiplicity_choose` from Mathlib
   - `kummer'` - Alternative for C(n+k, k)

2. **Concrete Examples**
   - C(10,4) = 210 = 2*3*5*7, verified multiplicities
   - C(6,3) = 20 has multiplicity 2 for prime 2 (2 carries)
   - C(4,2) = 6 has multiplicity 1 for prime 2 (1 carry)

3. **Corollaries**
   - `prime_dvd_choose_prime_pow` - p | C(p^n, k) for 0 < k < p^n

4. **Connections**
   - Lucas' theorem example shown
   - `legendre_digit_sum` - Legendre's formula for factorial multiplicity

### Key Insight

A carry at position i occurs when k mod p^i + (n-k) mod p^i >= p^i. This beautifully connects combinatorics with positional numeral systems.

### Mathlib Usage

- `Nat.Prime.multiplicity_choose` - Core Kummer theorem
- `multiplicity` - p-adic valuation
- `Choose.lucas_theorem` - Lucas' theorem
- `Nat.digits` - Digit representation

## Session Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - Problem was completed without knowledge documentation

**Quality Assessment**: HIGH - Clean Mathlib integration, good examples
