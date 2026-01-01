# Knowledge Base: mobius-inversion

## Problem Summary

Formalize Mobius inversion formula.

## Current State

**Status**: SKIPPED (IN MATHLIB)

### Why Skipped

Already in Mathlib with full proofs:
- `sum_eq_iff_sum_mul_moebius_eq` (for rings)
- `sum_eq_iff_sum_smul_moebius_eq` (for additive groups)  
- `prod_eq_iff_prod_pow_moebius_eq` (for multiplicative)
- `coe_zeta_mul_moebius` proves ζ*μ=1

### What's in Mathlib

```lean
-- The core inversion theorem
theorem sum_eq_iff_sum_mul_moebius_eq [AddCommGroup R] [Module R R]
    (f g : ℕ → R) : 
    (∀ n, g n = ∑ d ∈ n.divisors, f d) ↔ 
    (∀ n, f n = ∑ d ∈ n.divisors, μ d • g (n/d))
```

This problem was marked "skipped" but is actually IN MATHLIB.

## Session Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - This is complete in Mathlib, no work needed
