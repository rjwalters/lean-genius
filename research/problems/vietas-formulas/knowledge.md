# Knowledge Base: vietas-formulas

## Problem Summary

Formalize Vieta's formulas relating polynomial coefficients to sums and products of roots.

## Current State

**Status**: COMPLETED
**Proof File**: `proofs/Proofs/VietasFormulas.lean` (180 lines)
**Sorries**: 0

### What's Proven

1. **Quadratic Case**
   - `vieta_quadratic` - Uses Mathlib's `vieta_formula_quadratic`

2. **General Case**
   - `vieta_polynomial_coeff` - Coefficients = elementary symmetric functions of roots
   - `vieta_monic_coeff` - Simplified for monic polynomials

3. **Explicit Formulas**
   - `monic_quadratic_vieta` - (x-r1)(x-r2) = x^2 - (r1+r2)x + r1*r2
   - `monic_cubic_vieta` - Cubic expansion

4. **Examples**
   - x^2 - 5x + 6 = 0 roots 2, 3
   - x^3 - 6x^2 + 11x - 6 = 0 roots 1, 2, 3

### Key Insight

Alternating signs in Vieta come from expanding (x-r1)(x-r2)...(x-rn).

### Mathlib Usage

`Polynomial.Vieta`, `vieta_formula_quadratic`, `Multiset.esymm`

## Session Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - Problem was completed without knowledge documentation

**Quality Assessment**: MEDIUM-HIGH - Good Mathlib integration
