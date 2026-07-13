# Success Recap: cube-root-2-irrational

**Date**: 2025-12-30
**Approach**: approach-01 (Not-Integer via irrational_nrt_of_notint_nrt)
**Attempt**: 1
**Time to Success**: ~30 minutes (Fast Path)

## The Win

### What We Proved
```lean
theorem irrational_cbrt2 : Irrational ((2 : ℝ) ^ (1/3 : ℝ))
```

### Key Theorem/Tactic
The breakthrough came from: **`irrational_nrt_of_notint_nrt`** from `Mathlib.Data.Real.Irrational`

This theorem is simpler than the multiplicity-based approach mentioned in the problem description. It only requires proving:
1. `x ^ n = m` (integer)
2. `x` is not an integer

## Techniques That Worked

### Mathlib Resources Used
- **Primary theorem**: `irrational_nrt_of_notint_nrt` from `Mathlib.Data.Real.Irrational`
- **Supporting lemmas**:
  - `Real.rpow_natCast` — convert between rpow and ^
  - `Real.rpow_mul` — simplify (x^a)^b = x^(a*b)

### Tactic Patterns Discovered
```lean
-- Pattern: Power bounds for nlinarith
-- When to use: nlinarith fails on n^k expressions
-- Example:
have : n ^ 3 = n * n * n := by ring
rw [this]
nlinarith  -- Now works!
```

## For Future Problems

### If You See This Pattern Again
- **Problem shape**: "Prove m^(1/n) is irrational" for small integer m
- **Recommended approach**: Use `irrational_nrt_of_notint_nrt`, prove m is not perfect n-th power
- **Watch out for**: nlinarith doesn't handle powers, rewrite to products

### What We'd Do Differently
- Check `Mathlib.Data.Real.Irrational` first for any irrationality proof
- Use MATHLIB_SEARCH.md checklist
- Could have skipped ORIENT/DECIDE phases more explicitly (was implicit)

## Quick Stats

| Metric | Value |
|--------|-------|
| Attempts | 1 |
| Approaches tried | 1 |
| Lines of proof | 91 |
| Key dependencies | `Mathlib.Data.Real.Irrational`, `Mathlib.Analysis.SpecialFunctions.Pow.Real` |
