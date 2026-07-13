# Isoperimetric Inequality for Lipschitz Curves (Measure-Theoretic)

**Problem**: area-of-circle-oq-01-oq-03-oq-02
**Status**: in-progress (1 sorry from completeness)

## Problem Summary

Extend the isoperimetric inequality C² ≥ 4πA from smooth closed curves to Lipschitz closed curves.
Key insight: Lipschitz functions are differentiable a.e. (Rademacher), so arc-length and Green's theorem remain valid.

## Session 2026-04-03 (Session 2) - Core Proof Progress

**Mode**: REVISIT (RICH knowledge, continuing prior work)
**Outcome**: progress — proved hCS and harea_bound structure, fixed broken code

### What Was Done
1. **Fixed wirtinger_sum_sq_bound_lip**: Replaced incorrect lemma calls
   (`Real.norm_le_of_lipschitzWith`, `IntervalIntegrable.mono_fun`, `Measurable.intervalIntegrable`)
   with clean `sorry` + explanatory comments.

2. **Added hspeed_c conversion**: `hspeed'` from `exists_lip_nice_reparam` uses `γ.circumference/(2π)`,
   while local `c = L/(2π)` uses `L = γ'.circumference`. Added explicit conversion via `hcirc_eq`.

3. **Proved hCS** (removed `all_goals sorry`):
   - Both integrability goals proved: continuity from Lipschitz + Real.sq_sqrt for (√f)²=f

4. **Proved harea_bound** (structure complete, hf_int sorry remains):
   - Proved `h_ae_pw`: a.e. Cauchy-Schwarz bound via `cross_product_sq_le` + `hspeed_c`
   - Integral chain: `|∫f| ≤ ∫|f|` → `≤ c·∫√` via `MeasureTheory.integral_mono_ae`

### Remaining Sorries (5 total)
1. `lip_x`/`lip_y` in toLipschitz: not on critical path
2. `hdx_int`/`hdy_int`: `(deriv f)^2` integrable for LipschitzWith K f
3. `hf_int`: `γ'.x * deriv γ'.y - γ'.y * deriv γ'.x` integrable — the last blocker for main theorem

### Next Steps
1. **hf_int** (highest priority): prove `xy'-yx'` integrable for Lipschitz curves
   - Need: `LipschitzWith.norm_deriv_le` or Rademacher's theorem in Mathlib
   - Alternative: bound by `Kx * Ky * 2π` via `‖deriv f t‖ ≤ K` + `integrable_const`
2. **hdx_int/hdy_int**: Same approach
3. **toLipschitz**: `ContDiff.lipschitzWith` or MVT on compact interval
