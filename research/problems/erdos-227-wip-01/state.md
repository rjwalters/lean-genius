# Research State: erdos-227-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24
**Iteration**: 3

## Current Focus
Route 1 (the optional Mathlib bridge) is DONE: Part 12 (session 2026-07-24,
researcher-2, 10 new axiom-free theorems) proves the **unconditional** Cauchy
estimate `μ(r) ≤ M(r)` for every genuinely entire function — no coefficient
hypothesis — via `FormalMultilinearSeries.ofScalars` + radius = ⊤ +
one-dimensional power-series uniqueness + `norm_cauchyPowerSeries_le`.
Corollaries `termModulusRatio_le_one` and `limit_mem_Icc` (L ∈ [0,1]) are now
unconditional; the Part-11 `_of_nonneg` versions are special cases.
Docker build exit 0. Sorry/axiom profile unchanged (1 sorry, 3 axioms).

## Active Approach
Both the elementary layer (Part 11) and the complex-analytic bridge (Part 12)
are saturated. Remaining:
1. DEEP (blocked): the sorry (`positive_coeffs_normal`) and all 3 axioms need
   Clunie / Clunie–Hayman / Wiman–Valiron theory absent from Mathlib.
2. OPTIONAL polish veins (small): maximum-principle restatement of
   `maxModulus` via `Complex.AbsMax`; `AnalyticAt`-based characterisation of
   `IsEntire`.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1

## Blockers
- Sorry + 3 axioms: "materially new mechanism required" (Mathlib lacks
  Wiman–Valiron theory and the Clunie–Hayman constructions).

## Next Action
If re-served: only the small polish veins above, or stand down — do NOT
re-attempt axiom/sorry elimination from current Mathlib, and route 1
(HasFPowerSeriesOnBall bridge) is already done (session 2026-07-24).

## Session History
- 2026-07-22 (iteration 2): Part 11 elementary layer — 13 axiom-free
  theorems: IsEntire, μ(r) ≤ M(r) for non-negative coefficients, ratio ≤ 1,
  limits in [0,1], exp witness.
- 2026-07-24 (iteration 3): Part 12 Cauchy-estimate bridge — unconditional
  μ(r) ≤ M(r); see sessions/2026-07-24-s3-act-cauchy-estimate-bridge.md.
