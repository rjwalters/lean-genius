# Research State: erdos-1151-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-21
**Iteration**: 16
**Last Updated**: 2026-05-07

## Current Focus
2 sorries remain in `proofs/Proofs/Erdos1151OQ04.lean` (1567 lines, on `main`):

1. `trig_sum_harmonic_lb` (line ~1379) — *general* θ ∈ (0, π) harmonic lower
   bound for the trig sum Σ sin(φₖ)/|cos θ − cos φₖ| ≥ C·n·log(n+1).
   Self-contained statement (no p/q dependency); Lipschitz + harmonic over
   near-nodes + finite-set minimum for small n. **Steps 1–5 already proved**
   as helper lemmas (`exists_nearest_chebyshev_angle`,
   `chebyshev_angle_dist_triangle`, `chebyshev_angle_dist_from_nearest`,
   `sin_lb_of_in_interior`, `sin_chebyshev_midpoint_lb`,
   `chebyshev_term_lb_at_node`); only the final harmonic-sum + finite-set
   assembly remains.

2. `divergence_from_lebesgue_growth` (line ~1551) — fundamental
   functional-analysis gap: Banach–Steinhaus / UBP gives lim sup = ∞, not
   lim = +∞. Closing this requires either weakening the conclusion to
   lim sup or building an explicit lacunary continuous function.

## Active Approach

**Sorry 1** is the immediate target. Sessions 14–16 (2026-05-07) added the
full geometric scaffolding:

- Session 14 (PR #16593): `exists_nearest_chebyshev_angle` — given θ ∈ (0, π)
  and n ≥ 1, ∃ k₀ : Fin n with |θ − φ_{k₀}| ≤ π/(2n).
- Session 15 (PR #16745): `chebyshev_angle_dist_triangle`,
  `chebyshev_angle_dist_from_nearest` — for j-th nearest node beyond k₀,
  |θ − φ_{k₀+j+1}| ≤ (2j+3)π/(2n). Plus 5 Mathlib API drift fixes
  (`Nat.harmonic` → `harmonic`, `Even.not_odd` → `not_odd_iff_even.mpr`,
  `div_lt_div_iff` argument order, etc.).
- Session 16 (PR #16765): `sin_lb_of_in_interior` (sin φ ≥ d/π for
  φ ∈ (d/2, π−d/2)), `sin_chebyshev_midpoint_lb`,
  `chebyshev_term_lb_at_node` — assembled per-term lower bound
  (d/π) · 2n/((2j+3)π).

The remaining work for Sorry 1 is the **sub-sum + finite-set** assembly:

- Sum over j = 0,…,m−1 with m = ⌊nd/(4π)⌋:
  Σ ≥ (2dn/π²) · Σ_{j=0}^{m−1} 1/(2j+3) ≥ (2dn/π²) · ((1/2)·log(m+2) − 1)
  using already-proven `odd_harmonic_sum_lb`.
- For 1 ≤ n < N₀(d): finite-set minimum over `{1,…,N₀−1}` via
  `Finset.min'`; combine with the asymptotic constant.

## Next Steps

1. Prove `trig_sum_harmonic_lb` using the existing scaffolding (~80–120 lines):
   - Pull Σ over {k₀+1,…,k₀+m}; bound each term via
     `chebyshev_term_lb_at_node` (Step 5);
   - Apply `odd_harmonic_sum_lb` for the resulting Σ 1/(2j+3);
   - Finite-set minimum for small n.

2. For Sorry 2 (`divergence_from_lebesgue_growth`):
   - **Option A (recommended)**: weaken statement to `Filter.Tendsto … atTop`
     replaced by `∀ M, ∃ᶠ n, M < ...` (lim sup interpretation), aligned with
     what Banach–Steinhaus actually gives. Update the corollary chain.
   - **Option B**: build a lacunary continuous f such that f(φₙₖ) ∼ sign(...)
     to force Lₙf(x) → ∞. Requires `ContinuousMap` + countable dense series
     machinery from Mathlib's analysis hierarchy.

## Blockers

- Sorry 2 only — fundamental gap. Sorry 1 is now mechanically tractable
  given Sessions 14–16 infrastructure.

## History

- 2026-04-21: Problem selected by Seeker
- 2026-04-22: Sessions 1–4: companion lemmas, reduced 4→4 sorries (companion 0)
- 2026-04-22: Sessions 5–11: main file 4→2 sorries (PR #12153 chain)
- 2026-04-24: Session 12: deep analysis, x = −1 tan-cot rewriting
- 2026-04-25: Session 13: 5 helper lemmas (proved); corrected x = −1 analysis
- 2026-05-07: Session 14: `exists_nearest_chebyshev_angle` (PR #16593)
- 2026-05-07: Session 15: triangle bounds + Mathlib API drift (PR #16745)
- 2026-05-07: Session 16: Step 4 sin lb + Step 5 per-term lb (PR #16765)
- 2026-05-07: Session 17 (this update): observe-only state.md refresh

## Open PRs

None — all of Sessions 14–16 are merged into `main`.

## File Stats (after PR #16765 merged)

- `proofs/Proofs/Erdos1151OQ04.lean`: 1567 lines, 2 sorries
- `proofs/Proofs/Erdos1151OQ04Aristotle.lean`: companion file (0 sorries)
- `proofs/Proofs/Erdos1151Problem.lean`: parent problem statement
