# State: mean-value-theorem-oq-02-oq-04-oq-01

**Phase**: ACT (S2 NARROW: adds a proven existential form; explicit-form sorry untouched; off-by-one fix deferred to PR #17904)

## Lean File

`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — 397 lines, 0 new axioms, 1 sorry.

## Theorems Proved (constructively)

- `runge_one_add_sq_pos`: `∀ x : ℝ, 0 < 1 + x^2`
- `runge_abs_le_one`: `∀ y : ℝ, |runge y| ≤ 1`
- `runge_zero`: `runge 0 = 1`
- `runge_one`: `runge 1 = 1/2`
- `runge_analyticOn_R`: `AnalyticOn ℝ runge (Set.Ioo (-100 : ℝ) 100)`
- `oq04_axiom_is_false`: `¬ OQ04_AxiomStatement`
- `oq04_parent_axiom_is_false_in_principle`: corollary of the above
- **NEW (S2)** `analytic_taylor_remainder_uniform_geometric_complex`: existential Cauchy-style geometric approximation in z-centered coordinates, proven via Mathlib's `HasFPowerSeriesOnBall.uniform_geometric_approx'`.

## Theorems With Sorry (deferred)

- `analytic_taylor_remainder_uniform_bound_complex`: §3b explicit form (UNCHANGED in this PR; off-by-one fix left to parallel PR #17904).

## Definitions

- `runge : ℝ → ℝ` — the Runge function `1/(1+x²)`
- `OQ04_AxiomStatement : Prop` — Prop-encoding of the parent axiom

## Build Status

**Build VERIFIED** via `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` (worktree-local script): 7745 jobs, only one sorry warning on the §3b explicit form (pre-existing from S1). The new §3a existential theorem is proven cleanly.

## S2 Narrow Contribution (this session)

1. **Proven existential corrected-form theorem** `analytic_taylor_remainder_uniform_geometric_complex` (16-line proof, no sorries): Mathlib-native translation of `HasFPowerSeriesOnBall.uniform_geometric_approx'` from y-centered (f(a+y)) to z-centered (f z, z ∈ Metric.ball a r) coordinates. Existential constants K ∈ (0,1), C > 0.

2. **Added `open scoped NNReal ENNReal`** so the new theorem can use `ℝ≥0` / `ℝ≥0∞` notation.

3. **Did NOT modify the §3b explicit-form theorem** — coordination with PR #17904.

## Coordination Note

PR #17904 (researcher-1, created 2026-05-12T06:15:44Z) is a parallel S2 attempt that:
- Refutes S1's explicit-form statement as a Prop (off-by-one bug discovery).
- Restates the §3b explicit form with corrected `partialSum (n+1)` indexing.
- Decomposes proof into named sub-lemmas (geometric_tail_identity proven; cauchy_diag_norm_bound + combined statement sorry'd).
- Build pending (not Docker-verified at time of PR creation).

To avoid duplication and merge conflict, this S2 PR is narrowed to the unique deliverable: the proven existential form. The off-by-one fix is left to #17904. Whichever PR merges first, the other will rebase (changes are nearly orthogonal — different theorems).

## Next Action (S3+)

Discharge `analytic_taylor_remainder_uniform_bound_complex` (the explicit form, §3b) via:
1. `Complex.norm_cauchyPowerSeries_le` (Mathlib): `‖cauchyPowerSeries f a R n‖ ≤ ((2π)⁻¹ · ∫_{[0, 2π]} ‖f(circleMap a R θ)‖) · |R|⁻¹^n`.
2. From sup bound `‖f‖ ≤ M`, `∫ ≤ 2πM`, giving `‖p k‖ ≤ M / R^k`.
3. `DifferentiableOn.hasFPowerSeriesOnBall`: identifies abstract `p` with `cauchyPowerSeries`.
4. Term-by-term `‖p k (z - a)‖ ≤ M · (r/R)^k`.
5. Geometric tail summation.

Estimated S3 proof length: 150-200 lines.

## Pool Status Note

This slug is now in `progress` (one sorry remains on the explicit form). Set status to `progress` after S2 merge.
