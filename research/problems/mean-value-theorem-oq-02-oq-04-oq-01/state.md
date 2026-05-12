# State: mean-value-theorem-oq-02-oq-04-oq-01

**Phase**: ACT (Lean code shipped, refutation complete; one S2-deferred sorry on the corrected statement)

## Lean File

`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — 280 lines, 0 new axioms, 1 sorry.

## Theorems Proved (constructively)

- `runge_one_add_sq_pos`: `∀ x : ℝ, 0 < 1 + x^2`
- `runge_abs_le_one`: `∀ y : ℝ, |runge y| ≤ 1`
- `runge_zero`: `runge 0 = 1`
- `runge_one`: `runge 1 = 1/2`
- `runge_analyticOn_R`: `AnalyticOn ℝ runge (Set.Ioo (-100 : ℝ) 100)`
- `oq04_axiom_is_false`: `¬ OQ04_AxiomStatement`
- `oq04_parent_axiom_is_false_in_principle`: corollary of the above

## Theorems With Sorry (deferred to S2)

- `analytic_taylor_remainder_uniform_bound_complex`: corrected complex-disk version. Proof outline in §3 docstring.

## Definitions

- `runge : ℝ → ℝ` — the Runge function `1/(1+x²)`
- `OQ04_AxiomStatement : Prop` — Prop-encoding of the parent axiom

## Build Status

Build attempted; final state TBD pending PR CI. Local Docker build pass requires:
- `proofs/Proofs/MeanValueTheoremOQ02.lean` line 56: `∑ k in` → `∑ k ∈` (Mathlib drift; included in this PR)
- `proofs/Proofs/MeanValueTheoremOQ02.lean` line 67-69: redundant `ring` after simp closure removed (included in this PR)

## Next Action (Session 2)

Discharge `analytic_taylor_remainder_uniform_bound_complex` (the corrected statement) via:
1. Apply `HasFPowerSeriesOnBall.uniform_geometric_approx' hf hrR` to get `∃ a ∈ Ioo (0:ℝ) 1, ∃ C > 0, ...`.
2. Use `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius` to bound `‖p k‖ * R^k ≤ M`.
3. Sum the geometric tail `∑_{k > n} (r/R)^k = (r/R)^{n+1} / (1 - r/R)` using `tsum_geometric_of_lt_one`.
4. Combine to obtain the explicit `M · r^(n+1) / (R^n · (R - r))` bound.

Estimated S2 proof length: 100-200 lines.

## Pool Status Note

This slug was claimed as a fresh tier-B problem (status: available, score 0). After completion, set status to `progress` (since corrected statement still has a sorry) and release lock.
