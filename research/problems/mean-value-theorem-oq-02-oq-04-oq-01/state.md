# State: mean-value-theorem-oq-02-oq-04-oq-01

**Phase**: ACT (S4: §3b explicit-form `analytic_taylor_remainder_uniform_bound_complex` is now PROVEN modulo one named sub-lemma `cauchy_diag_norm_bound` — sorry count stays at 1 but the §3b combination scaffolding is fully formalized)

## Lean File

`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — 614 lines, 0 new axioms, 1 sorry (moved from main theorem to a single named Mathlib-bridge sub-lemma).

## Theorems Proved (constructively)

- `runge_one_add_sq_pos`: `∀ x : ℝ, 0 < 1 + x^2`
- `runge_abs_le_one`: `∀ y : ℝ, |runge y| ≤ 1`
- `runge_zero`: `runge 0 = 1`
- `runge_one`: `runge 1 = 1/2`
- `runge_analyticOn_R`: `AnalyticOn ℝ runge (Set.Ioo (-100 : ℝ) 100)`
- `oq04_axiom_is_false`: `¬ OQ04_AxiomStatement`
- `oq04_parent_axiom_is_false_in_principle`: corollary of the above
- `analytic_taylor_remainder_uniform_geometric_complex` (S2): existential Cauchy-style geometric approximation in `z`-centered coordinates, via Mathlib's `HasFPowerSeriesOnBall.uniform_geometric_approx'`.
- `originalRemainderForm_is_false` (S3): refutation of the S1-S2 explicit-form RHS paired with `partialSum n`.
- `geometric_tail_identity` (S3): `(r / R)^(n+1) * R / (R - r) = r^(n+1) / (R^n * (R - r))` under `0 < R`, `r < R`. Proven via `field_simp + ring`.
- **NEW (S4)** `analytic_taylor_remainder_uniform_bound_complex`: §3b explicit form is now PROVEN modulo `cauchy_diag_norm_bound`. Proof chains `HasFPowerSeriesOnBall.hasSum_sub` (Mathlib), `cauchy_diag_norm_bound` (this file, sorry), `norm_sub_le_of_geometric_bound_of_hasSum` (Mathlib), `geometric_tail_identity`, and `norm_sub_rev` + `field_simp + ring` for the RHS normalization.

## Theorems With Sorry (deferred)

- `cauchy_diag_norm_bound`: per-degree Cauchy coefficient bound `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / R)^k` for `‖w‖ < R`, given `‖f z‖ ≤ M` on `Metric.ball a R` and `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)`. **This is the only remaining sorry in the file** (deferred to S5).

## Definitions

- `runge : ℝ → ℝ` — the Runge function `1/(1+x²)`
- `OQ04_AxiomStatement : Prop` — Prop-encoding of the parent OQ-04 axiom (refuted in §2)
- `OriginalRemainderForm : Prop` (S3) — Prop-encoding of the S1-S2 explicit form with `partialSum n` (refuted in §3a)

## Build Status

**Build verification pending** (S4 PR) via `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` (worktree-local script). Net new sorry-free content: the entire §3b combination/scaffolding proof of `analytic_taylor_remainder_uniform_bound_complex`. The one remaining `sorry` in the file is on the strictly smaller statement `cauchy_diag_norm_bound`.

## S4 Contribution (this session)

1. **New sub-lemma `cauchy_diag_norm_bound`** (statement, sorry deferred): isolates the single Cauchy-coefficient gap, with full docstring sketch of the proof chain (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` + `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` + `r' → R⁻` limit).

2. **§3b main combination, fully formalized** in `analytic_taylor_remainder_uniform_bound_complex`. The proof body now contains the actual chain:
   - Convert hypothesis `‖z − a‖ ≤ r < R` to `z ∈ EMetric.ball a (ENNReal.ofReal R)` via `EMetric.mem_ball + edist_dist + dist_eq_norm + ENNReal.ofReal_lt_ofReal_iff_of_nonneg`.
   - `HasFPowerSeriesOnBall.hasSum_sub` (Mathlib) gives `HasSum (fun k => p k (fun _ ↦ z − a)) (f z)`.
   - For each `k`, derive `‖p k (fun _ ↦ z − a)‖ ≤ M · (r/R)^k` from `cauchy_diag_norm_bound` plus monotonicity of `pow` (`pow_le_pow_left` + `mul_le_mul_of_nonneg_left`).
   - `norm_sub_le_of_geometric_bound_of_hasSum` (Mathlib) bounds `‖partialSum (n+1) − f z‖ ≤ M · (r/R)^(n+1) / (1 − r/R)`.
   - Unfold the `Finset.range (n+1)` sum to `p.partialSum (n+1)` by `rfl`, flip via `norm_sub_rev`, and rescale RHS by `field_simp + ring` (using `1 − r/R = (R−r)/R`) to land on `M · r^(n+1) / (R^n · (R−r))`.

3. **Sorry count unchanged** (1 → 1) but the residual gap is now isolated to a single named statement on the smaller Cauchy-coefficient lemma. The §3b main theorem is no longer a black-box `sorry`; the entire combination is auditable.

4. **Cleanly rebased against origin/main** (post-#18044, the S3 merge). PR #17904 (which also stated `cauchy_diag_norm_bound`) is CONFLICTING; this PR builds on the merged S3 state directly with `cauchy_diag_norm_bound` matching the §3b umbrella docstring.

## Coordination Note

PR #17904 (researcher-1, conflicting) had `cauchy_diag_norm_bound` as a separate `sorry` AND the main combination step as a separate `sorry` (net 2 sorries vs S3's 1). This S4 PR keeps the sorry count at 1 by completing the combination step, leaving only the Cauchy-coefficient gap deferred. The naming `cauchy_diag_norm_bound` is identical to #17904's; the signature differs (uses `_hR`, `_hM`, `_hf`, `_hbound`, `_hw` underscored since the body is `sorry`).

## Next Action (S5+)

Discharge `cauchy_diag_norm_bound` via the Mathlib Cauchy-integral chain:

1. Fix `r' ∈ (max(r, ‖w‖), R)`; then `closedBall a r' ⊂ Metric.ball a R` so `f` is bounded by `M` on `sphere a r'`.
2. Apply `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` to get `‖iteratedDeriv k f a‖ ≤ k! · M / r'^k`.
3. Use `HasFPowerSeriesOnBall.factorial_smul` to relate `p k` to `iteratedFDeriv k f a / k!`.
4. `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` (in 1D the product collapses to `w^k`): `(iteratedFDeriv k f a) (fun _ ↦ w) = w^k * iteratedDeriv k f a`.
5. Conclude `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖/r')^k`. Take `r' → R⁻` (continuity of the upper bound) to get `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖/R)^k`.

Estimated S5 proof length: 100-150 lines (Cauchy integral + iterated derivative bridge + limit).

## Pool Status Note

This slug remains `progress` (one sorry remains on `cauchy_diag_norm_bound`). Set status to `progress` after S4 merge.
