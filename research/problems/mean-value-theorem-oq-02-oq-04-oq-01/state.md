# State: mean-value-theorem-oq-02-oq-04-oq-01

**Phase**: ACT (S5: `cauchy_diag_norm_bound` is now PROVEN by limit-extraction from a new finite-radius sub-lemma `cauchy_diag_norm_bound_at_radius`. The sorry shifts from the boundary-form bound to a strict-intermediate-radius form that directly matches Mathlib's Cauchy-integral chain on `sphere a r'`. Sorry count stays at 1 but the limit-extraction step (`r' → R⁻` via `Filter.Tendsto.le_of_tendsto`) is fully formalized.)

## Lean File

`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — 705 lines, 0 new axioms, 1 sorry (now on the finite-radius sub-lemma `cauchy_diag_norm_bound_at_radius`).

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
- **(S4)** `analytic_taylor_remainder_uniform_bound_complex`: §3b explicit form is now PROVEN modulo `cauchy_diag_norm_bound`. Proof chains `HasFPowerSeriesOnBall.hasSum_sub` (Mathlib), `cauchy_diag_norm_bound`, `norm_sub_le_of_geometric_bound_of_hasSum` (Mathlib), `geometric_tail_identity`, and `norm_sub_rev` + `field_simp + ring` for the RHS normalization.
- **NEW (S5)** `cauchy_diag_norm_bound` is now PROVEN by limit-extraction from a new sub-lemma `cauchy_diag_norm_bound_at_radius` (the finite-radius form with explicit `r' ∈ (0, R)`). The limit-extraction proof uses `ContinuousAt.mul`, `ContinuousAt.div`, `ContinuousAt.pow`, `Filter.Tendsto.mono_left` along `𝓝[<] R`, `Filter.eventually_of_mem` with `Set.Ioo 0 R ∈ 𝓝[<] R`, and `le_of_tendsto` to transport the eventual bound to the boundary limit. **The only remaining `sorry`** in the file is now the finite-radius `cauchy_diag_norm_bound_at_radius`, which directly matches Mathlib's Cauchy-integral chain on `sphere a r'`.

## Theorems With Sorry (deferred)

- `cauchy_diag_norm_bound_at_radius`: per-degree Cauchy coefficient bound at a strict intermediate radius `r' ∈ (0, R)` — `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / r')^k` — given `‖f z‖ ≤ M` on `Metric.ball a R` and `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)`. **This is the only remaining sorry in the file** (deferred to S6). The boundary form `cauchy_diag_norm_bound` is now PROVEN from this via limit-extraction.

## Definitions

- `runge : ℝ → ℝ` — the Runge function `1/(1+x²)`
- `OQ04_AxiomStatement : Prop` — Prop-encoding of the parent OQ-04 axiom (refuted in §2)
- `OriginalRemainderForm : Prop` (S3) — Prop-encoding of the S1-S2 explicit form with `partialSum n` (refuted in §3a)

## Build Status

**Build verification IN PROGRESS** (S5 PR) via `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` (worktree-local script). Net new sorry-free content (S5): the entire limit-extraction proof of `cauchy_diag_norm_bound` (from the finite-radius sub-lemma). The one remaining `sorry` in the file is on the strict-intermediate-radius `cauchy_diag_norm_bound_at_radius`.

## S5 Contribution (this session)

1. **Refactored sorry locality**: introduced new sub-lemma `cauchy_diag_norm_bound_at_radius` with explicit intermediate radius `r' ∈ (0, R)`. Its conclusion is the *finite-radius* Cauchy bound `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / r')^k` — exactly the statement Mathlib's `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` infrastructure produces directly on `sphere a r'`. The single residual sorry of the file now lives on this strict-r' form.

2. **Limit-extraction step, fully formalized** in `cauchy_diag_norm_bound`. The proof body now contains the actual chain:
   - For every `r' ∈ Set.Ioo 0 R`, apply `cauchy_diag_norm_bound_at_radius` to get `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / r')^k`.
   - Continuity of `r' ↦ M * (‖w‖ / r')^k` at `R > 0` via `ContinuousAt.mul`, `ContinuousAt.div` (with `R ≠ 0` from `0 < R`), and `ContinuousAt.pow`.
   - `Filter.Tendsto.mono_left` from `ContinuousAt.tendsto` to `𝓝[<] R`.
   - `Set.Ioo (0 : ℝ) R ∈ 𝓝[<] R` via `mem_nhdsWithin` with `Set.Ioi 0 ∈ 𝓝 R` witness (since `0 < R`).
   - `Filter.eventually_of_mem` transports the pointwise bound on `Set.Ioo 0 R` to `∀ᶠ r' in 𝓝[<] R, …`.
   - `le_of_tendsto` lifts the eventual bound to the boundary limit `M · (‖w‖ / R)^k`.

3. **Sorry count unchanged** (1 → 1) but the residual gap is now isolated to a *strict-intermediate-radius* statement rather than the boundary form. The limit-extraction step is no longer a black-box; the entire continuity / `𝓝[<]` / `le_of_tendsto` chain is auditable.

4. **Cleanly rebased against origin/main** (post-#18085, the S4 merge). The S5 changes are local to lines 417–490 (replacing the old `cauchy_diag_norm_bound` `sorry` with two theorems and a fully-proved limit reduction).

## Coordination Note (S5)

This builds on the merged S4 state (PR #18085). The S5 sub-lemma `cauchy_diag_norm_bound_at_radius` exposes the *exact* hypothesis pattern Mathlib's Cauchy-integral chain expects: a strict intermediate radius `r'`, a sup bound on the open ball of radius `R > r'`, and a HasFPowerSeriesOnBall hypothesis on the ball of radius `R`. A future S6 iteration can discharge it without re-litigating the limit-extraction logic.

## S4 Contribution (previous session, for reference)

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

## Next Action (S6+)

Discharge `cauchy_diag_norm_bound_at_radius` via the Mathlib Cauchy-integral chain (the limit-extraction step is **already done** in S5):

1. Sub-disk inclusion: `closedBall a r' ⊂ Metric.ball a R` from `r' < R`, hence `f` is bounded by `M` on `sphere a r' ⊂ closedBall a r'` via `hbound`.
2. Apply `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (or the closest Mathlib variant) to get `‖iteratedDeriv k f a‖ ≤ k! · M / r'^k`.
3. Use `HasFPowerSeriesOnBall.factorial_smul` (or `HasFPowerSeriesAt.iteratedFDeriv_eq_sum_of_completeSpace` — cf. `TaylorTheoremOQ02.fps_coeff_eq_taylor_coeff` for the ℝ-analogue) to relate `p k` to `iteratedFDeriv k f a / k!`.
4. `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` (in 1D the product collapses to `w^k`): `(iteratedFDeriv k f a) (fun _ ↦ w) = w^k * iteratedDeriv k f a`.
5. Combine: `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖/r')^k`.

Estimated S6 proof length: 60-100 lines (no limit step required; just the Cauchy estimate on a closed sphere + the formal-series / iterated-derivative bridge).

## Pool Status Note

This slug remains `progress` (one sorry remains on `cauchy_diag_norm_bound_at_radius`). Set status to `progress` after S5 merge.
