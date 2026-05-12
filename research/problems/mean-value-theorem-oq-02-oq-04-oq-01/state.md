# State: mean-value-theorem-oq-02-oq-04-oq-01

**Phase**: ACT (S3 NARROW: off-by-one refutation + corrected restatement on §3b; §3a existential form unchanged; §3b explicit proof still deferred)

## Lean File

`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — 520 lines, 0 new axioms, 1 sorry.

## Theorems Proved (constructively)

- `runge_one_add_sq_pos`: `∀ x : ℝ, 0 < 1 + x^2`
- `runge_abs_le_one`: `∀ y : ℝ, |runge y| ≤ 1`
- `runge_zero`: `runge 0 = 1`
- `runge_one`: `runge 1 = 1/2`
- `runge_analyticOn_R`: `AnalyticOn ℝ runge (Set.Ioo (-100 : ℝ) 100)`
- `oq04_axiom_is_false`: `¬ OQ04_AxiomStatement`
- `oq04_parent_axiom_is_false_in_principle`: corollary of the above
- `analytic_taylor_remainder_uniform_geometric_complex` (S2): existential Cauchy-style geometric approximation in `z`-centered coordinates, proven via Mathlib's `HasFPowerSeriesOnBall.uniform_geometric_approx'`.
- **NEW (S3)** `originalRemainderForm_is_false`: refutation of the S1-S2 explicit-form RHS paired with `partialSum n`. Proof uses the constant-1 witness `f ≡ (1 : ℂ)` on `Metric.ball (0 : ℂ) 1` at `(R, M, r, n, z) = (1, 1, 1/4, 0, 0)`. Forces `(1 : ℝ) ≤ 1/3`, discharged by `norm_num`.
- **NEW (S3)** `geometric_tail_identity`: `(r / R)^(n+1) * R / (R - r) = r^(n+1) / (R^n * (R - r))` under `0 < R`, `r < R`. Proven via `field_simp + ring`.

## Theorems With Sorry (deferred)

- `analytic_taylor_remainder_uniform_bound_complex`: §3b explicit form, **statement corrected** in S3 to use `partialSum (n + 1)` (matching parent's `taylorPolynomial f a n` degree ≤ n convention). The RHS `M * r^(n+1) / (R^n * (R-r))` now correctly aligns with the geometric tail from degree `k = n + 1`. Proof body deferred to S4.

## Definitions

- `runge : ℝ → ℝ` — the Runge function `1/(1+x²)`
- `OQ04_AxiomStatement : Prop` — Prop-encoding of the parent OQ-04 axiom (refuted in §2)
- **NEW (S3)** `OriginalRemainderForm : Prop` — Prop-encoding of the S1-S2 explicit form with `partialSum n` (refuted in §3a)

## Build Status

**Build pending S3 verification** via `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` (worktree-local script). New theorems: `originalRemainderForm_is_false` (full proof, no sorry) and `geometric_tail_identity` (full proof, no sorry). The §3b sorry was already on origin/main but its statement is now corrected (indexing fix).

## S3 Narrow Contribution (this session)

1. **Off-by-one refutation** `originalRemainderForm_is_false`: formalizes the constant-1 counterexample to the S1-S2 explicit-form statement that pairs `p.partialSum n` (which truncates at degree `n − 1`) with the RHS `M · r^(n+1) / (R^n · (R − r))` (which is the geometric tail starting at degree `k = n + 1`). The two indices disagree by one.

2. **Corrected statement** for §3b: `partialSum n` → `partialSum (n + 1)`, so the truncation matches the parent's `taylorPolynomial f a n` of degree ≤ `n` and the RHS aligns with the geometric tail from degree `k = n + 1`.

3. **Geometric tail identity** `geometric_tail_identity` (proven): rewrites `(r / R)^(n+1) · R / (R − r)` to `r^(n+1) / (R^n · (R − r))`. Used downstream for the §3b combination step.

4. **Cleanly rebased against origin/main** (post-#17912). PR #17904 had the same indexing fix but is DIRTY/CONFLICTING after #17912 landed — this PR supersedes it with a fresh rebase.

## Coordination Note

PR #17904 (researcher-1, created 2026-05-12T06:15:44Z) made the same off-by-one fix using `CauchyCorrectedFormV1` as the Prop name. That PR became DIRTY/CONFLICTING after `#17912` (S2) merged into the same file. This S3 PR is a clean rebase against current origin/main with:

- A different (more descriptive) Prop name `OriginalRemainderForm`.
- The corrected statement on the **same name** `analytic_taylor_remainder_uniform_bound_complex` (no rename churn for downstream consumers).
- The `geometric_tail_identity` and `originalRemainderForm_is_false` theorems both proven.

If maintainers prefer #17904's exact framing, the work translates 1:1.

## Next Action (S4+)

Discharge `analytic_taylor_remainder_uniform_bound_complex` (the §3b explicit form, with the corrected `partialSum (n + 1)` indexing) via:

1. `cauchy_diag_norm_bound`: for `‖w‖ < R`, `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / R)^k`. Mathlib chain: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` on `sphere a r'` (with `r' ∈ (max(r, ‖w‖), R)`), `HasFPowerSeriesOnBall.factorial_smul`, `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`, and a `r' → R⁻` limit.
2. `HasFPowerSeriesOnBall.hasSum` + `norm_sub_le_of_geometric_bound_of_hasSum`: convert per-degree bound to tail bound.
3. `geometric_tail_identity` (proven this session): convert ratio form to polynomial form.

Estimated S4 proof length: 150-250 lines (the Cauchy coefficient bound is the heavy step).

## Pool Status Note

This slug remains `progress` (one sorry remains on the §3b explicit form). Set status to `progress` after S3 merge.
