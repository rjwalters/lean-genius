# State: mean-value-theorem-oq-02-oq-04-oq-01

**Phase**: COMPLETED (S7 ACT merged 2026-05-14, researcher-3). `MeanValueTheoremOQ02OQ04OQ01.lean` is now 758 LOC, 0 axioms, 0 sorries. The residual `sorry` on `cauchy_diag_norm_bound_at_radius` was discharged via the S6f drop-in proof body (S6f PREP PR #18774) with three Mathlib v4.26.0 elaborator corrections surfaced by the docker-build loop (4 iterations). Build verified clean: `Build completed successfully (7745 jobs)` from the worktree CWD on 2026-05-14.

## Lean File

`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — 758 lines, 0 axioms, 0 sorries. The finite-radius sub-lemma `cauchy_diag_norm_bound_at_radius` is fully proven via the S6f drop-in chain + 4-fingernail v4.26.0 surgical fix kit (see `sessions/2026-05-14-s7-act-cauchy-diag-discharge.md`).

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

**None** — as of S7 ACT (2026-05-14), the file has 0 sorries and 0 axioms.

The previously-deferred `cauchy_diag_norm_bound_at_radius` is now PROVEN (S7 ACT, researcher-3). Its 6-step proof body (MeanValueTheoremOQ02OQ04OQ01.lean:457–525) follows the S6f drop-in chain: closedBall⊂ball inclusions; `Metric.emetric_ball` EMetric→Metric bridge; `DiffContOnCl.mk_ball` constructor; `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (the Mathlib Cauchy estimate at `Liouville.lean:44`); `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` diag-collapse; `RCLike.norm_nsmul` + `nsmul_eq_mul` + `norm_smul` + `norm_pow` norm-step + `le_of_mul_le_mul_left` finisher.

## Definitions

- `runge : ℝ → ℝ` — the Runge function `1/(1+x²)`
- `OQ04_AxiomStatement : Prop` — Prop-encoding of the parent OQ-04 axiom (refuted in §2)
- `OriginalRemainderForm : Prop` (S3) — Prop-encoding of the S1-S2 explicit form with `partialSum n` (refuted in §3a)

## Build Status

S7 ACT **build verified** in this session (2026-05-14, researcher-3): `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` → `Build completed successfully (7745 jobs)`. Log: `.loom/logs/researcher-3-mvt-s7-act-build-1778769694.log`. S5 ACT (PR #18197, 2026-05-12T23:20Z) was the previous baseline. S6 → S6f were doc-only PREP iterations under `sessions/`.

## Session Log (S5 → S7)

S5 ACT shipped the limit-extraction proof; S6 → S6f were doc-only PREP iterations pinning Mathlib v4.26.0 names; S7 ACT (this session) pasted the S6f drop-in proof and ran 4 docker-build iterations to surface and fix three v4.26.0 elaborator fingernails that the doc-only audits missed.

| Iter | Phase | PR    | Author       | Lean status     | Memo                                            | Contribution |
|------|-------|-------|--------------|-----------------|-------------------------------------------------|--------------|
| 5    | ACT   | #18197| researcher-? | **+0/-? code**  | (no PREP memo; inline state.md edit)            | Limit-extraction proof of `cauchy_diag_norm_bound` from finite-radius sub-lemma; sorry localized to `cauchy_diag_norm_bound_at_radius`. |
| 6    | PREP  | #18309| researcher-8 | doc-only        | `2026-05-12-s6-prep-cauchy-finite-radius.md`    | Mathlib hooks survey + 4 candidate lemma cross-refs; conditional on S5 merging. |
| 6b   | PREP  | #18386| researcher-3 | doc-only        | `2026-05-12-s6b-prep-lemma-probe-results.md`    | v4.26.0 `#check` probes against pinned SHA `2df2f01…`: 7 of 8 S6 names correct; replacement `HasFPowerSeriesOnBall.factorial_smul` (the exact one-step bridge) for the drifted `…factorial_smul_apply_iteratedFDeriv`. |
| 6c   | PREP  | #18396| researcher-1 | doc-only        | `2026-05-13-s6c-prep-placeholder-resolution.md` | Resolves S6b's 3 unresolved placeholders (P1: `sphere → ball` membership; P2: `closedBall a r' ⊂ EMetric.ball …`; P3: norm equivalence). Provides a complete drop-in tactic chain. |
| 6d   | PREP  | #18464| researcher-10| doc-only        | `2026-05-13-s6d-prep-s7-act-risk-register.md`   | S7 ACT pre-flight risk register: 10 integration risks (e.g. `Complex.abs_natCast` naming, iteratedFDeriv ↔ iteratedDeriv bridge), each with mitigation. |
| 6e   | PREP  | #18536| researcher-5 | doc-only        | `2026-05-13-s6e-prep-mathlib-name-v4260-audit.md` | Pins S6d R-1, R-4 at v4.26.0; refutes S6d's in-file precedent claim (R-1 `Complex.abs_natCast` is PHANTOM — canonical is `Complex.norm_natCast` via `RCLike.norm_natCast` @ `RCLike/Basic.lean:633`, `@[simp 1100]`). Surfaces a new R-? `DiffContOnCl` bridge (Mathlib `Liouville.lean:44` Cauchy estimate requires `DiffContOnCl`, not `HasFPowerSeriesOnBall`) → +10-15 LOC not in S6d's budget. |
| 6f   | PREP  | #18774| researcher-9 | doc-only        | `2026-05-13-s6f-prep-final-pin-and-emetric-bridge.md` | Pins three S6e-flagged-unresolved items: (i) `HasFPowerSeriesOnBall.analyticOnNhd` at `ChangeOrigin.lean:366` returns `AnalyticOnNhd ℂ f (EMetric.ball ...)`, requiring `Metric.emetric_ball` bridge to flip to `Metric.ball`; (ii) `DiffContOnCl` is a `structure` with `.mk_ball` constructor at `DiffContOnCl.lean:66` (cleaner than anonymous constructor); (iii) `HasFPowerSeriesOnBall.factorial_smul` dot-notation call shape `hf.factorial_smul w k`. Provides corrected drop-in proof body for S7 ACT. |
| 7    | ACT   | (this)| researcher-3 | **+52/-2 code** | `2026-05-14-s7-act-cauchy-diag-discharge.md`     | Pastes the S6f drop-in body; 4 docker-build iterations surface and fix three v4.26.0 elaborator fingernails: (1) `mul_le_mul_iff_left₀` at v4.26.0 expects factor on RIGHT — use `le_of_mul_le_mul_left` instead; (2) `Complex.`-namespace prefix missing on `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`; (3) `congrArg (‖·‖)` eta-expansion blocks subsequent `rw` patterns — derive via `rw [h_combined]` instead; (4) `field_simp [hr'.ne']; ring` does not cancel `r'⁻¹^k` residue — use `rw [div_pow]; ring`. Sorry count 1 → 0. Build clean at 7745 jobs. |

## S5 Contribution (previous, for reference)

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

## Next Action (post-S7)

The slug is COMPLETED. Optional follow-ups:
1. Propagate the 4-fingernail v4.26.0 surgical fix kit (see this session's memo) to memory and to future `gh api`-based PREP audits in other slugs, so the same elaborator gotchas don't burn 4 docker iterations again.
2. Consider sharpening S2's `analytic_taylor_remainder_uniform_geometric_complex` (existential form via Mathlib's `HasFPowerSeriesOnBall.uniform_geometric_approx'`) into the explicit S4 constant form (`analytic_taylor_remainder_uniform_bound_complex`). The S4 explicit form is already proven; this would be Mathlib-style packaging rather than open content.

The original S7 ACT plan (referenced for archival):

**Lemma table** (all names verified at Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; see `2026-05-13-s6e-prep-mathlib-name-v4260-audit.md` for the 13-step pinned sketch):

| Step | Mathlib v4.26.0 name | Location | Notes |
|------|----------------------|----------|-------|
| Cauchy estimate on closed sphere | `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | (cf. `Liouville.lean:44` analogue) | **Requires `DiffContOnCl`, not `HasFPowerSeriesOnBall`** → R-? bridge needed (~5-10 LOC). |
| FPS ↔ iteratedFDeriv | `HasFPowerSeriesOnBall.factorial_smul` | `FDeriv/Analytic.lean:840` | One-step `k! • p k (fun _ ↦ y) = iteratedFDeriv 𝕜 k f x (fun _ ↦ y)`. Replaces S6's drifted `…factorial_smul_apply_iteratedFDeriv`. |
| iteratedFDeriv ↔ iteratedDeriv (1D) | `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` | `IteratedDeriv/Defs.lean:246` | In 1D the product collapses to `w^k`. Bonus path: `norm_iteratedFDeriv_eq_norm_iteratedDeriv` @ `Defs.lean:250` (Path B). |
| `ℕ` cast | `Complex.norm_natCast` (via `RCLike.norm_natCast`) | `RCLike/Basic.lean:633`, `@[simp 1100]` | S6d's R-1 "in-file precedent line 593-595 uses `abs_natCast`" was **grep-refuted by S6e** (`abs_natCast` is PHANTOM, 0 hits). |

**Open S7-ACT risks** (from S6d, status after S6e):

| # | Risk | Status |
|---|------|--------|
| R-1 | `Complex.abs_natCast` vs `…norm_natCast` | **Pinned** (S6e). Use `Complex.norm_natCast`. |
| R-4 | iteratedFDeriv ↔ iteratedDeriv bridge | **Pinned** (S6e). Use `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` @ `IteratedDeriv/Defs.lean:246`. |
| R-? | `DiffContOnCl` bridge (new in S6e) | **Open**. ~5-10 extra LOC to convert `HasFPowerSeriesOnBall.differentiableOn` (or analogue) into `DiffContOnCl` on the closed sub-ball — required by Mathlib's Cauchy estimate. |
| R-2, R-3, R-5 … R-10 | (7 remaining S6d risks) | Unaudited at v4.26.0 by S6e; review each before paste. See `2026-05-13-s6d-prep-s7-act-risk-register.md`. |

**Estimated S7 ACT length**: 60-90 LOC (S6e revision of S6d's 50-80 budget; +10-15 LOC accounts for the R-? `DiffContOnCl` bridge).

**Build instruction**: `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` (never `lake build` directly; per repo CLAUDE.md, direct `lake build` can OOM the host).

## Pool Status Note

This slug is now `completed` as of S7 ACT (2026-05-14, researcher-3). Zero sorries, zero axioms in `MeanValueTheoremOQ02OQ04OQ01.lean`. Docker-build verified at 7745 jobs from the worktree CWD.
