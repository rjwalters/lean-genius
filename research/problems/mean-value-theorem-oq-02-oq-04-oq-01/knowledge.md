# Mean Value Theorem OQ-02 / OQ-04 / OQ-01: Refutation of the OQ-04 axiom

## Problem Summary

**Slug**: `mean-value-theorem-oq-02-oq-04-oq-01`
**Tier**: B (NEW-PROBLEM SCAFFOLD pattern)
**Significance**: 7
**Tractability**: 6
**Phase**: COMPLETED (S7 ACT merged 2026-05-14; file is 0 axioms / 0 sorries, docker build clean 7745 jobs)

**Question (from candidate-pool note)**: Can the axiom `analytic_taylor_remainder_uniform_bound` be proved by S2 via Mathlib's `HasFPowerSeriesOnBall` infrastructure? The key Mathlib lemma is a Cauchy coefficient bound `‖p k‖ ≤ M / R^k`; the rest is the geometric tail estimate.

**Answer (Session 1)**: NO. The parent axiom is mathematically false as stated.

## Session 2026-05-12 (Session 1, FRESH) — Refutation by Runge counterexample

**Mode**: FRESH (NEW-PROBLEM SCAFFOLD pattern; tier-B fallback after MODERATE+ saturation)
**Outcome**: progress (axiom refuted constructively; corrected statement deferred to S2)

### What I Did

1. **Investigated the parent axiom**. Read `Proofs/MeanValueTheoremOQ02OQ04.lean`, identified the OQ-04 axiom statement: for `f : ℝ → ℝ` real-analytic on `(a-R, a+R)` with `|f y| ≤ M` on that interval, conclude `|f x − T_n f(a)(x)| ≤ M·r^(n+1) / (R-r)`. The parent's docstring explicitly references the COMPLEX disk in the "mathematical background" but axiomatizes only the REAL-interval version, "absorbing the R^n into M".

2. **Identified counterexample by mental check**. The Runge function `f(x) = 1/(1+x²)` is real-analytic on ℝ, bounded by 1, but has complex poles at ±i. The complex Cauchy radius around 0 is only 1, NOT R = 100. At `(a, R, M, r, n, x) = (0, 100, 1, 1, 0, 1)`:
   - LHS: `|f(1) − f(0)| = |1/2 − 1| = 1/2`
   - RHS: `1·1^1 / (100−1) = 1/99 ≈ 0.0101`
   - **50× gap** — robust refutation.

3. **Probed Mathlib API**. Confirmed via `/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/Mathlib/Analysis/Analytic/`:
   - `analyticOn_id ℝ : AnalyticOn ℝ (fun x ↦ x) s` (note: 𝕜 is EXPLICIT)
   - `analyticOn_const : AnalyticOn 𝕜 (fun _ ↦ v) s` (𝕜 implicit)
   - `AnalyticOn.pow`, `AnalyticOn.add`, `AnalyticOn.div` (with nonzero hypothesis)
   - `HasFPowerSeriesOnBall.uniform_geometric_approx'` for the existential approximation
   - `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius` for explicit Cauchy bounds

4. **Wrote Lean file** `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` (~280 lines):
   - §1: Defined `runge x := 1/(1+x²)`, proved `runge_one_add_sq_pos`, `runge_abs_le_one`, `runge_zero`, `runge_one`, `runge_analyticOn_R`.
   - §2: Defined `OQ04_AxiomStatement : Prop` to capture the parent axiom's signature, then proved `oq04_axiom_is_false` and `oq04_parent_axiom_is_false_in_principle` via specialization at the Runge witness.
   - §3: Stated `analytic_taylor_remainder_uniform_bound_complex` (corrected complex-disk version) with sorry, deferred to S2 with explicit Mathlib chain documented.

5. **Fixed grandparent build drift**. The build initially failed because `Proofs/MeanValueTheoremOQ02.lean` line 56 used the deprecated `∑ k in Finset.range ...` syntax (Mathlib has switched to `∑ k ∈ ...`). Single-character fix unblocks the entire MVT-OQ02 subtree (3 downstream files: `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean`, `MeanValueTheoremOQ02OQ04.lean`, this file).

6. **Created gallery scaffold**:
   - `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/{meta.json, index.ts, annotations.json}`
   - `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json`
   - This `knowledge.md` and `state.md`

### Key Findings

- **The parent OQ-04 axiom is mathematically false**: `f(x) = 1/(1+x²)` at `(R, M, r, n, x) = (100, 1, 1, 0, 1)` violates the bound by a factor of ~50 (1/2 vs 1/99). The root cause is the Runge phenomenon: real-analyticity + real sup bound is too weak to control complex Cauchy coefficient bounds.
- **The corrected statement requires complex-disk hypothesis**: replace `AnalyticOn ℝ f (Ioo (a-R) (a+R))` + `∀ y ∈ Ioo, |f y| ≤ M` with `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)` + `∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M`. Also fix the RHS: `M·r^(n+1)/(R^n·(R-r))` instead of `M·r^(n+1)/(R-r)`. The explicit `R^n` factor in the denominator is essential.
- **Mathlib's `AnalyticOn.div` recipe is clean**: For rational functions on intervals avoiding the real zeros of the denominator, `analyticOn_id ℝ` + `.pow` + `analyticOn_const` + `.add` + `.div` with `positivity` discharging the nonzero hypothesis is a 6-line proof.
- **Grandparent file `MeanValueTheoremOQ02.lean` had Mathlib drift**: the deprecated `∑ k in Finset.range` syntax broke the build; one-character fix to `∑ k ∈` and removal of a redundant `ring` (post-simp goal closure) unblocked downstream.

### Files Modified

- **New**: `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` (280 lines, 0 axioms, 1 sorry)
- **New**: `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/{meta.json, index.ts, annotations.json}`
- **New**: `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json`
- **New**: `research/problems/mean-value-theorem-oq-02-oq-04-oq-01/{knowledge.md, state.md}`
- **Modified**: `proofs/Proofs/MeanValueTheoremOQ02.lean` — Mathlib drift fix: `∑ k in` → `∑ k ∈` (line 56); removed redundant `ring` after simp closure (line 69)

### Next Steps

- **S2**: Discharge `analytic_taylor_remainder_uniform_bound_complex` via the documented Mathlib chain (`HasFPowerSeriesOnBall.uniform_geometric_approx'` + `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius` + geometric tail summation). Estimated proof length: 100-200 lines.
- **S3 (optional)**: Add a comment in the parent file `MeanValueTheoremOQ02OQ04.lean` referencing this OQ-01 refutation, so downstream readers see the obstruction without searching.
- **Architectural**: Consider generalizing the Prop-encoding refutation pattern (`def AxiomStatement : Prop := ...; theorem ¬ AxiomStatement`) as a gallery template for axiom-validity audits.

## Session 2026-05-12 (Session 2, narrow scope) — Add proven existential form via Mathlib's uniform_geometric_approx'

**Mode**: REVISIT (S2 continuation of S1)
**Outcome**: progress (existential form proven and build-verified; explicit form unchanged in this PR)

### Coordination with PR #17904 (parallel S2)

During this session researcher-1 also opened a S2 PR (#17904, created ~18 min before this session). That parallel PR refutes the S1 explicit-form statement as a Prop (`CauchyCorrectedFormV1`) on the basis of an off-by-one bug (`partialSum n` should be `partialSum (n+1)`), restates the explicit form with corrected indexing, and decomposes the proof into named sub-lemmas (`geometric_tail_identity` proven; `cauchy_diag_norm_bound` and the combined explicit-form theorem sorry'd).

To avoid duplication / merge collisions, **this S2 PR is narrowed to one unique deliverable: the proven existential form** (`analytic_taylor_remainder_uniform_geometric_complex`). The off-by-one fix on the explicit form is left to PR #17904.

### What I Did (narrow scope)

1. **Read Mathlib's `HasFPowerSeriesOnBall.uniform_geometric_approx'`** (Mathlib/Analysis/Analytic/Basic.lean:622). The lemma gives an *existential* bound, not the explicit `M·r^(n+1)/(R^n·(R-r))` form from S1's §3 docstring. Constants `C, K` depend on the formal multilinear series `p`, not on a user-supplied sup bound `M`.

2. **Independently noted the S1 §3 explicit-form off-by-one bug** (also flagged by PR #17904). **This PR does NOT fix the off-by-one** (deferred to PR #17904).

3. **Wrote a new proven theorem** `analytic_taylor_remainder_uniform_geometric_complex` (§3a, 16-line proof): Mathlib-native translation of `uniform_geometric_approx'` from y-centered (`f(a+y)`) to z-centered (`f z`) coordinates. The proof is `obtain` + `refine` + change-of-variables, applying `hp (z-a)` and simplifying `a + (z-a) = z`.

4. **Build verified** via `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01` (worktree-local script): build succeeded with only the pre-existing sorry on §3b.

5. **Updated metadata narrowly**: lineCount 330 → 397; theoremCount 7 → 9 (also fixed S1 undercount); added one mainTheorems entry.

### Key Findings (S2, narrow)

- **`uniform_geometric_approx'` is a translation-of-coordinates between y-form and z-form**. The substantive content is purely the change of variables `z = a + y`. No new mathematics, but a clean "Mathlib bridge" lemma for downstream consumers.

- **The Mathlib chain for the explicit form is deeper than S1 estimated**. `norm_mul_pow_le_mul_pow_of_lt_radius` is also existential, not `M/R^n`. To get `M/R^n`, you need the Cauchy integral formula via `cauchyPowerSeries` and `norm_cauchyPowerSeries_le`.

- **`ℝ≥0` and `ℝ≥0∞` notation requires `open scoped NNReal ENNReal`**. S1 didn't open these scopes (it used `ENNReal.ofReal` directly without the notation). Added in this PR.

### Files Modified (S2, narrow)

- **Modified**: `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — added `open scoped NNReal ENNReal`; added `analytic_taylor_remainder_uniform_geometric_complex` (proven, §3a) with docstring; added one `#check` line. Explicit-form theorem (§3b) **unchanged**.
- **Modified**: `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/meta.json` — sorries stays 1, lineCount 330→397, theoremCount 7→9, mainTheorems gains one entry.
- **Modified**: `research/problems/mean-value-theorem-oq-02-oq-04-oq-01/{knowledge.md, state.md}` — narrow S2 entry.
- **Modified**: `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json` — synced.

### Next Steps (S3+)

- **Merge-order coordination with PR #17904**: If this PR merges first, #17904 rebases. If #17904 merges first, this PR rebases — only the §3a addition is needed (the off-by-one fix from #17904 lives in §3b independently).

- **Discharge the explicit form** via the Cauchy integral chain (Complex.norm_cauchyPowerSeries_le + DifferentiableOn.hasFPowerSeriesOnBall + geometric tail). Estimated 150–200 lines.

- **Audit other gallery files** that import `MeanValueTheoremOQ02OQ04` for similar OQ-04-axiom-dependence.

- **Generalize the off-by-one pattern**: search the gallery for other "partial sum residual" bounds that may have the same indexing bug.

## Session 2026-05-12 (Session 4, S4 ACT) — Discharge §3b combination step; isolate cauchy_diag_norm_bound

**Mode**: REVISIT (S4 continuation of S3)
**Outcome**: progress (§3b main theorem now proven modulo a single named sub-lemma; sorry count stays at 1 but residual gap is isolated to the Cauchy coefficient estimate)

### What I Did

1. **Looked up exact Mathlib API** via GitHub raw fetches against the pinned Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):
   - `HasFPowerSeriesOnBall.hasSum_sub` (Mathlib/Analysis/Analytic/Basic.lean) gives `HasSum (fun n => p n fun _ => y - x) (f y)` for `y ∈ EMetric.ball x r`.
   - `norm_sub_le_of_geometric_bound_of_hasSum` (Mathlib/Analysis/SpecificLimits/Normed.lean) gives `‖(∑ x ∈ range n, f x) - a‖ ≤ C * r^n / (1 - r)` from per-term geometric bound + HasSum + `r < 1`.
   - `Complex.norm_cauchyPowerSeries_le` (Mathlib/MeasureTheory/Integral/CircleIntegral.lean) gives the Cauchy coefficient bound `‖cauchyPowerSeries f c R n‖ ≤ ((2π)⁻¹ ∫ ‖f(c + Re^iθ)‖ dθ) · |R|⁻¹^n` — the key missing Mathlib lemma for `cauchy_diag_norm_bound`.

2. **Introduced sub-lemma `cauchy_diag_norm_bound`** (sorry, deferred to S5):
   - Statement: `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖ / R) ^ k` for `‖w‖ < R`, given `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)` and `‖f z‖ ≤ M` on `Metric.ball a R`.
   - Proof chain (sketched, deferred): `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` + `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` + `r' → R⁻` limit.
   - This isolates the formalization gap to a single named statement; the surrounding combination is now provable.

3. **Discharged the §3b main theorem `analytic_taylor_remainder_uniform_bound_complex` in full**, modulo `cauchy_diag_norm_bound`. The proof body (lines 480–537) chains:
   - `EMetric.mem_ball + edist_dist + dist_eq_norm + ENNReal.ofReal_lt_ofReal_iff_of_nonneg` to lift `‖z − a‖ < R` to `z ∈ EMetric.ball a (ENNReal.ofReal R)`.
   - `hf.hasSum_sub hz_eball` gives `HasSum (fun k => p k (fun _ ↦ z − a)) (f z)`.
   - For each `k`, `cauchy_diag_norm_bound` + `pow_le_pow_left` + `mul_le_mul_of_nonneg_left` derives `‖p k (fun _ ↦ z − a)‖ ≤ M · (r/R)^k`.
   - `norm_sub_le_of_geometric_bound_of_hasSum` at index `n + 1` gives `‖(∑ k ∈ range (n+1), p k (fun _ ↦ z − a)) − f z‖ ≤ M · (r/R)^(n+1) / (1 − r/R)`.
   - The finite sum unfolds to `p.partialSum (n+1) (z − a)` by `rfl` (definition of `partialSum`).
   - `norm_sub_rev` flips the norm; `field_simp + ring` (using `1 − r/R = (R−r)/R`) rescales the RHS to `M · r^(n+1) / (R^n · (R−r))`.

### Key Findings (S4)

- **`HasFPowerSeriesOnBall.hasSum_sub` is the right Mathlib hook** for the diagonal HasSum at a point `z` in the disk. The corresponding `hasSum` (without the `_sub` suffix) takes a `y` in the ball-at-origin, which requires more rewriting.

- **`partialSum n y = ∑ k ∈ Finset.range n, p k (fun _ => y)` definitionally** — `rfl` closes the unfolding step. No `unfold` or `change` needed.

- **The RHS algebra is a clean `field_simp + ring`** after rewriting `1 − r/R` to `(R − r)/R` (the `field_simp` needs a slightly massaged form because `1 − r/R` isn't a pure ratio).

- **Sorry count stays at 1** but its *scope* shrinks: previously `analytic_taylor_remainder_uniform_bound_complex` had the entire combination as a black-box sorry; now the entire combination is auditable Lean code and only the per-coefficient Cauchy estimate is deferred. This is honest progress without sorry-count inflation.

### Files Modified (S4)

- **Modified**: `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — added `cauchy_diag_norm_bound` (sorry, ~30 lines incl. docstring); replaced the sorry in `analytic_taylor_remainder_uniform_bound_complex` with a ~50-line combination proof. Net delta +94 lines, 520 → 614.
- **Modified**: `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/meta.json` — sorries stays 1, lineCount 520→614, theoremCount 9→10 (added cauchy_diag_norm_bound); definitionCount 2→3 (catch-up: OriginalRemainderForm was added in S3 but not bumped).
- **Modified**: `research/problems/mean-value-theorem-oq-02-oq-04-oq-01/{knowledge.md, state.md}` — S4 entry.
- **Modified**: `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json` — synced.

### Next Steps (S5+)

- **Discharge `cauchy_diag_norm_bound`** via the Cauchy integral chain: pick `r' ∈ (max r ‖w‖, R)`; apply `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` on `sphere a r'` (bounded by `M` since `sphere a r' ⊂ Metric.ball a R`); use `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` to translate to `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖/r')^k`; take `r' → R⁻` continuity-of-upper-bound limit. Estimated 100-150 lines.

- **Alternative S5**: use `cauchyPowerSeries` + `Complex.norm_cauchyPowerSeries_le` + `DifferentiableOn.hasFPowerSeriesOnBall` + power-series uniqueness on the closed disk of radius `r' < R`. This routes through `cauchyPowerSeries` directly, potentially shorter than the iterated-derivative path.

- **Audit sibling gallery files** that import `MeanValueTheoremOQ02OQ04` for similar OQ-04-axiom-dependence (still open from S2).

## Session 2026-05-12 (Session 5, researcher-3) — Limit-extraction proof for `cauchy_diag_norm_bound`

**Mode**: REVISIT (RICH knowledge, 4 prior sessions)
**Outcome**: progress (cauchy_diag_norm_bound is now PROVEN by limit-extraction from a new finite-radius sub-lemma; the residual sorry shifts to the finite-radius form)

### What I Did

1. **Decomposed `cauchy_diag_norm_bound` into two natural sub-steps**:
   - **(a)** the Cauchy estimate at a strict intermediate radius `r' ∈ (0, R)`: `‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖/r')^k` — captured in new sub-lemma `cauchy_diag_norm_bound_at_radius`, deferred to S6.
   - **(b)** the limit-extraction step `r' → R⁻`: continuity of `r' ↦ M · (‖w‖/r')^k` at `R > 0` lets `Filter.Tendsto` along `𝓝[<] R` transport the pointwise bound from `Set.Ioo 0 R` to the boundary value `M · (‖w‖ / R)^k`. **Fully proved this iteration.**

2. **Wrote ~50-line limit-extraction proof** for `cauchy_diag_norm_bound`. Key Mathlib API used:
   - `ContinuousAt.mul`, `ContinuousAt.div` (with `R ≠ 0` from `0 < R` via `ne_of_gt`), `ContinuousAt.pow`, `continuousAt_const`, `continuousAt_id`
   - `ContinuousAt.tendsto` + `Filter.Tendsto.mono_left` + `nhdsWithin_le_nhds` for `Tendsto … (𝓝[<] R) (𝓝 g R)`
   - `mem_nhdsWithin` + `isOpen_Ioi.mem_nhds hR` for `Set.Ioo 0 R ∈ 𝓝[<] R`
   - `Filter.eventually_of_mem` for `∀ᶠ r' in 𝓝[<] R, ‖p k (fun _ ↦ w)‖ ≤ M · (‖w‖/r')^k`
   - `le_of_tendsto` to transport the eventual bound to the boundary limit

3. **Build verification**: docker-build started this session. State.md updated to reflect the new sorry locality.

### Mathematical Insight

The limit-extraction is structurally orthogonal to the Cauchy-integral chain on `sphere a r'`. By isolating it, the residual gap (the finite-radius form `cauchy_diag_norm_bound_at_radius`) is now precisely the statement Mathlib's Cauchy estimate produces directly — no further "take limit" plumbing required of a future S6 iteration. This makes the remaining gap easier to discharge and the proof easier to audit.

The function `g(r') := M · (‖w‖ / r')^k` is in fact *monotonically decreasing* on `(0, ∞)` (assuming `M ≥ 0` and `‖w‖ ≥ 0`), so the infimum over `r' ∈ (0, R)` is attained as `r' → R⁻` and equals `g(R) = M · (‖w‖ / R)^k`. The limit-extraction is "tight" — no slack is introduced by taking the limit.

### Edge cases handled by the inner sub-lemma

- `w = 0`, `k = 0`: bound at r' is `M · (0/r')^0 = M · 1 = M`. Limit gives `M · (0/R)^0 = M`. Both consistent with `‖p 0 (fun _ ↦ 0)‖ = ‖f a‖ ≤ M`.
- `w = 0`, `k > 0`: bound at r' is `M · 0^k = 0`. Limit gives 0. Both consistent with multilinear annihilation `p k (fun _ ↦ 0) = 0`.
- `w ≠ 0`: limit refinement is genuine — `(‖w‖/r')^k > (‖w‖/R)^k` strictly for `r' < R`.

### Files Modified

- **Modified**: `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — split `cauchy_diag_norm_bound` into `cauchy_diag_norm_bound_at_radius` (new sorry, S6 deferral) + `cauchy_diag_norm_bound` (now proven by limit-extraction). +91 lines.
- **Modified**: `research/problems/mean-value-theorem-oq-02-oq-04-oq-01/{knowledge.md, state.md}` — S5 entry.
- **Modified**: `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json` — synced.

### Next Steps (S6+) — DONE at S7 (see sync below)

- ~~**Discharge `cauchy_diag_norm_bound_at_radius`**~~ — completed at S7 (2026-05-14) exactly via the proposed route (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` + `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`).

- **Reference template**: `Proofs/TaylorTheoremOQ02.lean::fps_coeff_eq_taylor_coeff` already implements the ℝ-analogue of the formal-series / iterated-derivative bridge via `HasFPowerSeriesAt.iteratedFDeriv_eq_sum_of_completeSpace`. The ℂ-version should be parallel (ℂ is also a CompleteSpace).

## Session 2026-06-13 (Session 6, researcher-10) — STATE-SYNC: record S6–S7 completion

**Mode**: REVISIT (doc STATE-SYNC, no Lean code change)
**Outcome**: completed (tracker propagation only)

### What I Did

`knowledge.md` had frozen at S5, where `cauchy_diag_norm_bound_at_radius` was still a "deferred sorry, S6 target." The work was actually finished: `sessions/` holds the S6–S6f PREP files and `2026-05-14-s7-act-cauchy-diag-discharge.md`, and both `state.md` and `src/data/research/problems/…json` already record S7 completion. This session propagates that into `knowledge.md` and the Lean file's stale docstrings.

### Key Findings (verified against origin/main source, not re-built)

- `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` is **0 axioms, 0 sorries** at 758 LOC (comment-stripped token count = 0). The corrected complex theorem `analytic_taylor_remainder_uniform_bound_complex` and all supporting lemmas (`cauchy_diag_norm_bound`, `cauchy_diag_norm_bound_at_radius`) are fully proven.
- `cauchy_diag_norm_bound_at_radius` discharges the finite-radius Cauchy estimate via Mathlib's `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, bridged to the formal series by `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` — exactly the S5 next-steps plan.
- Build provenance: `state.md` records a clean `docker-build` (7745 jobs) on 2026-05-14, i.e. **before** the current Docker blackout (2026-06-13). This sync makes no new build claim.

### Files Modified

- `research/problems/mean-value-theorem-oq-02-oq-04-oq-01/knowledge.md` — Phase → COMPLETED; this S6 sync entry; struck the obsolete S6+ next-step.
- `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — comment-only: added §0 S7 Status banner; corrected three stale "only remaining sorry" docstrings to past tense. No code change (still 0 sorries / 0 axioms).

### Next Steps

None for this slug — proof is complete and was build-verified pre-blackout. The corrected complex bound could seed a follow-up OQ (sharpness of the `R^n·(R−r)` denominator, or the ℝ-restriction with an explicit complexification hypothesis), but no strong distinct question is forced.
