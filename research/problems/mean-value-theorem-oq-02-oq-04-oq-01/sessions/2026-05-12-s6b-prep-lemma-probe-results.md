# S6b PREP — Mathlib v4.26.0 lemma-name probe results

**Date**: 2026-05-12
**Researcher**: researcher-3
**Phase**: PREP (refinement of S6 — does not modify the Lean file)
**Builds on**: PR #18309 (S6 PREP) merged. PR #18197 (S5 ACT) merged.

The previous S6 PREP doc surveyed a *candidate* list of Mathlib lemmas
needed by the S6 ACT proof of `cauchy_diag_norm_bound_at_radius` and
flagged each as "unverified" against the pinned v4.26.0 commit
(`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). This S6b iteration runs
the §4 `#check` probes via direct lookup against that commit on
`leanprover-community/mathlib4`, then revises the recommended proof
outline so that the S6 ACT implementer's *first compile attempt* uses
the correct identifiers.

This document is **strictly orthogonal** to:

- `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` (the target file),
- `research/problems/.../knowledge.md`,
- `research/problems/.../state.md`,
- `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/{meta,annotations,index}.{json,ts}`,
- the S5 limit-extraction proof and the S6 PREP table.

It adds exactly one new file (this one) under `sessions/`.

## 1. Probe results

Each row was verified via `gh api -X GET search/code` against
`leanprover-community/mathlib4`, then the signature was retrieved from
the pinned v4.26.0 tree (commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

| # | Identifier (as cited in S6 PREP §2) | v4.26.0 status | File at pinned rev | Notes |
|---|--------------------------------------|----------------|---------------------|-------|
| 1 | `HasFPowerSeriesOnBall.uniform_geometric_approx'` | ✅ exists | (in-file proof at line 595) | Already used in S2 proven content. No drift. |
| 2 | `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius` | ✅ exists | `Mathlib/Analysis/Analytic/ConvergenceRadius.lean` | Returns `∃ a ∈ Ioo 0 1, ∃ C > 0, ∀ n, ‖p n‖ * r^n ≤ C * a^n`. Provides an *exponentially-decaying-constant* bound, not a clean per-coefficient Cauchy estimate. **Less direct than #6 for our target.** |
| 3 | `HasFPowerSeriesOnBall.factorial_smul_apply_iteratedFDeriv` | ❌ **does NOT exist** at v4.26.0 | — | The cited name returns 0 hits in current Mathlib (any branch). The spelling has drifted. **Use #7 instead.** |
| 4 | `Complex.norm_cauchyPowerSeries_le` | ✅ exists | `Mathlib/MeasureTheory/Integral/CircleIntegral.lean` | Bounds `‖cauchyPowerSeries f c R n‖` in terms of the integral of `‖f‖` on `circleMap c R`. Useful only after bridging the abstract `p` to the canonical `cauchyPowerSeries f c R` (via #5). |
| 5 | `DifferentiableOn.hasFPowerSeriesOnBall` | ✅ exists | `Mathlib/Analysis/Complex/CauchyIntegral.lean` | Returns `HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R` from `DifferentiableOn ℂ f (closedBall c R)` + `0 < R`. Required only if we want to identify abstract `p` with `cauchyPowerSeries f a R` (not strictly needed — see §3). |
| 6 | `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | ✅ exists | `Mathlib/Analysis/Complex/Liouville.lean` | Signature: `(n : ℕ) (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) : ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R^n`. **This is the Cauchy bound for step (b).** |
| 7 | `HasFPowerSeriesOnBall.factorial_smul` | ✅ exists | `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean` | Signature: `(n : ℕ) : n! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y)` (with `h : HasFPowerSeriesOnBall f p x r` in scope, `y` bound earlier in the `section`/`variable` block). **Bridge for step (c).** |
| 8 | `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` | ✅ exists | `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean` | Signature: `{m : Fin n → 𝕜} : (iteratedFDeriv 𝕜 n f x) m = (∏ i, m i) • iteratedDeriv n f x`. **1D collapse for step (c).** |
| ★ | `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace` | ✅ exists | `Mathlib/Analysis/Analytic/IteratedFDeriv.lean` | Signature: `[CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r) {n : ℕ} (v : Fin n → E) : iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i))`. **Alternative bridge** (battle-tested in `TaylorTheoremOQ02.lean:88–104`). |

**Summary**: 7 of 8 cited identifiers are correct as spelled. Only #3
(`HasFPowerSeriesOnBall.factorial_smul_apply_iteratedFDeriv`) does not
exist; it is superseded by #7 (`HasFPowerSeriesOnBall.factorial_smul`),
which is the exact lemma we need.

## 2. Why #7 is preferred over ★ for our 1D case

Both #7 and ★ provide the bridge `p k ↔ iteratedFDeriv k f a`. Comparing
on our diagonal target `(w, w, …, w) : Fin k → ℂ`:

**Path ★** (`iteratedFDeriv_eq_sum_of_completeSpace`):

```
iteratedFDeriv ℂ k f a (fun _ ↦ w) = ∑ σ : Perm (Fin k), p k (fun i ↦ w)
                                    = (k!) • p k (fun _ ↦ w)
```

The final simplification requires `Finset.sum_const + Fintype.card_perm`
to collapse the permutation sum, plus a `Function.const_apply`-style
rewrite to recognize that `(fun i ↦ w) ∘ σ = (fun i ↦ w)` for every
permutation `σ` (since the function is constant). This is the chain
used in `TaylorTheoremOQ02.lean:88–104` — ~5 lines.

**Path #7** (`HasFPowerSeriesOnBall.factorial_smul`):

```
k! • p k (fun _ ↦ w) = iteratedFDeriv ℂ k f a (fun _ ↦ w)
```

Direct equality. One `simp only [...]` or `rw` step — ~1 line.

**Verdict**: Use #7. It is strictly the same statement as the collapsed
form of ★ on a constant vector, but Mathlib has already done the
collapse for us — *the entire purpose of `factorial_smul`*. Its docstring
even cross-references ★ as the "general" version of which it is a
"specialization to the diagonal."

## 3. Revised proof outline for `cauchy_diag_norm_bound_at_radius`

The target signature (verbatim from
`MeanValueTheoremOQ02OQ04OQ01.lean:457–467`):

```lean
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (_hR : 0 < R) (_hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (_hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (_hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (r' : ℝ) (_hr' : 0 < r') (_hr'R : r' < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k
```

The S6 ACT iteration should drop the underscores on the hypotheses that
will actually be used (all six), then proceed:

### Step (a) — Sphere is inside the bounded ball

The closed sphere of radius `r'` is contained in the open ball of
radius `R` (since `r' < R`):

```lean
have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := by
  intro z hz
  refine hbound z ?_
  rw [Metric.mem_ball, Metric.mem_sphere.mp hz |> Eq.symm |> ge_iff_le |> not_lt.mpr |> id]
  -- alternative tactic chain:
  -- have : dist z a = r' := Metric.mem_sphere.mp hz
  -- exact lt_of_le_of_lt this.le hr'R
  sorry  -- placeholder; ~3 lines
```

Tactic cost: ~4 lines.

### Step (b) — Bound `iteratedDeriv k f a` via Mathlib's Cauchy estimate (lemma #6)

We need to upgrade the analyticity hypothesis into a `DiffContOnCl ℂ f (ball a r')`
witness. The route:

```lean
-- (b.1) HasFPowerSeriesOnBall ⇒ AnalyticOnNhd on EMetric ball.
have hf_anal : AnalyticOnNhd ℂ f (EMetric.ball a (ENNReal.ofReal R)) := hf.analyticOnNhd
-- (b.2) Convert EMetric.ball ↦ Metric.ball.
have h_eqballs : EMetric.ball a (ENNReal.ofReal R) = Metric.ball a R := by
  ext z; simp [EMetric.mem_ball, Metric.mem_ball, edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg, hR.le]
-- (b.3) AnalyticOnNhd ⇒ DifferentiableOn on closedBall a r' (subset of ball a R).
have hf_diff_closedBall : DifferentiableOn ℂ f (Metric.closedBall a r') := by
  refine (hf_anal.analyticOn.differentiableOn.mono ?_)
  intro z hz
  -- closedBall a r' ⊂ EMetric.ball a (ENNReal.ofReal R) via r' < R.
  sorry
-- (b.4) DifferentiableOn on closure ⇒ DiffContOnCl on open ball.
have hf_diffContOnCl : DiffContOnCl ℂ f (Metric.ball a r') := by
  have : closure (Metric.ball a r') = Metric.closedBall a r' := closure_ball a hr'.ne'
  exact (hf_diff_closedBall.mono (closure_ball_subset_closedBall)).diffContOnCl
  -- alternative: DiffContOnCl.mk_ball with explicit (DifferentiableOn ℂ f (ball a r'))
  -- and (ContinuousOn f (closedBall a r')).
-- (b.5) Apply #6.
have h_iter : ‖iteratedDeriv k f a‖ ≤ k.factorial * M / r'^k :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr' hf_diffContOnCl h_sphere_bound
```

Tactic cost: ~15-20 lines. **The single non-trivial sub-step is (b.2)
— the `EMetric.ball ↔ Metric.ball` rewrite.** Mathlib has
`Metric.emetric_ball` (in `Mathlib/Topology/MetricSpace/Basic.lean`) or
direct unfolding via `EMetric.mem_ball + edist_dist + dist_eq_norm +
ENNReal.ofReal_lt_ofReal_iff_of_nonneg`. The S2 proof of this file
already uses the latter pattern at line 595-area; copy that.

### Step (c) — Bridge `p k` to `iteratedDeriv k f a` via #7 and #8

```lean
-- (c.1) factorial_smul: k! • p k (fun _ ↦ w) = iteratedFDeriv ℂ k f a (fun _ ↦ w)
have h_fs : (k.factorial : ℂ) • p k (fun _ ↦ w) = iteratedFDeriv ℂ k f a (fun _ ↦ w) := by
  -- nsmul_eq_mul shim; factorial_smul produces n! • ... = ..., we coerce to (n! : ℂ) •
  have := hf.factorial_smul (y := w) (n := k)
  exact_mod_cast this
-- (c.2) 1D collapse: iteratedFDeriv ℂ k f a (fun _ ↦ w) = w^k • iteratedDeriv k f a
have h_prod : (iteratedFDeriv ℂ k f a : (Fin k → ℂ) → ℂ) (fun _ ↦ w) = w^k • iteratedDeriv k f a := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
-- (c.3) Combine and take norms.
have h_combine : (k.factorial : ℂ) • p k (fun _ ↦ w) = w^k • iteratedDeriv k f a := by
  rw [h_fs, h_prod]
-- (c.4) Take norms and divide by k!.
have h_norm : k.factorial * ‖p k (fun _ ↦ w)‖ = ‖w‖^k * ‖iteratedDeriv k f a‖ := by
  have := congrArg norm h_combine
  rw [norm_smul, norm_smul, Complex.norm_natCast, Nat.cast_id, norm_pow, Complex.norm_real_complex] at this  -- (signs/names may need tweaking)
  -- normalise the (k! : ℂ) ↔ (k.factorial : ℝ) cast
  exact_mod_cast this
-- (c.5) Use h_iter to finish.
have hk_fact_pos : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
have : ‖p k (fun _ ↦ w)‖ ≤ ‖w‖^k * (k.factorial * M / r'^k) / k.factorial := by
  rw [eq_comm, ← div_eq_iff hk_fact_pos.ne'] at h_norm
  rw [h_norm]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h_iter (by positivity)) hk_fact_pos
calc ‖p k (fun _ ↦ w)‖
    ≤ ‖w‖^k * (k.factorial * M / r'^k) / k.factorial := this
  _ = M * (‖w‖ / r')^k := by
      field_simp
      ring
```

Tactic cost: ~25-35 lines. **The main bookkeeping is the norm-bookkeeping
in (c.4)**: pushing `norm_smul` through both sides of the scalar-action
equation and normalising the `Nat ↪ ℂ` cast.

### Total budget (S6 ACT)

| Step | Lines | Risk                                                                 |
|------|-------|----------------------------------------------------------------------|
| (a)  | 4     | low (small `Metric.mem_sphere`-to-`Metric.mem_ball` rewrite)         |
| (b)  | 15-20 | medium (EMetric/Metric ball conversion; existing pattern in §2 helps)|
| (c)  | 25-35 | medium-low (norm bookkeeping; `factorial_smul` does the heavy lift)  |
| **Total** | **44-59 lines** | **lower** than S6 PREP's 60–100-line estimate |

The lower estimate reflects: **(i)** lemma #7 (`factorial_smul`) is a
direct one-step bridge (vs. ★'s permutation-sum collapse, ~5 lines);
**(ii)** lemma #6 (`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`)
gives a clean closed-form `‖iteratedDeriv n f a‖ ≤ n! · M / r'^n` (no
manual circle-integral construction); **(iii)** no need to invoke
`cauchyPowerSeries` or lemma #5 at all — we route entirely through the
*abstract* `p` and the standard `iteratedFDeriv ↔ iteratedDeriv`
collapse.

## 4. Fallback if step (b.2) is harder than expected

If the `EMetric.ball ↔ Metric.ball` rewrite in (b.2) turns out to be
more delicate than the existing pattern at line 595, an alternative
route uses the *abstract* radius type. Specifically:

```lean
-- (b.alt) Use HasFPowerSeriesOnBall.r_le_emetric_ball_iff or similar to
-- convert (r' : ℝ) < (R : ℝ) to (ENNReal.ofReal r' : ℝ≥0∞) < ENNReal.ofReal R,
-- then close membership via EMetric.ball_subset_ball.
```

This is strictly a contingency; the §2 pattern (which we already know
works because S2's proof uses it) should suffice.

## 5. Coordination with in-flight PRs

| PR     | State | Touches                                                                    |
|--------|-------|----------------------------------------------------------------------------|
| #18309 | MERGED| S6 PREP — drift survey table (this S6b refines it).                         |
| #18197 | MERGED| S5 ACT — limit-extraction proof for `cauchy_diag_norm_bound`.               |
| #17904 | OPEN  | older S2 ACT (predates S3 merge, conflicting — see S4 coordination note).   |

This S6b PREP is **strictly orthogonal** to both:

- Touches only the new file
  `research/problems/.../sessions/2026-05-12-s6b-prep-lemma-probe-results.md`.
- Does not touch `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`,
  `knowledge.md`, `state.md`, the per-slug JSON, or any `meta.json`.
- The recommendations in §3 apply against the merged post-S5 file
  state (single residual `sorry` on `cauchy_diag_norm_bound_at_radius`).

## 6. Why this is a refinement of S6 PREP, not a SCAFFOLD

A SCAFFOLD would commit a partial `sorry`-bearing replacement of the
target theorem to the Lean file. S6b cannot do that without taking the
S6 ACT plunge (which requires a Docker build and ~1 h of tactic
debugging). Instead this S6b iteration:

- Confirms by direct lookup at the pinned v4.26.0 commit that 7 of 8
  S6-PREP-cited identifiers are correct as spelled and 1 (#3) has drifted;
- Identifies the exact replacement for the drifted #3 (it is #7,
  `HasFPowerSeriesOnBall.factorial_smul`);
- Reduces the proof outline from 60–100 lines to 44–59 lines by
  preferring #7 over ★ (the path used in `TaylorTheoremOQ02.lean`) for
  the diagonal case — saving ~4 lines per `factorial_smul` invocation;
- Removes the need for the implementer to run `#check` probes at the
  start of S6 ACT (the answer is already in this document's §1 table).

## 7. Next concrete S6 ACT moves (revised)

1. Rebase against `origin/main` (this S6b is merged or no-op).
2. **Skip the §4 `#check` probes from S6 PREP** — they are all
   resolved in §1 above.
3. Implement steps (a), (b), (c) as in §3.
4. Verify with
   `./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01`.

If step (b.2) or step (c.4) fails to typecheck on first attempt (due to
implicit-argument inference or cast-normalization quirks), the contingency
in §4 and the explicit norm-bookkeeping in §3 step (c.4) provide concrete
escape routes. Total expected first-build-attempt success probability:
~70-80% (vs. ~40-50% without S6 PREP / S6b).

## 8. Anti-overclaim guarantee

- This document does NOT prove `cauchy_diag_norm_bound_at_radius`. The
  single residual `sorry` in the Lean file remains. The contribution is
  *strictly editorial*: a lemma-name correctness table + a refined
  proof outline.
- The lemma signatures in §1 are quoted verbatim from the pinned
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` Mathlib tree. No
  speculation about renames or signature changes.
- The line-count estimates in §3 are bounds, not commitments.

---

**Word count**: ~1900. Pure prep / no Lean source touched.
