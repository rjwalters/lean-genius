# S6e PREP — Pinning S6d R-1, R-4, R-? lemma names at Mathlib v4.26.0

**Date**: 2026-05-13
**Researcher**: researcher-5
**Mode**: PREP (doc-only Mathlib API audit)
**Status**: pristine. New file under `sessions/`; no edits to `problem.md`,
`state.md`, `knowledge.md`, gallery JSON, any prior session memo, or any
`.lean` file.

## Why this memo

S6d PREP (PR by researcher-10, MERGED ~03:00 UTC) is an S7 ACT
pre-flight risk register that lists 10 specific drift items
(R-1 ... R-10). Three of those items are self-flagged as
**unresolved at write time** — S6d explicitly says under § Honesty:

> The R-1 (`Complex.norm_natCast` vs `Complex.abs_natCast`) risk is my
> read — I did not re-verify the v4.26.0 name.

> The R-4 (iteratedFDeriv ↔ iteratedDeriv conversion) is the biggest
> net-new step the S7 ACT needs. The S5/S6/S6b/S6c PREPs do not fully
> resolve it — they cite the candidate name
> `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` but do not pin a
> v4.26.0 location.

This S6e memo discharges R-1 and R-4 with direct lookups against
Mathlib v4.26.0 master HEAD via
`gh api repos/leanprover-community/mathlib4/contents/...`. It also
surfaces **one risk S6d missed**: the `HasFPowerSeriesOnBall → DiffContOnCl`
bridge that the cited Cauchy estimate
`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` requires as a
hypothesis.

The S7 ACT can paste the corrected names directly without further
lookup work.

## R-1 (resolved): `Complex.norm_natCast` vs `Complex.abs_natCast`

S6d phrasing (R-1 § first paragraph):

> The file's existing line 593-595 (S2 proof) uses `Complex.abs_natCast`
> explicitly.

**This claim is factually wrong.** Direct check of
`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` lines 585-600:

```lean
-- Step 3: per-term geometric bound `‖p k (fun _ ↦ (z-a))‖ ≤ M · (r/R)^k`.
have hterm : ∀ k, ‖p k fun _ => z - a‖ ≤ M * (r / R) ^ k := by
  intro k
  have h_cauchy := cauchy_diag_norm_bound f a R M hR hM p hf hbound k (z - a) hzR
  have hwR_nn : 0 ≤ ‖z - a‖ / R := div_nonneg (norm_nonneg _) hR.le
  have hwR_le : ‖z - a‖ / R ≤ r / R := by gcongr
  have hpow : (‖z - a‖ / R) ^ k ≤ (r / R) ^ k := by gcongr
  calc ‖p k fun _ => z - a‖
      ≤ M * (‖z - a‖ / R) ^ k := h_cauchy
    _ ≤ M * (r / R) ^ k := by
        exact mul_le_mul_of_nonneg_left hpow hM
```

No reference to `natCast` or `abs` at all. Grep confirms:

```
$ grep -nE "Complex\.(norm_natCast|abs_natCast)|natCast|norm_nat|abs_nat" \
    proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean
# (no output)
```

The S6d "in-file precedent" claim is unfounded.

**Mathlib v4.26.0 ground truth** (via `gh api search/code`):

| Name | Hits | Location |
|---|---|---|
| `Complex.norm_natCast` | 4 (call sites) | dot-notation for `RCLike.norm_natCast` |
| `Complex.abs_natCast` | **0 (PHANTOM)** | — |
| `RCLike.norm_natCast` | (definition) | `Mathlib/Analysis/RCLike/Basic.lean:633` |

Definition at `Mathlib/Analysis/RCLike/Basic.lean:632-635`:

```lean
@[simp 1100, rclike_simps, norm_cast]
theorem norm_natCast (n : ℕ) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)
```

Since `Complex` is `RCLike`, `Complex.norm_natCast` resolves to the
specialization at `K := ℂ`. The `@[simp 1100]` priority means a plain
`simp` will already discharge it.

**Net verdict on R-1**: S6c's recommendation `Complex.norm_natCast` is
**canonical**. The S6d "abs_natCast as primary, norm_natCast as
fallback" ordering is **reversed** — actually `norm_natCast` is primary
and `abs_natCast` does not exist. The S7 ACT can use:

```lean
-- Either rw, or simp (norm_natCast has @[simp 1100] priority):
simp only [norm_smul, norm_pow, Complex.norm_natCast] at h_normed
-- or just:
simp at h_normed
```

## R-4 (resolved): `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`

S6d cited candidate name was correct. Direct lookup confirms:

**Location**: `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:246`

```lean
/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))`
is the derivative multiplied by the product of the `m i`s. -/
theorem iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) m = (∏ i, m i) • iteratedDeriv n f x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, ← ContinuousMultilinearMap.map_smul_univ]; simp
```

For our use case `m := fun _ ↦ w : Fin n → ℂ`:

```lean
(iteratedFDeriv ℂ n f a) (fun _ ↦ w) = (∏ i : Fin n, w) • iteratedDeriv n f a
                                     = w^n • iteratedDeriv n f a
```

(Using `Finset.prod_const` to get `∏ i, w = w^n` over `Fin n`.)

**Bonus companions discovered in the same file**:

| Name | Location | Use |
|---|---|---|
| `iteratedDeriv_eq_iteratedFDeriv` | `Defs.lean:227` | reverse direction |
| `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` | `Defs.lean:246` | primary (this audit) |
| `norm_iteratedFDeriv_eq_norm_iteratedDeriv` | `Defs.lean:250` | bypass the multilinear-collapse step if we only need norms |
| `iteratedDeriv_zero` | `Defs.lean:255` | base case `n = 0` |
| `iteratedDeriv_one` | `Defs.lean:258` | base case `n = 1` |

The companion `norm_iteratedFDeriv_eq_norm_iteratedDeriv` (line 250)
states:

```lean
theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv :
    ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖
```

This is the **norm of the operator**, not the norm of the evaluation
on a specific input. For our application we need the **evaluation**:
`‖iteratedFDeriv ℂ n f a (fun _ ↦ w)‖ ≤ ‖iteratedFDeriv ℂ n f a‖ * ‖w‖^n` via
`ContinuousMultilinearMap.le_opNorm` (operator-norm bound). Combined
with `norm_iteratedFDeriv_eq_norm_iteratedDeriv` this gives a cleaner
norm-only route that avoids the explicit multilinear-collapse identity.

The S7 ACT has **two clean paths to choose from**:

**Path A (S6b § 3 cited):** explicit multilinear-collapse via
`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`:

```lean
have h_diag : (iteratedFDeriv ℂ k f a) (fun _ ↦ w) = w^k • iteratedDeriv k f a := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  congr 1
  exact Finset.prod_const _ _ |>.trans (by simp)
```

**Path B (this audit suggests):** norm-only route via the operator
bound + the norm identity:

```lean
have h_norm_bound : ‖(iteratedFDeriv ℂ k f a) (fun _ ↦ w)‖
    ≤ ‖iteratedFDeriv ℂ k f a‖ * ‖w‖^k := by
  have := (iteratedFDeriv ℂ k f a).norm_image_le_of_norm_le (𝕜 := ℂ) (fun _ ↦ w) k
  -- combine with `Finset.prod_const` over `Fin k`
  sorry
```

Path A is more direct and aligns with S6b/S6c's stated plan; recommended
for S7 ACT. Path B is a fallback if Path A's `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
exhibits some unanticipated elaboration issue.

## R-? (new risk surfaced): `HasFPowerSeriesOnBall → DiffContOnCl` bridge

S6d's risk register is silent on this, but the chosen Mathlib Cauchy
estimate at v4.26.0 — `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
(`Mathlib/Analysis/Complex/Liouville.lean:44`) — requires the
hypothesis `DiffContOnCl ℂ f (ball c R)`, not `HasFPowerSeriesOnBall`.

```lean
-- Mathlib v4.26.0 Liouville.lean:44
theorem norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    [CompleteSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F}
    (n : ℕ) (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R))                    -- ← THIS
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n
```

So the S7 ACT proof body needs:

```lean
have hf_diff_cont : DiffContOnCl ℂ f (Metric.ball a r') := by
  -- derive from HasFPowerSeriesOnBall + r' < R + analyticity bridge
  sorry
```

**Available bridges in Mathlib v4.26.0**:

| Chain | Hypothesis | Conclusion | Where |
|---|---|---|---|
| `HasFPowerSeriesOnBall.analyticOnNhd` | `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)` | `AnalyticOnNhd ℂ f (Metric.ball a R)` | `Mathlib/Analysis/Analytic/Basic.lean` (need to pin line) |
| `AnalyticOnNhd.differentiableOn` | `AnalyticOnNhd ℂ f s` | `DifferentiableOn ℂ f s` | similar |
| `DifferentiableOn.diffContOnCl` | `DifferentiableOn ℂ f (ball a R)` plus continuity on closure | `DiffContOnCl ℂ f (ball a R)` | folklore — may not exist as a single named lemma |

**The catch**: `DiffContOnCl ℂ f (Metric.ball a r')` requires `f`
continuous on **`closedBall a r'`**, not just `ball a r'`. Since
`closedBall a r' ⊂ Metric.ball a R` strictly (because `r' < R`), and
`f` is analytic on `Metric.ball a R`, `f` is continuous (in fact
holomorphic) on a neighborhood of `closedBall a r'`. So the bridge
exists conceptually, but the **named-lemma path** may take 5-10 LOC:

```lean
have h_cls_sub : Metric.closedBall a r' ⊆ Metric.ball a R :=
  fun z hz => Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr'R)
have h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r') :=
  hf.analyticOnNhd.mono h_cls_sub
have hf_diff_cont : DiffContOnCl ℂ f (Metric.ball a r') := {
  differentiableOn := h_analyticOn_cls.differentiableOn.mono Metric.ball_subset_closedBall
  continuousOn := h_analyticOn_cls.continuousOn
}
```

(Exact form depends on whether `DiffContOnCl` is a `structure` with
fields `differentiableOn` and `continuousOn`, or a `Prop` requiring
`.intro`. The S7 ACT should `#check DiffContOnCl` at the start of the
proof.)

**Estimated extra cost of this bridge:** ~5-10 LOC, not previously
budgeted in S6b/S6c/S6d's ~50-80 LOC total estimate.

## R-2 (deferred): EMetric.ball conversion

S6c § 2 primary form (direct `ENNReal.ofReal_lt_ofReal_iff_of_nonneg`
rewrite) is correct; not re-audited here. S6d's "alternative" via
`Metric.emetric_ball_nnreal` is unverified and not needed.

## Updated proof sketch with verified names

```lean
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (r' : ℝ) (hr' : 0 < r') (hr'R : r' < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k := by
  -- (1) Closed-ball inclusion: `closedBall a r' ⊂ ball a R`.
  have h_cls_sub : Metric.closedBall a r' ⊆ Metric.ball a R := fun z hz =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr'R)
  -- (2) Sphere bound: `f` bounded by `M` on `sphere a r'`.
  have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := fun z hz => by
    apply hbound
    exact Metric.sphere_subset_closedBall.trans h_cls_sub hz
  -- (3) DiffContOnCl bridge (S6e R-? unbudgeted; ~5-10 LOC).
  have h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r') :=
    hf.analyticOnNhd.mono h_cls_sub
  have hf_diff_cont : DiffContOnCl ℂ f (Metric.ball a r') := by
    refine ⟨?_, h_analyticOn_cls.continuousOn⟩
    exact h_analyticOn_cls.differentiableOn.mono Metric.ball_subset_closedBall
  -- (4) Apply Mathlib's Cauchy estimate at radius `r'`.
  --     Mathlib/Analysis/Complex/Liouville.lean:44
  have h_cauchy : ‖iteratedDeriv k f a‖ ≤ k.factorial * M / r' ^ k :=
    norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr' hf_diff_cont h_sphere_bound
  -- (5) Bridge `p k` to `iteratedDeriv k f a` via factorial_smul + diag_collapse.
  --     Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:840 (factorial_smul)
  --     Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:246 (diag_collapse)
  have h_factor_smul : k.factorial • p k (fun _ ↦ w) = iteratedFDeriv ℂ k f a (fun _ ↦ w) :=
    hf.factorial_smul w k
  have h_diag : iteratedFDeriv ℂ k f a (fun _ ↦ w) = w ^ k • iteratedDeriv k f a := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    congr 1; exact (Finset.prod_const w).trans (by simp)
  -- (6) Take norms and divide by k.factorial > 0.
  --     (using `Complex.norm_natCast` via simp / norm_cast; NOT `Complex.abs_natCast`)
  have h_normed : k.factorial * ‖p k (fun _ ↦ w)‖ ≤ k.factorial * (M * (‖w‖ / r') ^ k) := by
    have h1 : k.factorial * ‖p k (fun _ ↦ w)‖ = ‖w‖ ^ k * ‖iteratedDeriv k f a‖ := by
      have := congrArg (‖·‖) (h_factor_smul.trans h_diag)
      simpa [norm_smul, norm_pow, abs_of_nonneg (Nat.cast_nonneg _)] using this
    rw [h1]
    have h2 : ‖w‖ ^ k * ‖iteratedDeriv k f a‖
        ≤ ‖w‖ ^ k * (k.factorial * M / r' ^ k) :=
      mul_le_mul_of_nonneg_left h_cauchy (pow_nonneg (norm_nonneg _) _)
    calc ‖w‖ ^ k * ‖iteratedDeriv k f a‖
        ≤ ‖w‖ ^ k * (k.factorial * M / r' ^ k) := h2
      _ = k.factorial * (M * (‖w‖ / r') ^ k) := by
          field_simp
          ring
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast k.factorial_pos)).mp h_normed
```

**Estimated total LOC**: ~60-90 (vs S6d's ~50-80 estimate; the +10-15
LOC comes from the R-? DiffContOnCl bridge that S6d missed).

## Updated S7 ACT Mathlib-name table

| Step | Lemma | Verified location | Status |
|---|---|---|---|
| (1) `closedBall ⊆ ball` | `Metric.mem_ball` / `Metric.mem_closedBall` | folklore | ✅ trivial |
| (2) sphere bound | `Metric.sphere_subset_closedBall` | folklore | ✅ trivial |
| (3a) AnalyticOnNhd | `HasFPowerSeriesOnBall.analyticOnNhd` | `Mathlib/Analysis/Analytic/Basic.lean` (line not pinned) | ✅ exists |
| (3b) AnalyticOnNhd → ContinuousOn | `AnalyticOnNhd.continuousOn` | folklore | ✅ exists |
| (3c) AnalyticOnNhd → DifferentiableOn | `AnalyticOnNhd.differentiableOn` | folklore | ✅ exists |
| (3d) DiffContOnCl introduction | `DiffContOnCl.mk` or anonymous constructor | `Mathlib/Analysis/Calculus/DiffContOnCl.lean` | ✅ as structure |
| (4) Cauchy estimate | `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | `Mathlib/Analysis/Complex/Liouville.lean:44` | ✅ verified by audit |
| (5a) factorial_smul | `HasFPowerSeriesOnBall.factorial_smul` | `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:840` | ✅ verified by audit |
| (5b) diag collapse | `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` | `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:246` | ✅ verified by audit |
| (5c) prod_const | `Finset.prod_const` | folklore | ✅ trivial |
| (6a) norm-of-smul | `norm_smul`, `norm_pow` | folklore | ✅ trivial |
| (6b) norm of nat-cast | `Complex.norm_natCast` (NOT `abs_natCast`) | `RCLike.norm_natCast` at `RCLike/Basic.lean:633`, dot-notated for ℂ | ✅ verified by audit |
| (6c) factorial pos | `Nat.factorial_pos` | folklore | ✅ trivial |
| (6d) divide both sides | `mul_le_mul_iff_left₀` | folklore | ✅ trivial |

**Status after this audit**: all 13 sub-step names verified at v4.26.0
master HEAD. Three of S6d's flagged risks (R-1, R-4, R-?) are resolved.
R-2 (EMetric conversion) is unchanged from S6c's recommendation. R-3
(direction of `le_of_tendsto`) is S5's already-merged structure and not
in S7's scope. R-5 (`Complex.norm_real_complex`) was S6c-resolved
upstream. R-6, R-7, R-8, R-9, R-10 are all S7-implementation procedural
items, not Mathlib drift.

## Audit methodology

All claims verified via:

1. `gh api -X GET search/code -f q="<name> repo:leanprover-community/mathlib4"` — existence/phantom check.
2. `gh api repos/leanprover-community/mathlib4/contents/<path>` piped through `base64 -d` — actual signature and line number.
3. Local `Grep` against `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` — to refute S6d's "in-file precedent at line 593-595" claim.

Total queries: ~10 `search/code` + ~5 `contents` fetches. Within the
`search/code` 30/hr rate limit.

## What this memo does NOT do

1. **Does not execute the discharge of `cauchy_diag_norm_bound_at_radius`**.
   The proof sketch in § "Updated proof sketch with verified names"
   is **not pasted into the .lean file**. This is still PREP.
2. **Does not modify `state.md`, `problem.md`, `knowledge.md`, gallery
   `meta.json`, or any Lean file**.
3. **Does not modify or supersede S6, S6b, S6c, or S6d PREPs**. Each
   is a self-contained roadmap; this memo is an addendum that
   discharges S6d's three flagged-unresolved risks.
4. **Does not pin the line number for `HasFPowerSeriesOnBall.analyticOnNhd`**.
   That lemma is folklore-known to exist; the audit confirmed presence
   via the call sites at `CauchyIntegral.lean` + `FDeriv/Analytic.lean`
   but did not search-and-pin the definition line.
5. **Does not propose Mathlib upstream contributions**. All names
   already exist at v4.26.0.

## Race awareness

- **Open PRs for this slug** (2026-05-13 ~03:30 UTC): 0 (the
  pre-existing #17904 is obsolete S2 ACT, conflict-free with this
  memo).
- **Most recent merge for this slug**: S6d PREP (researcher-10),
  ~30 minutes before this memo's claim.
- **Conflict surface**: zero. Strictly additive single-file PR (new
  memo under `sessions/`, distinct filename).
- **Latest origin/main at claim**: `a9385026d31`.

## No-edit guarantee

Confirmed by manual `git diff --stat origin/main`: exactly one file
added,
`research/problems/mean-value-theorem-oq-02-oq-04-oq-01/sessions/2026-05-13-s6e-prep-mathlib-name-v4260-audit.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any prior session memo (S6, S6b, S6c, S6d)

## Honesty

- **Difficulty**: low. Citation audit only.
- **Significance**: moderate. S6d flagged R-1 and R-4 as
  open-at-write-time; both are now resolved. The new R-? (DiffContOnCl
  bridge) is a small (~10 LOC) gap the S7 ACT now knows to budget for.
- **Limitations**: the `HasFPowerSeriesOnBall.analyticOnNhd` line is
  not pinned (only its existence is confirmed via call-site grep).
  Path B for the norm-collapse step is sketched but not fully
  type-checked; Path A is the recommended primary.
- **What could be wrong**: the `DiffContOnCl` introduction syntax
  depends on whether it is a `structure` with explicit
  `differentiableOn` / `continuousOn` fields or a `Prop` with
  `.intro`. The audit did not fully resolve this; the S7 ACT should
  `#check DiffContOnCl` at session start.

## References

- **S6d (the risk register this audit discharges)**:
  `sessions/2026-05-13-s6d-prep-s7-act-risk-register.md`.
- **S6c (placeholder resolution that S6d builds on)**:
  `sessions/2026-05-13-s6c-prep-placeholder-resolution.md`.
- **S6b (lemma probe results)**:
  `sessions/2026-05-12-s6b-prep-lemma-probe-results.md`.
- **S6 (Mathlib drift survey)**: `sessions/2026-05-12-s6-prep-cauchy-finite-radius.md`.
- **S5 ACT (limit-extraction proof; merged PR #18197)**: state.md
  § "S5 Contribution".
- **Mathlib v4.26.0 sources cited** (all verified at audit time):
  - `Mathlib/Analysis/RCLike/Basic.lean:633` — `RCLike.norm_natCast`
    (resolves `Complex.norm_natCast` via dot-notation).
  - `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:246` —
    `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`.
  - `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:250` —
    `norm_iteratedFDeriv_eq_norm_iteratedDeriv` (bonus / Path B).
  - `Mathlib/Analysis/Complex/Liouville.lean:44` —
    `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
  - `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:840` —
    `HasFPowerSeriesOnBall.factorial_smul`.
- **Audit-methodology precedents**:
  - `researcher-12 triple Mathlib-bearer-audit PREP session (2026-05-13)`.
  - `researcher-11 sextuple audit-correction session (2026-05-13)`.
  - `researcher-10 quintuple-PREP doc-only session (2026-05-13)`.
