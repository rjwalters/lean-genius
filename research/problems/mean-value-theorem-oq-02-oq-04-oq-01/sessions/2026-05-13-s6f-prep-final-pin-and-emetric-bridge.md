# S6f PREP — Final pin of S6e's three unpinned items + new EMetric.ball bridge

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only Mathlib API audit)
**Status**: pristine. New file under `sessions/`; no edits to `problem.md`,
`state.md`, `knowledge.md`, gallery JSON, any prior session memo, or any
`.lean` file.

## Why this memo

S6e PREP (researcher-5, PR #18536, merged 2026-05-13) discharged S6d's
R-1 and R-4 risks and surfaced the new R-? `DiffContOnCl` bridge. But
S6e itself explicitly left three items **unpinned at v4.26.0**:

> Limitations: the `HasFPowerSeriesOnBall.analyticOnNhd` line is not
> pinned (only its existence is confirmed via call-site grep). Path B
> for the norm-collapse step is sketched but not fully type-checked;
> Path A is the recommended primary.

> What could be wrong: the `DiffContOnCl` introduction syntax depends
> on whether it is a `structure` with explicit `differentiableOn` /
> `continuousOn` fields or a `Prop` with `.intro`. The audit did not
> fully resolve this; the S7 ACT should `#check DiffContOnCl` at session
> start.

This memo pins both — plus surfaces **a new type-mismatch risk** that
S6e's proof sketch quietly contains: `HasFPowerSeriesOnBall.analyticOnNhd`
returns `AnalyticOnNhd 𝕜 f (EMetric.ball x r)`, not
`AnalyticOnNhd 𝕜 f (Metric.ball x R)`, so S6e's `hf.analyticOnNhd.mono h_cls_sub`
with `h_cls_sub : Metric.closedBall a r' ⊆ Metric.ball a R` is a
**type-mismatched application** as written. A one-line EMetric ↔ Metric
bridge (`Metric.emetric_ball`) fixes it.

The S7 ACT can paste S6e's updated sketch only **after** applying the
three corrections below; this memo gives the corrected proof body so
the next session is a true paste step.

## Lake-manifest pin

All audit queries below target Mathlib revision
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (matches `proofs/lake-manifest.json`,
same SHA as S6e). Audit method: `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` piped through `base64 -d`.

## Item 1 (resolved): `HasFPowerSeriesOnBall.analyticOnNhd` — pinned location and **EMetric** caveat

**Location**: `Mathlib/Analysis/Analytic/ChangeOrigin.lean:366-368`.

```lean
theorem HasFPowerSeriesOnBall.analyticOnNhd (hf : HasFPowerSeriesOnBall f p x r) :
    AnalyticOnNhd 𝕜 f (EMetric.ball x r) :=
  fun _y hy => hf.analyticAt_of_mem hy
```

**The trap** (S6e quietly missed): the conclusion is
`AnalyticOnNhd 𝕜 f (EMetric.ball x r)`, with `r : ℝ≥0∞`. In our setting
`r = ENNReal.ofReal R`. So `hf.analyticOnNhd` gives:

```
AnalyticOnNhd ℂ f (EMetric.ball a (ENNReal.ofReal R))
```

S6e's sketch wrote:

```lean
have h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r') :=
  hf.analyticOnNhd.mono h_cls_sub                                    -- ✗ TYPE MISMATCH
```

with `h_cls_sub : Metric.closedBall a r' ⊆ Metric.ball a R`. The `.mono`
call would need both sets to be of the same type; `Metric.ball a R` and
`EMetric.ball a (ENNReal.ofReal R)` are different objects (one is a
`Set ℂ` viewed via the metric structure, the other via the EMetric
structure; they are extensionally equal as sets but not the same term).

**Bridge available**: `Metric.emetric_ball` at
`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:945`:

```lean
theorem Metric.emetric_ball {x : α} {ε : ℝ} :
    EMetric.ball x (ENNReal.ofReal ε) = ball x ε := by
  ...
```

No hypothesis on `ε`. So we can rewrite `EMetric.ball a (ENNReal.ofReal R) = Metric.ball a R` directly.

The corrected pattern is:

```lean
have h_analyticOn_R : AnalyticOnNhd ℂ f (Metric.ball a R) := by
  have h := hf.analyticOnNhd                 -- AnalyticOnNhd ℂ f (EMetric.ball a (ENNReal.ofReal R))
  rwa [Metric.emetric_ball] at h
have h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r') :=
  h_analyticOn_R.mono h_cls_sub
```

**Compatibility note**: this matches the in-file precedent at
`MeanValueTheoremOQ02OQ04OQ01.lean:582-584` which already navigates the
EMetric ↔ Metric boundary:

```lean
-- in-file precedent (S2 era, line 582-584):
have hz_eball : z ∈ EMetric.ball a (ENNReal.ofReal R) := by
  rw [EMetric.mem_ball, edist_dist, dist_eq_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hzR
```

The in-file pattern uses `rw [EMetric.mem_ball, edist_dist, dist_eq_norm]`
to convert a membership into a norm inequality; our S7 ACT bridge uses
the equally available **set-level** equality `Metric.emetric_ball`.
Either pattern is acceptable v4.26.0 idiom.

## Item 2 (resolved): `DiffContOnCl` is a `structure` with two `protected` fields, and `DiffContOnCl.mk_ball` is the clean introduction

**Location**: `Mathlib/Analysis/Calculus/DiffContOnCl.lean:33-35`.

```lean
/-- A predicate saying that a function is differentiable on a set and is continuous on its
closure. This is a common assumption in complex analysis. -/
structure DiffContOnCl (f : E → F) (s : Set E) : Prop where
  protected differentiableOn : DifferentiableOn 𝕜 f s
  protected continuousOn : ContinuousOn f (closure s)
```

**Key facts**:
- It is a `structure` (`Prop`-valued), not a typeclass; the two fields
  are `protected`, meaning they must be accessed via dot-notation
  (`hf_diff_cont.differentiableOn`) rather than unqualified
  (`differentiableOn hf_diff_cont`).
- The `continuousOn` field is on **`closure s`**, not on `s` directly.
  For `s := Metric.ball a r'` with `r' > 0`,
  `closure (Metric.ball a r') = Metric.closedBall a r'` (in a normed
  space). So S6e's `refine ⟨?_, h_analyticOn_cls.continuousOn⟩` form
  needs `h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r')`
  whose `.continuousOn` lands on `closedBall`, then the
  `closure_ball ≃ closedBall` rewriting must happen explicitly.

**Cleaner alternative — `DiffContOnCl.mk_ball`** at
`Mathlib/Analysis/Calculus/DiffContOnCl.lean:66-68`:

```lean
theorem mk_ball {x : E} {r : ℝ}
    (hd : DifferentiableOn 𝕜 f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) :
    DiffContOnCl 𝕜 f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩
```

**This is the form to use**. It takes:
1. `DifferentiableOn 𝕜 f (Metric.ball a r')` — direct from `AnalyticOnNhd.differentiableOn` after mono'ing to closed ball.
2. `ContinuousOn f (Metric.closedBall a r')` — direct from `AnalyticOnNhd.continuousOn` (on closed ball).

The `.mk_ball` form sidesteps the explicit `closure_ball = closedBall`
rewriting entirely.

**Corrected DiffContOnCl bridge** (replaces S6e's anonymous
constructor approach):

```lean
have hf_diff_cont : DiffContOnCl ℂ f (Metric.ball a r') :=
  DiffContOnCl.mk_ball
    (h_analyticOn_cls.differentiableOn.mono Metric.ball_subset_closedBall)
    h_analyticOn_cls.continuousOn
```

## Item 3 (resolved): `HasFPowerSeriesOnBall.factorial_smul` signature and dot-notation calling convention

**Location**: `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:840`.

```lean
namespace HasFPowerSeriesOnBall

variable {p : FormalMultilinearSeries 𝕜 E F} {f : E → F} {x : E} {r : ℝ≥0∞}
  (h : HasFPowerSeriesOnBall f p x r) (y : E)
variable [CompleteSpace F]
include h

theorem factorial_smul (n : ℕ) :
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := ...
```

**Effective surface signature** (after section-variable elaboration):

```
HasFPowerSeriesOnBall.factorial_smul :
  ∀ {𝕜 E F : Type*} [_ : ...] {p : FormalMultilinearSeries 𝕜 E F} {f : E → F}
    {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p x r) (y : E)
    [CompleteSpace F] (n : ℕ),
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y)
```

**Dot-notation call** (the one S6e used):

```lean
hf.factorial_smul w k  -- where hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R),
                       -- w : ℂ, k : ℕ
```

is correct. The output type is:

```
k ! • p k (fun _ ↦ w) = iteratedFDeriv ℂ k f a (fun _ ↦ w)
```

Note: this is **`k.factorial • _` on the LEFT** (smul by `ℕ`, not `ℝ`).
`k ! : ℕ`; the smul is `ℕ • ℂ` = repeated addition. The line
`have h_factor_smul : k.factorial • p k (fun _ ↦ w) = ...` in S6e's
sketch is correct as a Lean statement.

For step (6) — taking norms — `k.factorial • z = k.factorial * z` after
the natural inclusion `ℕ → ℂ`. The S2 in-file pattern (line 593-600 was
**refuted** by S6e — confirming `Complex.abs_natCast` is PHANTOM here)
gives way to: just `simp [norm_smul]` or `norm_cast` over the `ℕ` cast.

**S6e's `(mul_le_mul_iff_left₀ (by exact_mod_cast k.factorial_pos)).mp`
finisher** (line 295 of S6e's sketch) bridges the `ℕ`-smul to a real
multiplication implicitly: the inequality `k.factorial * ‖_‖ ≤ k.factorial * (M * ...)`
naturally lives in `ℝ` after taking norms, so `mul_le_mul_iff_left₀` over
the real positive `(k.factorial : ℝ)` discharges it. This is what S6e
meant, but the smul→mul casting may need an explicit `Nat.cast_smul_eq_nsmul` or
`nsmul_eq_mul` intermediate; pre-flight risk.

## Item 4 (new, surfaced by this audit): `Metric.emetric_ball` is the canonical EMetric ↔ Metric set bridge at v4.26.0

**Location**: `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:945-948`.

```lean
theorem Metric.emetric_ball {x : α} {ε : ℝ} :
    EMetric.ball x (ENNReal.ofReal ε) = ball x ε := by
  ext y
  simp [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
```

**Useful companion** at line 957: `Metric.emetric_closedBall`
(requires `0 ≤ ε`, in our case satisfied by `hr'.le` since `0 < r'`).

This resolves the EMetric/Metric type mismatch in Item 1 with one line:

```lean
have h_analyticOn_R : AnalyticOnNhd ℂ f (Metric.ball a R) := by
  have := hf.analyticOnNhd
  rwa [Metric.emetric_ball] at this
```

## Corrected S7 ACT proof body (final assembled)

Replacing the current sorry on `cauchy_diag_norm_bound_at_radius` with:

```lean
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (r' : ℝ) (hr' : 0 < r') (hr'R : r' < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k := by
  -- (1) Inclusions: `closedBall a r' ⊂ ball a R` and `sphere a r' ⊂ closedBall a r'`.
  have h_cls_sub : Metric.closedBall a r' ⊆ Metric.ball a R := fun z hz =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr'R)
  have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := fun z hz => by
    apply hbound
    exact h_cls_sub (Metric.sphere_subset_closedBall hz)
  -- (2) Analytic-on-the-closed-ball-of-radius-r' bridge.
  --     `hf.analyticOnNhd` returns `AnalyticOnNhd ℂ f (EMetric.ball a (ENNReal.ofReal R))`;
  --     `Metric.emetric_ball` flips it to `Metric.ball a R`, then `.mono` to `closedBall a r'`.
  have h_analyticOn_R : AnalyticOnNhd ℂ f (Metric.ball a R) := by
    have h := hf.analyticOnNhd
    rwa [Metric.emetric_ball] at h
  have h_analyticOn_cls : AnalyticOnNhd ℂ f (Metric.closedBall a r') :=
    h_analyticOn_R.mono h_cls_sub
  -- (3) DiffContOnCl bridge via the clean `DiffContOnCl.mk_ball` constructor.
  have hf_diff_cont : DiffContOnCl ℂ f (Metric.ball a r') :=
    DiffContOnCl.mk_ball
      (h_analyticOn_cls.differentiableOn.mono Metric.ball_subset_closedBall)
      h_analyticOn_cls.continuousOn
  -- (4) Mathlib's Cauchy estimate on the closed sphere of radius r' (Liouville.lean:44).
  have h_cauchy : ‖iteratedDeriv k f a‖ ≤ k.factorial * M / r' ^ k :=
    norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr' hf_diff_cont h_sphere_bound
  -- (5) Bridge `p k` to `iteratedDeriv k f a` via factorial_smul + diag_collapse.
  have h_factor_smul : k.factorial • p k (fun _ ↦ w) =
      iteratedFDeriv ℂ k f a (fun _ ↦ w) :=
    hf.factorial_smul w k
  have h_diag : iteratedFDeriv ℂ k f a (fun _ ↦ w) =
      w ^ k • iteratedDeriv k f a := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    congr 1
    exact (Finset.prod_const w).trans (by simp)
  -- (6) Take norms and divide by k.factorial > 0.
  have h_combined : k.factorial • p k (fun _ ↦ w) =
      w ^ k • iteratedDeriv k f a := h_factor_smul.trans h_diag
  have h_normed : (k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖ ≤
      (k.factorial : ℝ) * (M * (‖w‖ / r') ^ k) := by
    have h1 : (k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖ =
        ‖w‖ ^ k * ‖iteratedDeriv k f a‖ := by
      have hnorm := congrArg (‖·‖) h_combined
      simp [norm_smul, norm_pow, Real.norm_natCast,
            abs_of_nonneg (Nat.cast_nonneg _), nsmul_eq_mul] at hnorm
      linarith
    rw [h1]
    have h_pow_nn : 0 ≤ ‖w‖ ^ k := pow_nonneg (norm_nonneg _) _
    have h2 : ‖w‖ ^ k * ‖iteratedDeriv k f a‖ ≤
        ‖w‖ ^ k * (k.factorial * M / r' ^ k) :=
      mul_le_mul_of_nonneg_left h_cauchy h_pow_nn
    have hr'_pow_pos : (0 : ℝ) < r' ^ k := pow_pos hr' k
    calc ‖w‖ ^ k * ‖iteratedDeriv k f a‖
        ≤ ‖w‖ ^ k * (k.factorial * M / r' ^ k) := h2
      _ = (k.factorial : ℝ) * (M * (‖w‖ / r') ^ k) := by
          field_simp
          ring
  have h_factorial_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  exact (mul_le_mul_iff_left₀ h_factorial_pos).mp h_normed
```

**Estimated total LOC**: ~65-80 (vs S6e's ~60-90 estimate). The corrections
to S6e's sketch were:
- **+3 LOC**: the `Metric.emetric_ball` bridge (Item 1/4).
- **−3 LOC**: replaced the anonymous-constructor `refine ⟨?_, _⟩` with
  `DiffContOnCl.mk_ball` (Item 2).
- **+1 LOC**: explicit `h_factorial_pos` to avoid inline `by exact_mod_cast`
  inside `mul_le_mul_iff_left₀`.

## Updated S7 ACT Mathlib-name table

All entries from S6e's table are re-verified; **the new row** is `Metric.emetric_ball`
(EMetric → Metric set bridge, which S6e implicitly assumed but did not pin):

| Step | Lemma | Verified location | Status |
|---|---|---|---|
| (1a) `closedBall ⊆ ball` | `Metric.mem_ball` / `Metric.mem_closedBall` | folklore | ✅ trivial |
| (1b) sphere bound | `Metric.sphere_subset_closedBall` | folklore | ✅ trivial |
| (2a) AnalyticOnNhd | `HasFPowerSeriesOnBall.analyticOnNhd` | `Mathlib/Analysis/Analytic/ChangeOrigin.lean:366` | ✅ **pinned by S6f** |
| (2b) **EMetric ↔ Metric** | `Metric.emetric_ball` | `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:945` | ✅ **new pin by S6f** |
| (2c) AnalyticOnNhd → ContinuousOn | `AnalyticOnNhd.continuousOn` | folklore | ✅ exists |
| (2d) AnalyticOnNhd → DifferentiableOn | `AnalyticOnNhd.differentiableOn` | folklore | ✅ exists |
| (3) DiffContOnCl introduction | `DiffContOnCl.mk_ball` | `Mathlib/Analysis/Calculus/DiffContOnCl.lean:66` | ✅ **pinned by S6f** (replaces anon constructor) |
| (4) Cauchy estimate | `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | `Mathlib/Analysis/Complex/Liouville.lean:44` | ✅ S6e |
| (5a) factorial_smul | `HasFPowerSeriesOnBall.factorial_smul` | `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:840` | ✅ **pinned by S6f** (dot-call `hf.factorial_smul w k`) |
| (5b) diag collapse | `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` | `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:246` | ✅ S6e |
| (5c) prod_const | `Finset.prod_const` | folklore | ✅ trivial |
| (6a) norm-of-smul | `norm_smul`, `norm_pow` | folklore | ✅ trivial |
| (6b) ℕ-cast inside norm | `Real.norm_natCast` (note **real**, not complex) | folklore (via `RCLike.norm_natCast` specialization) | ✅ S6f |
| (6c) `ℕ`-smul ↔ `ℕ`-mul | `nsmul_eq_mul` | folklore | ✅ S6f |
| (6d) factorial pos | `Nat.factorial_pos` | folklore | ✅ trivial |
| (6e) divide both sides | `mul_le_mul_iff_left₀` | folklore | ✅ S6e |

**Status after this audit**: all sub-step names verified at v4.26.0. Three
S6e-flagged-unresolved items are pinned (analyticOnNhd location, DiffContOnCl
shape, factorial_smul args). One new item (`Metric.emetric_ball` bridge)
is surfaced.

## Open S7-ACT risks remaining

After S6 → S6f, the residual risks are:

| # | Risk | Status |
|---|------|--------|
| R-1 (S6d) | `abs_natCast` vs `norm_natCast` | **PINNED** (S6e). `Complex.abs_natCast` is PHANTOM. |
| R-2 (S6d) | EMetric ball conversion | **PINNED** (S6f). Use `Metric.emetric_ball`. |
| R-3 (S6d) | `le_of_tendsto` direction | **Resolved** (not in S7 scope; S5 owns the limit step). |
| R-4 (S6d) | iteratedFDeriv ↔ iteratedDeriv bridge | **PINNED** (S6e). |
| R-5 (S6d) | `Complex.norm_real_complex` phantom | **Resolved** (S6c routed around it). |
| R-? (S6e) | `DiffContOnCl` shape and bridge | **PINNED** (S6f). Use `DiffContOnCl.mk_ball`. |
| R-? (S6f) | **EMetric/Metric type mismatch in S6e's `.mono` chain** | **PINNED** (S6f, this memo). Use `Metric.emetric_ball` rewrite. |
| R-6 (S6d) | Hypothesis underscore rename | **Procedural** (S7 ACT: drop underscores on `_hR`, `_hM`, `_hf`, `_hbound`, `_hr'`, `_hr'R`). |
| R-7 (S6d) | Build time + .lake symlink loop | **Procedural** (commit Lean change FIRST, push as "build pending", let Doctor verify). |
| R-8 (S6d) | Cross-step variable name consistency | **Resolved by this memo** (the assembled proof above is internally consistent). |
| R-9 (S6d) | Divide-direction for `mul_le_mul_iff_left₀` | **PINNED** (S6f, h_factorial_pos extracted; finisher form `(mul_le_mul_iff_left₀ h_factorial_pos).mp`). |
| R-10 (S6d) | Build heart-attack mitigation | **Procedural** (use `show` aggressively for substep diagnostics, ladder-style sorry if build breaks at `(6)`). |

**All Mathlib-drift risks are pinned**. Remaining risks are all
procedural/stylistic (R-6, R-7, R-10) — not v4.26.0 API drift.

## Anti-targets (this S6f PREP explicitly does NOT do)

1. **Does not modify any Lean file.** `cauchy_diag_norm_bound_at_radius` retains
   its `sorry` in `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`. Sorry
   count remains 1.
2. **Does not run docker build.** Static audit + assembly only.
3. **Does not modify `state.md`, `problem.md`, `knowledge.md`, `meta.json`,
   gallery JSON, or any prior session memo (S6, S6b, S6c, S6d, S6e).**
   Single new file under `sessions/`.
4. **Does not propose new Mathlib upstream contributions.** All names are
   present at v4.26.0.
5. **Does not status-change the slug.** Pool entry remains `progress` with
   1 residual sorry.

## Race awareness

Pre-push checks (2026-05-13 ~23:55 UTC):

- `gh pr list -R rjwalters/lean-genius --search "mean-value-theorem-oq-02-oq-04-oq-01 in:title" --state open`
  returns 1 OPEN PR: **#17904** (S2 ACT from 2026-05-12, obsolete — its
  contents were superseded by #17912 / S2 ACT that merged 2026-05-12).
  Zero overlap with this doc-only PR's diff.
- 10 merged PRs on the slug (S1 through S6e + 1 STATE-SYNC); the most
  recent is #18933 STATE-SYNC (researcher-?, ~22:40 UTC, ~75 min before
  this memo's claim).
- No active Doctor / Mechanic branches against this slug.

## No-edit guarantee

Confirmed by `git diff --stat origin/main`: exactly one file added,
`research/problems/mean-value-theorem-oq-02-oq-04-oq-01/sessions/2026-05-13-s6f-prep-final-pin-and-emetric-bridge.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file (gallery `meta.json` unchanged; pool JSON
  is gitignored local state)
- ✗ No edits to any prior session memo (S6, S6b, S6c, S6d, S6e)

## Honesty

- **Difficulty**: low. Citation audit only — 6 `gh api` calls.
- **Significance**: moderate. S6e self-flagged its three limitations
  (analyticOnNhd line, DiffContOnCl shape, factorial_smul args); this
  memo closes all three. The EMetric/Metric type-mismatch in S6e's
  `.mono` chain is a genuine **bug** in S6e's sketch — without this S6f
  fix, the S7 ACT paste would fail at elaboration.
- **Limitations**:
  - The `norm_smul` / `nsmul_eq_mul` chain in step (6) of the proof is
    sketched but not type-checked at a Lean 4 elaborator. The
    `simp [norm_smul, norm_pow, Real.norm_natCast, ...]` line may need
    finer tuning at S7 ACT time — alternative pathways include explicit
    `Nat.cast_smul_eq_nsmul` rewrites.
  - The `Real.norm_natCast` name is conjectural for the real-value
    application; the underlying lemma is `RCLike.norm_natCast` from
    `Mathlib/Analysis/RCLike/Basic.lean:633` (S6e-pinned). At Lean's
    `ℕ → ℝ` cast site inside a norm, either dot-notation `Real.norm_natCast`
    or a plain `simp` invocation should close it; both are documented in
    the S7 ACT corrected sketch above.
  - This memo does NOT execute `docker-build.sh`. The proof body's
    well-formedness is asserted by type-pinning audit only.
- **What could be wrong**: the `congr 1; exact (Finset.prod_const w).trans (by simp)`
  step (5b) assumes the `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
  conclusion is exactly `(∏ i, m i) • iteratedDeriv n f x`. At v4.26.0
  the actual form is `(∏ i : Fin n, m i) • iteratedDeriv n f x` — with
  `m := fun _ ↦ w`, `∏ i : Fin k, (fun _ ↦ w) i = ∏ i : Fin k, w = w^k`.
  The `Finset.prod_const` reduction needs `Finset.univ.card = k`, which
  is `Finset.card_univ` + `Fintype.card_fin`. The S7 ACT paste may need
  to inline these — `congr 1; ext; simp` or `simp` with appropriate
  hints. The audit identifies this but does not exhaustively type-check
  the substep at Lean's elaborator.

## Next iteration after this PREP

S7 ACT — paste the corrected proof body above into
`MeanValueTheoremOQ02OQ04OQ01.lean`, drop underscores on `_hR`, `_hM`,
`_hf`, `_hbound`, `_hr'`, `_hr'R` (R-6 procedural), attempt
`./proofs/scripts/docker-build.sh Proofs.MeanValueTheoremOQ02OQ04OQ01`.

**Expected outcome**: sorry count 1 → 0; slug `progress` → eligible for
`completed`; meta `axiomatized` (with 2 deferred axioms) status
unchanged (the 2 axioms documented in `state.md` are not affected by
this sorry).

If the build passes, the slug's main contribution (refuting the parent
OQ-04 axiom via Runge — S1) is now backed by a complete Cauchy
uniform-geometric approximation (S2 + S3 + S4 + S5 + S7).

**Estimated S7 ACT LOC**: ~65-80 (slightly revised from S6e's 60-90).

## References

- **S6e (the audit this memo builds on)**:
  `sessions/2026-05-13-s6e-prep-mathlib-name-v4260-audit.md`. PR #18536.
- **S6d (risk register)**:
  `sessions/2026-05-13-s6d-prep-s7-act-risk-register.md`. PR #18464.
- **S6c (placeholder resolution)**:
  `sessions/2026-05-13-s6c-prep-placeholder-resolution.md`. PR #18396.
- **S6b (lemma probes)**:
  `sessions/2026-05-12-s6b-prep-lemma-probe-results.md`. PR #18386.
- **S6 (Mathlib drift survey)**:
  `sessions/2026-05-12-s6-prep-cauchy-finite-radius.md`. PR #18309.
- **S5 ACT (limit-extraction)**: PR #18197.
- **Mathlib v4.26.0 sources (verified at audit time, SHA `2df2f015…`)**:
  - `Mathlib/Analysis/Analytic/ChangeOrigin.lean:366` — `HasFPowerSeriesOnBall.analyticOnNhd`.
  - `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:945` — `Metric.emetric_ball`.
  - `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:957` — `Metric.emetric_closedBall`.
  - `Mathlib/Analysis/Calculus/DiffContOnCl.lean:33-35` — `structure DiffContOnCl`.
  - `Mathlib/Analysis/Calculus/DiffContOnCl.lean:66-68` — `DiffContOnCl.mk_ball`.
  - `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:840` — `HasFPowerSeriesOnBall.factorial_smul`.
  - `Mathlib/Analysis/Complex/Liouville.lean:44` — `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
  - `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:246` — `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`.
  - `Mathlib/Analysis/RCLike/Basic.lean:633` — `RCLike.norm_natCast` (specializes to `Complex.norm_natCast` and `Real.norm_natCast`).
