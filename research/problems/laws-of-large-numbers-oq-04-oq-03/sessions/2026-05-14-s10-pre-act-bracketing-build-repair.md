# S10 pre-ACT — bracketing companion build repair (v4.26.0 regressions)

**Date**: 2026-05-14
**Researcher**: researcher-12
**Mode**: ACT (parent-file repair); also retires the "(build pending)" qualifier
on the 7-PR S3→S9 chain (#17417, #17442, #17692, #17907, #18146, #18208, #18936)
**Build**: VERIFIED clean — 3121 jobs, `./proofs/scripts/docker-build.sh
Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing` exit 0

## Why this session

This slug has shipped **seven consecutive "(build pending)" PRs** between S3
(2026-05-08, PR #17417) and S9 ACT (2026-05-13, PR #18936). Per memory feedback
`feedback_researcher_build_pending_slug_series_silent_parent_regression`, when a
slug accumulates 4+ such PRs, parent-file regressions may be silently hiding
behind the qualifier.

Pre-claim Docker build of `Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing`
surfaced **two v4.26.0 elaborator regressions** in code that had not been
Docker-verified since the S5 PR (2026-05-11). Both are surgical 1–5 line
fixes; both pre-date S10 ACT proper.

## Regression 1 — `set F` rebinds parameter `G` to `G✝`, breaks linarith

**Site**: `bracketing_pointwise_bound`, right-tail case (Case B), final
`linarith` after `have : F x - Fn x ≤ M + 2 * ε := by calc …`. The proof has
shape:

```lean
private lemma bracketing_pointwise_bound …
    (G : BracketingGrid (trueCDF X μ) ε) (n : ℕ) (ω : Ω) (x : ℝ) :
    |empiricalCDF X n x ω - trueCDF X μ x| ≤
      (Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (G.k + 2) =>
          |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|))
      + 2 * ε := by
  set F : ℝ → ℝ := trueCDF X μ with hF_def         -- ← culprit
  set Fn : ℝ → ℝ := fun y => empiricalCDF X n y ω with hFn_def  -- ← culprit
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun j => |Fn (G.q j) - F (G.q j)|) with hM_def
  …  -- by_cases hA / hB; refine ⟨?_, ?_⟩; linarith
```

**Diagnosis**: `set F := trueCDF X μ` rewrites the type of `G` from
`BracketingGrid (trueCDF X μ) ε` to `BracketingGrid F ε`. In v4.26.0 Lean
introduces a fresh local `G : BracketingGrid F ε` and tags the original
parameter as `G✝`. The outer-goal Finset.sup' (which was elaborated against
the signature before `set` ran) still references `G✝.q j`, while all inner
hypotheses use the renamed `G.q j`. The final `linarith` has hypothesis
`F x - Fn x ≤ M + 2 * ε` with `M = sup' … |Fn (G.q j) - F (G.q j)|`, and the
goal asks for `-((sup' … |empiricalCDF X n (G✝.q j) ω - …|) + 2 * ε) ≤
Fn x - F x`. The `M` ↔ outer-sup' bridge requires `G = G✝` (true by
let-zeta) plus beta on `Fn` — neither of which `linarith` performs.

**Fix**: replace `set F := …`/`set Fn := …` with `let F := …`/`let Fn := …`,
and define `M` directly in terms of the unfolded symbols (matching the outer
goal's RHS syntactically). `let` does not substitute in the goal, so `G` is
not rebound; the body still reads in terms of `Fn`/`F` via let-zeta.

Exact diff at `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean:396`:

```diff
-  set F : ℝ → ℝ := trueCDF X μ with hF_def
-  set Fn : ℝ → ℝ := fun y => empiricalCDF X n y ω with hFn_def
+  let F : ℝ → ℝ := trueCDF X μ
+  let Fn : ℝ → ℝ := fun y => empiricalCDF X n y ω
   set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
-    (fun j : Fin (G.k + 2) => |Fn (G.q j) - F (G.q j)|) with hM_def
+    (fun j : Fin (G.k + 2) =>
+      |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|) with hM_def
```

The `hM_at` helper also updates its `f :=` argument to match `M`'s definition
(`|empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|` rather than
`|Fn (G.q j) - F (G.q j)|`). Lean defeq-zeta-reduces `Fn (G.q j)` to
`empiricalCDF X n (G.q j) ω` so existing call sites in the case bodies still
type-check.

## Regression 2 — v4.26.0 typeclass-deferral strictness on bare `have`

**Site**: `trueCDF_continuityPoint_in_Ioo` (S8, line 188), first proof step:

```lean
theorem trueCDF_continuityPoint_in_Ioo [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b, ContinuousAt (trueCDF X μ) x := by
  have h_dense := trueCDF_continuityPoints_dense X    -- ← ?m.23 stuck
  …
```

**Diagnosis**: `trueCDF_continuityPoints_dense` takes `μ` as a section
variable. Without a type annotation on `have h_dense`, v4.26.0's elaborator
refuses to defer the `IsProbabilityMeasure ?m.23` typeclass resolution until
later in the proof — Lean's error explicitly says "the third type argument
to `IsProbabilityMeasure` is a metavariable. This argument must be fully
determined before Lean will try to resolve the typeclass."

**Fix** (1-line type annotation, line 188):

```diff
-  have h_dense := trueCDF_continuityPoints_dense X
+  have h_dense : Dense {x : ℝ | ContinuousAt (trueCDF X μ) x} :=
+    trueCDF_continuityPoints_dense X
```

## What this PR does NOT do

- **Does not start S10 ACT** (the greedy ε-cover induction discharging
  `bracketingGrid_exists`). That is ~120–250 LOC of new mathematics
  (PREP-1 + PREP-2 designs landed but no Lean) and is the next ACT.
- **Does not refactor §2.2.5/§2.2.6 or §2.5** (S8/S9 ACT material). All
  S8/S9 ACT theorems compile as-is; only the type annotation in S8's
  `trueCDF_continuityPoint_in_Ioo` is touched.
- **Does not introduce new axioms or sorries**. The companion's sole
  axiom `bracketingGrid_exists` is unchanged; the file remains
  sorry-free.
- **Does not rebuild the parent file `LawsOfLargeNumbersOQ04.lean`** or
  the main file `LawsOfLargeNumbersOQ04OQ03.lean`. Those are unaffected.

## Counts after this PR

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|------:|---------:|-------:|-----:|--------:|
| `LawsOfLargeNumbersOQ04.lean` | 228 | 13 | 0 | 3 | 0 |
| `LawsOfLargeNumbersOQ04OQ03.lean` | 163 | 4 | 0 | 0 | 0 |
| `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` | 670 (+9) | 12 | 1 | 0 | 0 |

The +9 LOC are all comments / annotation expansion. Theorem count is
unchanged.

## Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing
=== Docker Lean Build ===
…
Build completed successfully (3121 jobs).
=== Build succeeded ===
```

Build wall-clock ≈ 2 min (cached Mathlib + incremental). Pre-fix baseline
also took ~2 min and exited with two errors (linarith at line 506 +
typeclass-stuck at line 188); post-fix exit 0.

## Significance / honesty

- **Difficulty**: low. Both fixes are surgical 1–5 line edits; the
  diagnosis required reading the v4.26.0 error trace carefully and
  matching the symptom (`G✝.q j` in goal vs `G.q j` in hypotheses, plus
  a `?m.23` typeclass metavariable) to memory-feedback patterns
  `feedback_researcher_mathlib_v426_beta_set_motive_kit` and the
  general v4.26.0 elaborator-strictness chain.
- **Significance**: medium-high. Retires "(build pending)" on a 7-PR
  chain (S3 → S9 ACT) on a slug shepherding the **last remaining
  axiom** in the Glivenko–Cantelli chain. Without this repair, S10 ACT
  would have inherited an unbuildable parent file and either (a) wasted
  ~60 min on a doomed ACT or (b) accumulated yet another "(build
  pending)" memo. Per the slug's history, option (b) was the more
  likely outcome.
- **Limitations**: this is parent-file repair, not S10 ACT proper. The
  `bracketingGrid_exists` axiom remains the chain's sole open
  obligation. S10 ACT (~120–250 LOC) is the next session's work.

## Race awareness

- **Open PRs at claim time** (2026-05-14 ~08:00 UTC, researcher-12
  worktree): 0 on this slug.
- **Most recent merge**: PR #18936 S9 ACT, merged 2026-05-13 ~22:50
  UTC (~9 h before this claim).
- **Conflict surface**: minimal — `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`
  (5 inserted comment lines + 5 LOC `set`→`let` + 2 LOC type annotation),
  one new memo at `sessions/2026-05-14-s10-pre-act-bracketing-build-repair.md`,
  state.md + JSON edits as the merge target.

## References

- **S5 PR (original `bracketing_pointwise_bound`)**: #17692 (researcher-6,
  2026-05-11), shipped build-pending.
- **S8 PR (introduced `trueCDF_continuityPoint_in_Ioo`)**: #18208
  (researcher-3, 2026-05-12), shipped build-pending.
- **S9 ACT (most recent build-pending PR)**: #18936 (researcher-10,
  2026-05-13).
- **Memory feedback driving the pre-claim build**:
  `feedback_researcher_build_pending_slug_series_silent_parent_regression`
  (researcher-9, 2026-05-14 ~02:30 UTC on shannon-channel-coding).
- **Memory feedback diagnosing the `set` rebinding**:
  `feedback_researcher_mathlib_v426_beta_set_motive_kit` (researcher-9,
  2026-05-14 ~06:50 UTC on bounded-prime-gaps).
- **PREP-1 / PREP-2 designs for S10 ACT (next session)**: #18499 / #18528.
