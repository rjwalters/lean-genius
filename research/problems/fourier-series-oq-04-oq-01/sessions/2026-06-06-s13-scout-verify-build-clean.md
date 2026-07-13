# S13 SCOUT verify — build clean at current Mathlib pin

**Date**: 2026-06-06
**Researcher**: researcher-1
**Mode**: SCOUT (doc-only build verification; no Lean delta)
**Outcome**: VERIFIED — S11 ACT + S12 PREP baseline remains buildable
  at current Mathlib v4.26.0 cache; the 18-35 LOC S13 ACT budget
  predicted by S12 PREP §5 remains tractable.

## What I did

1. Claimed `fourier-series-oq-04-oq-01` (knowledge score 50, RICH, MODERATE+
   tier depth-first selection).
2. Ran `./proofs/scripts/docker-build.sh Proofs.FourierSeriesOQ04OQ01`
   on `lean4-arm64:v4.26.0` against the shared `lean-mathlib-cache`
   Docker volume.
3. Confirmed the build completes cleanly with the expected sorry
   warning at line 148 (`sphPartialSum_L2_norm_converge`).

## Build result

```
[180s] Building...
⚠ [7743/7743] Replayed Proofs.FourierSeriesOQ04OQ01
warning: Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

- 7743 jobs total (mostly cached replays — Mathlib cache hit was 100%
  on the 7727 file cache).
- 0 errors. Single expected sorry warning at line 148, exactly the
  pre-existing `sphPartialSum_L2_norm_converge` placeholder for the
  Mathlib-gap-bound Plancherel-on-T² L²-norm convergence.
- Sorry surface identical to the last verified build (S11 ACT,
  2026-05-31; sessions/2026-05-31-s11-act-step1-contingency-haart2-volume.md).
- No new warnings introduced by Mathlib pin updates since S11 ACT.

## Why this matters

The state.md §1 had been at iter 11 since 2026-06-01's S12 PREP audit.
S12 cataloged 4 Mathlib API entries (`mFourier`, `mFourierLp`,
`mFourierCoeff`, `hasSum_mFourier_series_L2`) at pinned commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Five days have elapsed.
Without a verification build, we could not confidently invoke the
18-35 LOC S13 ACT budget — any silent Mathlib drift would invalidate
the cataloged signatures and reset the budget estimate.

This iteration confirms:
- The pinned commit's API surface is still load-bearing (build clean).
- The S11 ACT `haarT2_eq_volume` bridge still typechecks.
- The S9 cofinality + S10 `coeFn_finset_sum_haarT2` helpers still
  elaborate. (Implicit: any drift in their bearer set would surface
  as build errors here.)
- The `sphPartialSum_L2_norm_converge` sorry remains the lone sorry
  in the file. No regressions.

## Next action

**S14 ACT** — execute the S12 PREP §5 tactic skeleton against the live
file. Per S12 budget projection: 18-35 LOC closing the single sorry at
line 148, via the option (c) `eLpNorm` swap workaround on top of the
S9/S10/S11 ACT bearers. The recipe (S7 audit §4 steps 4 + 5 + 6) is
fully paste-ready in the S12 memo. Estimated 2-3 Docker iterations
for tactic adjustment.

This SCOUT clears the gate for that ACT to proceed against a verified
baseline rather than a stale pin assumption.

## Files modified

- `research/problems/fourier-series-oq-04-oq-01/state.md` — header bump
  iter 11 → 12, S13 SCOUT entry added, S12 status section retitled.
- `research/problems/fourier-series-oq-04-oq-01/sessions/2026-06-06-s13-scout-verify-build-clean.md`
  — this file.

No Lean delta. No new axioms. No new sorries. Doc-only iteration.
