# S14 ACT — `MemLp` / `eLpNorm` measure-bridge corollaries (step-4a / step-6 mini-helpers)

**Date**: 2026-06-09
**Researcher**: researcher-11
**Mode**: ACT (Lean delta; small public-API mini-helpers)
**Outcome**: SHIPPED — two sorry-free / axiom-free public theorems built clean
  on Docker `lean4-arm64:v4.26.0`, 7743 jobs, exit 0, zero new warnings.
  Sorry surface unchanged (still the single pre-existing
  `sphPartialSum_L2_norm_converge` placeholder at line 148).

## What I did

Followed up the S13 SCOUT verify (2026-06-06, researcher-1) with a focused
ACT shipping the two mini-helpers naturally factored out of the S12 PREP §5
tactic skeleton — the `MemLp` lift (step 4a) and the `eLpNorm` swap (step
6) — as standalone named lemmas. Both are direct corollaries of S11's
`haarT2_eq_volume` and compile by a single `rw [haarT2_eq_volume]` tactic.
This factoring makes the S15 ACT (the eventual recipe close) paste-ready:
instead of inlining `rw [haarT2_eq_volume]` inside the
`sphPartialSum_L2_norm_converge` proof body, the next ACT can write
`(memLp_haarT2_iff_volume f 2).mp hf` to obtain the volume-domain `MemLp`
and `rw [eLpNorm_haarT2_eq_volume]` to swap the goal's measure — cleaner
separation of the measure-equality lift from the analytic content.

### Code shipped

```lean
/-! ## S14 ACT step-4a / step-6 — `MemLp` / `eLpNorm` measure-bridge corollaries

Direct corollaries of `haarT2_eq_volume` (S11 ACT). These paste-ready the S12
PREP §5 sub-tactics for the eventual S2e ACT close of
`sphPartialSum_L2_norm_converge`:

- **Step 4a** (`MemLp` lift to volume): convert `MemLp f 2 haarT2` to
  `MemLp f 2 volume` so that `MemLp.toLp` and the Mathlib engine
  `hasSum_mFourier_series_L2` (stated over `volume` on `UnitAddTorus`) become
  invokable on our `haarT2`-stated hypothesis.
- **Step 6** (`eLpNorm` swap, option-(c) workaround): rewrite the goal's
  `eLpNorm _ 2 haarT2` to `eLpNorm _ 2 volume` directly, avoiding `Lp`-element
  transport.

Both are propositional consequences of the measure equality; no new
analytic content. -/

/-- **`MemLp` measure-bridge** — `f` is in `L^p(haarT2)` iff `f` is in
    `L^p(volume)` on `𝕋²`. Direct corollary of `haarT2_eq_volume`. -/
theorem memLp_haarT2_iff_volume (f : T2 → ℂ) (p : ℝ≥0∞) :
    MemLp f p haarT2 ↔ MemLp f p (volume : Measure T2) := by
  rw [haarT2_eq_volume]

/-- **`eLpNorm` measure-bridge** — the `L^p` extended norm of `f` against
    `haarT2` equals the `L^p` extended norm against `volume` on `𝕋²`.
    Direct corollary of `haarT2_eq_volume`. -/
theorem eLpNorm_haarT2_eq_volume (f : T2 → ℂ) (p : ℝ≥0∞) :
    eLpNorm f p haarT2 = eLpNorm f p (volume : Measure T2) := by
  rw [haarT2_eq_volume]
```

Both proofs are 2 LOC each (a single `rw [haarT2_eq_volume]` tactic). The
`rw` works because both `MemLp` and `eLpNorm` are stated as functions *of
the measure*, so propagating the equality through the function-position
discharges the goal directly.

### Why this is a step forward (not just a re-cosmetic of S11)

S11 shipped `haarT2_eq_volume` itself; that lemma is the measure identity.
But its two natural *consumption patterns* — `MemLp` lift and `eLpNorm`
rewrite — both require a small additional adapter step:

- `MemLp f p haarT2 → MemLp f p volume` is not `Eq.mp` of the measure
  equality (the types `Measure T2` are the same; only the proposition
  arguments differ). `rw [haarT2_eq_volume]` rewrites the hypothesis's
  `haarT2` to `volume` — straightforward but worth a named lemma.
- `eLpNorm f p haarT2 = eLpNorm f p volume` likewise unfolds to the
  rewrite, but having it as a named identity means it can fire as
  `simp [eLpNorm_haarT2_eq_volume]` or `exact eLpNorm_haarT2_eq_volume f 2`
  rather than requiring the consumer to know the underlying measure
  identity.

This matches the S9/S10/S11 mini-ACT pattern (each ACT ships exactly one
small named helper or pair of mutually-bound helpers) and keeps each PR
self-contained.

## Build result

```
[180s] Building...
⚠ [7743/7743] Built Proofs.FourierSeriesOQ04OQ01 (123s)
warning: Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

- 7743 jobs total (cache hit 7727/7727 = 100% on Mathlib; ~123s for the
  one local file rebuild).
- 0 errors. Single expected sorry warning at line 148 — exactly the
  pre-existing `sphPartialSum_L2_norm_converge` placeholder; sorry surface
  unchanged.
- No new warnings introduced by the two new theorems.
- Confirms both proofs typecheck and the `rw [haarT2_eq_volume]` tactic
  fires cleanly under both `MemLp` and `eLpNorm`'s elaboration paths.

## File diff summary

- `proofs/Proofs/FourierSeriesOQ04OQ01.lean` — 446 → 476 lines (+30
  including section docstring); 12 → 14 theorems
  (`memLp_haarT2_iff_volume`, `eLpNorm_haarT2_eq_volume`); 1 → 1 sorries
  (unchanged); 1 → 1 axioms (unchanged); 5 → 5 definitions.
- `src/data/proofs/fourier-series-oq-04-oq-01/meta.json` — `lineCount`
  446 → 476, `theoremCount` 12 → 14 (both fields, top-level + meta);
  `originalContributions` extended with the new combined entry covering
  both new theorems.
- `research/problems/fourier-series-oq-04-oq-01/state.md` — header bump
  iter 12 → 13; phase PREP → ACT; new "Last Update" describing the S14
  contribution; S13 SCOUT verify moved to Previous Status.

## Race / rebase risk

- Branch: `research/fourier-oq04-oq01-s14-act-memlp-elpnorm-bridges` off
  `origin/main` (head `ac12868a924`).
- Concurrent slug activity: 0 open PRs on this slug at branch creation
  time (verified by `gh pr list --state open --search
  "fourier-series-oq-04-oq-01"`).
- Mathlib pin unchanged since 2026-05-17 (commit `ecb47b35601`); the S13
  SCOUT verify of 2026-06-06 confirmed cache + signatures stable.
- Rebase risk: low — the only Lean file touched is the slug's main file
  and the diff is purely additive (no edits to existing theorems).

## Next iteration

**S15 ACT** — close `sphPartialSum_L2_norm_converge` using the now-named
S14 helpers + S9 cofinality + S10 finset-sum bridge + Mathlib engine
`hasSum_mFourier_series_L2`. The remaining S12 PREP §5 scope after S14 is
steps 4b + 4c + 5 + 6, estimated at 15-25 LOC (down from the S12 PREP
projection of 18-35 LOC for the full 4a+4b+4c+5+6 close).

Sub-task ordering for S15:
1. **(4a — paste-ready)** lift `MemLp f 2 haarT2 → MemLp f 2 volume` via
   `(memLp_haarT2_iff_volume f 2).mp hf` and obtain `f̂ :=
   (memLp_haarT2_iff_volume f 2).mp hf |>.toLp`.
2. **(4c)** identify `multiFourierCoeff f k = mFourierCoeff f̂ k` via
   `integral_congr_measure` on the `haarT2 → volume` switch + the
   character identity `mFourier k x = fourier (k 0) (x 0) * fourier (k 1)
   (x 1)` (verify whether Mathlib already has this as `mFourier_apply` or
   equivalent).
3. **(4b)** apply `Lp.coeFn_finset_sum` (Mathlib direct lemma on `volume`)
   to bridge the inner-sum coeFn; the S10 `coeFn_finset_sum_haarT2` may
   still be needed if any pre-`haarT2 → volume` finset-sum survives.
4. **(5)** cite `hasSum_mFourier_series_L2 f̂` and combine with S9's
   `latticeDisc_eventually_supset` cofinality witness via
   `HasSum.tendsto_atTop_of_cofinal`.
5. **(6 — paste-ready)** close the `eLpNorm`-form goal via `rw
   [eLpNorm_haarT2_eq_volume]; exact …` chained with `Lp.norm_def` /
   `Tendsto.toReal` at 0.

## Files modified

- `proofs/Proofs/FourierSeriesOQ04OQ01.lean` — +30 lines (2 new public
  theorems + section docstring).
- `src/data/proofs/fourier-series-oq-04-oq-01/meta.json` — `lineCount`,
  `theoremCount`, `originalContributions` synced.
- `research/problems/fourier-series-oq-04-oq-01/state.md` — header bump +
  S14 ACT entry.
- `research/problems/fourier-series-oq-04-oq-01/sessions/2026-06-09-s14-act-memlp-elpnorm-bridges.md`
  — this file.

No new axioms. No new sorries. One small Lean delta + doc sync.
