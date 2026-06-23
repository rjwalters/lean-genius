# S2a ACT — Chart-Local Arc Length (Definition + Sanity)

**Iteration**: S2a ACT
**Author**: researcher-3
**Date**: 2026-05-14
**File**: this session note + `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (new, ~60 LOC)

## Purpose

Deliver the first ACT iteration on the S1-OBSERVE-recommended **Path A**
(chart-local Euclidean arc length). S2a scope from the S1 plan
(`sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md:185`):

> S2a (~50 LOC, easy): `chartArcLength` definition + `chartArcLength_refl = 0` +
> `chartArcLength_nonneg`. Single chart only.

## What landed

`proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (~60 LOC, 0 sorries, 0 axioms):

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace TriangleInequalityOQ04OQ01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def chartArcLength (γ : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖

@[simp]
theorem chartArcLength_self (γ : ℝ → E) (a : ℝ) : chartArcLength γ a a = 0 := by
  simp [chartArcLength, intervalIntegral.integral_same]

@[simp]
theorem chartArcLength_const (c : E) (a b : ℝ) :
    chartArcLength (fun _ : ℝ => c) a b = 0 := by
  simp [chartArcLength, deriv_const']

theorem chartArcLength_nonneg (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ chartArcLength γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)
```

Plus a docstring explaining the chart-local scope and the v4.26.0
Riemannian-typeclass gap (linking back to the S1 OBSERVE survey).

Registered in `proofs/Proofs.lean` after
`import Proofs.TriangleInequalityOQ04`.

## Mathlib v4.26.0 surface notes (audited via `raw.githubusercontent`)

Pinned rev: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| Lemma | Module:Line | Verified |
|---|---|---|
| `intervalIntegral.integral_same : ∫ x in a..a, f x ∂μ = 0` | `MeasureTheory/Integral/IntervalIntegral/Basic.lean:641` | ✔ |
| `deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0` | `Analysis/Calculus/Deriv/Basic.lean:744` | ✔ |
| `intervalIntegral.integral_nonneg : a ≤ b → (∀ u ∈ Icc a b, 0 ≤ f u) → 0 ≤ ∫ u in a..b, f u ∂μ` | `MeasureTheory/Integral/IntervalIntegral/Basic.lean:1246` | ✔ |
| `intervalIntegral.integral_add_adjacent_intervals` (S2b API) | `MeasureTheory/Integral/IntervalIntegral/Basic.lean:1022` | ✔ (queued) |

**v4.26.0 surface regression** (not in current cumulative kit memory):
`Mathlib.MeasureTheory.Integral.IntervalIntegral` is a **directory** at v4.26.0,
no longer a single file. Old code using
`import Mathlib.MeasureTheory.Integral.IntervalIntegral` will 404; the correct
import is `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`. Recorded in
`knowledge.md` Insight 12.

## Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01
...
✔ [2551/2551] Built Proofs.TriangleInequalityOQ04OQ01 (4.2s)
Build completed successfully (2551 jobs).
```

Single Docker iteration, no retry needed. No Mathlib v4.26.0 elaborator
surprises in this scope.

## Why simple type at `ℝ → E` (not on manifolds)

The S1 OBSERVE plan sketches `chartArcLength` as applied to `φ ∘ γ̃` where
`γ̃ : ℝ → M` is on the manifold. Implementing this directly would require
`MFDeriv`, `ChartedSpace`, `SmoothManifoldWithCorners` typeclass arguments at
the definition site — a heavy typeclass burden for a single arc-length integral.

Cleaner: define `chartArcLength` at `ℝ → E` (post-chart), and let callers apply
the chart externally. Resulting definition is ~3 lines, two imports, zero
typeclass surprises. The chart-local scope is preserved (any chart map can be
composed before invoking), and the S2b/c sub-iterations will naturally lift
this to the chart-local distance.

This is faithful to the S1 plan's recommendation ("write `chartArcLength`
parametric in the norm, so that when upstream Mathlib lands `RiemannianMetric`
(`norm := √g`), the chart-local result extends to chart-invariant Riemannian
arc length"). The current type `(γ : ℝ → E) → ℝ` is the maximally simple
form — the eventual Riemannian generalization will replace `‖deriv γ t‖` with
`Real.sqrt (g (mfderiv γ t 1) (mfderiv γ t 1))`, but the `chartArcLength_*`
proof structure (interval-integral additivity, nonnegativity, infimum
exchange) survives unchanged.

## Honest scope

- **NOT the Riemannian distance.** Chart-local. Different charts give different
  arc lengths.
- **NOT the parent `eVariationOn` arc length.** The bridge (eVariationOn =
  intervalIntegral for $C^1$ curves) is a separate lemma, deferred to a future
  iteration (Insight 7 in `knowledge.md`).
- **NOT chart-invariant.** Chart-invariance gates on `RiemannianMetric`, which
  Mathlib v4.26.0 does not have.

What S2a *does* deliver: the foundational definition + three trivial sanity
lemmas, build-verified, with zero new axioms / sorries / dead-ends. Slug status
advances from OBSERVE (S1) to ACT (S2a).

## Race / coordination notes

Pre-claim check (2026-05-14T17:35Z): `gh pr list --search
"triangle-inequality-oq-04-oq-01 in:title" --state open` returned 0. Sibling
`triangle-inequality-oq-04` had 0 open PRs as well. Pristine territory; no
race.

Mid-session: no new PRs surfaced during the ~30 min Docker iteration + commit
window.

## Next iteration

**S2b ACT** — `chartArcLength_trans`:

```
theorem chartArcLength_trans (γ : ℝ → E) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h_int_ab : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b)
    (h_int_bc : IntervalIntegrable (fun t => ‖deriv γ t‖) volume b c) :
    chartArcLength γ a c = chartArcLength γ a b + chartArcLength γ b c
```

Proof: `intervalIntegral.integral_add_adjacent_intervals h_int_ab h_int_bc`.
Estimated ~25–40 LOC.

After S2b, the foundation will be ready for S2c (`chartIntrinsicDist` +
triangle inequality, mirroring the parent's infimum-exchange proof).

## Outcome of this iteration

**Outcome**: progress (S2a ACT delivered, build verified, sorry-free).
**Build status**: Docker-verified at v4.26.0 (2551 jobs clean).
**Net change**:
- Added `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (~60 LOC).
- Registered new file in `proofs/Proofs.lean`.
- Updated `state.md` (S1 OBSERVE → S2a ACT).
- Added 5 new Insights (8–12) to `knowledge.md`.
- Updated `src/data/research/problems/triangle-inequality-oq-04-oq-01.json`
  (phase, iteration, attempt counts, knowledge fields).
- Created this session note.

**Sorries**: 0 (was 0). **Axioms**: 0 (was 0).
**Theorems added**: 3. **Definitions added**: 1.
