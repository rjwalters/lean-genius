# Research State: fundamental-theorem-calculus-oq-01-incomplete-01

## Current State
**Phase**: ORIENT → ACT-ready (no Docker required for next picker's first move)
**Path**: full
**Since**: 2026-06-09 (researcher-5, iter 5 PREP — API name confirmed; sharpened paste-ready skeleton; was 2026-06-02 / iter 4)
**Iteration**: 5

## Current Focus (iter 5)

Iter 5 is a **PREP** session, banking a confirmed Mathlib API name and
a sharpened paste-ready skeleton. **Key discovery**: the BV→a.e.-diff
Mathlib lemma — iter-4's last unknown — is **resolved without Docker**
via Mathlib html docs.

Confirmed canonical name:

```text
BoundedVariationOn.ae_differentiableAt_of_mem_uIcc
  (h : BoundedVariationOn f (Set.uIcc a b)) :
  ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → DifferentiableAt ℝ f x
```

(Mathlib v4.26.0, `Mathlib.Analysis.BoundedVariation`, finite-dim normed
codomain — ℝ qualifies.)

Net effect:
- Iter-4 §2.2 skeleton's `sorry` at the BV step → replaced by 2-line
  invocation (`Set.uIcc_of_le hab` reshape + lemma application).
- Iter-4 §2.2 "within-vs-full bridge (~10-20 LOC)" → **NO LONGER NEEDED**
  (lemma returns full `DifferentiableAt`).
- Iter-4 §3 Docker grep recipe → obsolete (web docs were authoritative).

Iter-5 skeleton retains ONE residual `sorry`: the measurability of
`{x | DifferentiableAt ℝ F x}`. This is standard Mathlib and the
canonical home is `Mathlib.Analysis.Calculus.FDeriv.Measurable`. Next
picker's first Docker grep targets that single name.

Full record: `sessions/2026-06-09-iter5-prep-api-confirmed.md`.

## Active Approach

`AC → BV → a.e. DifferentiableAt` chain — **all three links now have
named Mathlib (or sibling) lemmas**:
- **AC → BV**: `FTCLebesgueACImpliesBV.ac_implies_bv` (sibling, verified,
  0 axioms / 0 sorries).
- **BV → a.e. DifferentiableAt**:
  `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` (Mathlib, confirmed
  iter-5).
- **∀ᵐ → ∃ measurable S of full measure**: standard measure-theory
  unfolding (~10 LOC, uses `MeasureTheory.ae_iff` + a single
  `measurableSet_of_differentiableAt`-style lemma).

The within-vs-full upgrade step that iter-3/iter-4 planned is no longer
needed — `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` returns
`DifferentiableAt`, not `DifferentiableWithinAt`.

## Completed This Iteration (iter 5)

- **API name confirmation via Mathlib web docs**: the `BoundedVariation`
  module's `ae_differentiable*` family enumerated and dispatched
  (6 candidates → 1 winner: `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`).
  Removes iter-4's primary Docker-bound ask.
- **T+7d temporal-drift re-verification**: parent file LOC/axiom/sorry
  counts unchanged (311 LOC, 2 axioms, 1 sorry); sibling unchanged
  (185 LOC); 0 open PRs; no main commits touching either file since
  2026-05-15.
- **Operational blocker check**: host disk 4.3 GiB → 107 GiB free (~25×
  healthier than iter-4); Docker server running; `lean4-arm64:v4.26.0`
  image cached (4.08 GB); `lean-mathlib-cache` volume present.
- **Sharpened paste-ready skeleton**: iter-4's §2.2 single placeholder
  `sorry` replaced by a 2-line `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`
  invocation + an ∀ᵐ → ∃-witness packaging block. Remaining residual:
  a single 1-line Mathlib name for `MeasurableSet {x | DifferentiableAt}`.

## Prior Iteration Notes (preserved)

### Iter 4 (2026-06-02, researcher-1, PREP)
- Paste-ready Lean skeleton (parent-file edit) with BV→a.e.-diff name
  marked as a placeholder + Docker grep recipe.
- T+3d premise re-verification (all clear, unchanged).
- Disk hygiene flag (4.3 GiB free).

### Iter 3 (2026-05-30, researcher-1, SURVEY follow-up)
- **Discovery**: `ac_implies_bv` already proved in sibling file
  `FundamentalTheoremCalculusLebesgueOQ01.lean` (gallery
  `fundamental-theorem-calculus-oq-01-oq-01`, status `verified`).
- Documented concrete discharge plan for `lebesgue_ftc_differentiable`
  (knowledge.md, with Lean code sketch + API placeholders).
- Verified parent unchanged: 311 lines, 2 axioms, 1 sorry.

### Iter 1-2 (2026-05-28, researcher-1)
- Added `ac_implies_continuousOn` (AC ⟹ `ContinuousOn`) — verified.
- Added `ac_on_subinterval` (AC localizes to subintervals) — verified.
- Mathlib infrastructure assessment + full de-axiomatization roadmap recorded.

## Attempt Count
- Total attempts: 3 (iter 1-2 helper-lemma adds; iter 4 PREP skeleton;
  iter 5 PREP API-name resolution)
- Current approach attempts: 0 (iter 5 is PREP — discovery-banked; no
  Lean / no meta.json edits)
- Approaches tried: 0 ACT (gate at iter 5: ALL GREEN except memory cap)

## Blockers

- **Host memory cap (NEW)**: host total memory 7.65 GiB. Docker default
  `LEAN_MEMORY_LIMIT=32768` would fail. Safe build needs
  `LEAN_MEMORY_LIMIT=4096`. First-time Mathlib-warm module compile ~15-25
  minutes; iterating residual `sorry` adds ~10-15 minutes; cumulative
  borderline for a single cycle.
- **(Resolved iter-4 blocker)** ~~Docker required~~: Docker now healthy.
- **(Resolved iter-4 blocker)** ~~BV-name unknown~~: confirmed iter-5
  via Mathlib web docs.
- **(Resolved iter-4 blocker)** ~~Host disk pressure~~: 107 GiB free.

## Next Action

ACT phase (Docker-required, memory-tuned):

1. Pull the iter-5 PREP skeleton from
   `sessions/2026-06-09-iter5-prep-api-confirmed.md` §2.2.
2. Grep `Mathlib/Analysis/Calculus/FDeriv/Measurable.lean` for
   `MeasurableSet.*Differentiable` (one-time, single name).
3. Replace the §2.2 residual `sorry` with the confirmed name.
4. Bank a clean baseline Docker build (parent unchanged) with
   `LEAN_MEMORY_LIMIT=4096 LEAN_BUILD_TIMEOUT=45m`.
5. Apply the §2.1 + §2.2 edits.
6. Build under Docker; iterate if Mathlib name differs.
7. On green: update `meta.json` per §2.3 (`axiomCount: 2 → 1`,
   `theoremCount: 5 → 6`, `lineCount` re-measure, status carry).
8. Commit, push, PR. Expected delta: parent `axiomCount: 2 → 1`.

Iter-5 PREP banks both the API name *and* the sharpened skeleton, so
steps 2-3 above are ~5 minutes and steps 4-6 are the cycle's only real
wall-clock spend. Do NOT speculatively commit the skeleton to `main`
without a green Docker build — the gallery integrity audit penalizes
uncompilable main, and the skeleton intentionally retains one residual
`sorry` at the differentiability-set measurability bridge until the API
name is verified.
