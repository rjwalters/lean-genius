# Research State: fundamental-theorem-calculus-oq-01-incomplete-01

## Current State
**Phase**: ACT-attempted → BLOCKED (sibling repair gate); reverted to PREP-ready
**Path**: full
**Since**: 2026-06-09 (researcher-11, iter 6 ACT-attempt → PREP discoveries banked)
**Iteration**: 6

## Current Focus (iter 6)

Iter 6 attempted the iter-5 PREP-banked ACT plan under Docker. The
attempt surfaced **three pre-existing issues** that block the plan:

1. **Iter-5's plan has a circular import.** The plan called for adding
   `import Proofs.FundamentalTheoremCalculusLebesgueOQ01` to the parent,
   but the sibling already imports the parent. Reverse direction is the
   only viable one.

2. **The sibling file does not build at HEAD against Mathlib v4.26.0.**
   Confirmed via Docker build on a clean checkout (no edits). Initial
   fail: `invalid 'import' command, it must be used in the beginning of
   the file` (line 23 — the `/-! ... -/` docstring precedes imports).
   After moving imports to top, deeper errors emerge in `ac_implies_bv`:
   * `eVariationOn.eq_zero_iff.mpr` — unknown constant (likely renamed).
   * `div_lt_iff` — unknown identifier (likely renamed to `div_lt_iff₀`).
   * `ENNReal.natCast_ne_top` used unapplied (needs `(n)` or `_`).
   * `linarith failed` cascade.

3. **The axiom `lebesgue_ftc_differentiable` is orphaned.** Grep finds
   only the declaration — zero downstream callers. Simplifies the
   discharge plan: just delete it (no parent-side edit needed beyond
   the deletion).

Full record: `sessions/2026-06-09-iter6-prep-act-blocked.md`.

## Active Approach (refined for iter 7+)

**Same chain as iter-5**: `AC → BV → a.e. DifferentiableAt`. **Same
named lemmas confirmed**: `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`
+ `measurableSet_of_differentiableAt`.

**Structural change vs iter-5**: discharge proof lives in the **sibling**
file (which already imports parent), not the parent. Avoids the
circular-import bug. The parent's orphan axiom is deleted post-discharge.

## Completed This Iteration (iter 6)

- **Iter-5 plan validation under Docker** (5 cycles total): paste-ready
  skeleton attempted and rejected by Lake at import time (circular
  import). After locally working around the cycle (placing discharge in
  sibling), uncovered three layers of pre-existing breakage that iter-5
  PREP missed.
- **HEAD-only baseline build** (no edits): confirmed sibling fails to
  build against current Mathlib. Validates that the sibling's gallery
  status `verified` is *stale data*.
- **Operational state corrected**: host memory is actually 96 GiB
  (not 7.65 GiB as iter-5 recorded — that was almost certainly a
  Docker-container reading). Memory is NOT a blocker.
- **Build-ready discharge proof skeleton banked** in iter-6 session §3
  (paste-tested after sibling repair, modulo the broken sibling).
  Includes `Classical.not_imp` disambiguation, `open MeasureTheory`
  fix for `volume`, inlined `{x | DifferentiableAt ℝ F x}` (replacing
  iter-5's `set ... with` that defeats rewriting).
- **API name re-confirmations** via Mathlib web docs
  (`mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Measurable.html`).
- **Orphan-axiom discovery**: `lebesgue_ftc_differentiable` has zero
  callers anywhere in the codebase.

## Prior Iteration Notes (preserved)

### Iter 5 (2026-06-09, researcher-5, PREP)
- Banked Mathlib API name `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`.
- Sharpened iter-4 skeleton to a single residual `sorry`.
- Plan superseded by iter-6 due to circular-import bug.

### Iter 4 (2026-06-02, researcher-1, PREP)
- Paste-ready Lean skeleton (parent-file edit) with BV→a.e.-diff name
  as a placeholder + Docker grep recipe.
- T+3d premise re-verification.
- Disk hygiene flag.

### Iter 3 (2026-05-30, researcher-1, SURVEY follow-up)
- **Discovery**: `ac_implies_bv` proved in sibling. **Iter 6 update**:
  the sibling's "verified" status was based on stale audit data; the
  proof does not build against current Mathlib (see iter-6 §4).
- Documented concrete discharge plan.

### Iter 1-2 (2026-05-28, researcher-1)
- Added `ac_implies_continuousOn` (AC ⟹ `ContinuousOn`) — verified.
- Added `ac_on_subinterval` (AC localizes to subintervals) — verified.

## Attempt Count
- Total attempts: 5 (iter 1-2 helper-lemma adds; iter 4 PREP skeleton;
  iter 5 PREP API-name resolution; iter 6 ACT-attempt + discoveries).
- Current approach attempts: 1 ACT (iter 6, blocked at sibling-repair
  gate).
- Approaches tried: 1 (the AC → BV → a.e. Diff chain remains the only
  viable path; iter 6 ACT execution was halted by upstream breakage,
  not by a chain-level issue).

## Blockers

- **Sibling-file pre-existing breakage** (NEW, iter 6, gates iter 7+):
  `FundamentalTheoremCalculusLebesgueOQ01.lean` does not build at HEAD
  against Mathlib v4.26.0. Repair scope (see iter-6 §4 & §9.1):
  rename `div_lt_iff → div_lt_iff₀`, apply `ENNReal.natCast_ne_top n`,
  resolve `eVariationOn.eq_zero_iff` rename, reorder imports above
  docstring, add `open MeasureTheory`.
- **(Resolved iter-6)** ~~Host memory cap~~: host actually has 96 GiB.
- **(Resolved iter-5)** ~~Docker required~~ / ~~BV-name unknown~~ /
  ~~Host disk pressure~~.

## Next Action

**Iter 7 (gate-clearing)**: repair the sibling file's pre-existing
errors per iter-6 §4. Single Docker build cycle should suffice
(~5-10 min warm-cache). Once green, the §3 discharge proof is paste-ready
and a second build cycle confirms axiomCount: 2 → 1.

Specifically:

1. Edit `proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean`:
   a. Move `import` lines above the `/-! ... -/` docstring.
   b. Add `open MeasureTheory` to the `open` line.
   c. Rename `div_lt_iff` → `div_lt_iff₀` (line 157).
   d. Apply `ENNReal.natCast_ne_top n` (line 182).
   e. For the two `eVariationOn.eq_zero_iff.mpr` usages (lines ~103,
      ~149), grep Mathlib for the current name; likely rewrite to use
      `show ... = 0; ...` directly via the definitional `eVariationOn`
      = 0 condition.
2. Docker build the sibling.
3. On green: paste iter-6 §3's discharge theorem.
4. Add the new import `Mathlib.Analysis.Calculus.FDeriv.Measurable`.
5. Docker build again to confirm.
6. On green: delete parent's `axiom lebesgue_ftc_differentiable`
   (lines ~188-204 — see iter-6 session for exact deltas).
7. Update `meta.json`s: parent `axiomCount: 2 → 1`; sibling
   `theoremCount: 6 → 7`; both touch `assumptions` text.
8. Commit, push, open PR.

Expected delta vs origin/main:
* Parent `axiomCount: 2 → 1`.
* Sibling `theoremCount: 6 → 7`.
* Sibling status remains `verified` (not regressed).
* Cantor `sorry` and `lebesgue_ftc_integral` axiom remain (separate
  scope).

Estimated iter-7 wall-clock: 30-45 minutes (2 Docker cycles + edits +
PR), well within the 90-minute claim TTL.
