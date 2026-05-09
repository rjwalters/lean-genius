# Session 30 — Sorry 2 Statement Refactor (Option A)

**Date**: 2026-05-09
**Researcher**: researcher-13
**Goal**: Refactor `divergence_from_lebesgue_growth` and the corollary
  `erdos_1941_divergence_from_growth` from the strictly-stronger
  `Filter.Tendsto … atTop atTop` form to the unboundedness form
  `∀ M, ∃ n, M < |Lₙf(x)|`.

## Motivation

After S29 (PR #17580) closed Sorry 1 (`trig_sum_harmonic_lb`), only
`divergence_from_lebesgue_growth` (Sorry 2) remained. The prior state.md
"Next Steps" section 2 documented two paths:

  - **Option A (recommended)**: weaken the conclusion to an unboundedness
    / lim-sup form aligned with what UBP delivers.
  - **Option B**: build a lacunary continuous f forcing `Lₙf(x) → ∞`.

Option A is the structurally correct move because the original `Tendsto`
conclusion is **strictly stronger than UBP can deliver**. UBP gives:

> If `T_n : E → F` are continuous linear maps and `‖T_n‖` is unbounded,
> then `∃ x ∈ E, sup_n ‖T_n x‖ = ∞`.

Translated to our setting (E = C[-1,1], T_n = (f ↦ Lₙf(x)),
‖T_n‖ = `chebyshevLebesgue n x`, hypothesis: `Λₙ(x) → ∞`), this gives
exactly `∃ f, sup_n |Lₙf(x)| = ∞` — i.e., `∀ M, ∃ n, M < |Lₙf(x)|`. It
does **not** give `Lₙf(x) → ∞` (Tendsto.atTop), which would require
synchronizing convergence across all n simultaneously, not just along a
subsequence.

Erdős 1941 *does* prove the stronger result via lacunary construction,
but that's a much heavier proof. The unboundedness form is enough to
exhibit interpolation divergence (which is the actual content of "f is a
counterexample to Chebyshev interpolation convergence").

## Changes

### `proofs/Proofs/Erdos1151OQ04.lean` (2561 → 2610 lines)

- File-level docstring (lines 17–22): updated Sorry 1/Sorry 2 status and
  noted the S30 refactor.
- "Sorry 2" doc block (lines 59–78): replaced with a clear statement of
  the unboundedness form, the rationale for the weakening, and the UBP
  closure path.
- `divergence_from_lebesgue_growth` (theorem statement and docstring,
  ~32-line doc block expansion): conclusion changed from
  ```
  ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterp n f x
  ```
  to
  ```
  ∀ M : ℝ, ∃ n : ℕ, M < |chebyshevInterp n f x|
  ```
  Added detailed docstring explaining the rationale and intended UBP-based
  proof.
- `erdos_1941_divergence_from_growth` (corollary): conclusion updated to
  match. The body is unchanged (still
  `divergence_from_lebesgue_growth _ (chebyshev_lebesgue_growth …)`).

### `src/data/research/problems/erdos-1151-oq-04.json`

- `leanFiles[0].lineCount`: 2561 → 2610.
- `currentState.iteration`: 29 → 30.
- `currentState.focus`: replaced with S30 narrative.
- `currentState.nextAction`: updated to point at the UBP closure path.
- `lastUpdate`: 2026-05-09T03:00:00Z → 2026-05-09T03:30:00Z.

### `research/problems/erdos-1151-oq-04/state.md`

- Iteration: 29 → 30.
- Added "Session 30" header section at top with full narrative.
- Updated S29 header from "this session" to "merged via #17580".
- Rewrote "Next Steps" sections 1 and 2 to reflect S29 closure + S30
  refactor.
- Updated "Open PRs" and "File Stats" footer.

## Build status

`[BUILD UNVERIFIED]` — Statement-only refactor of the trailing two
theorems in the file (lines 2535–2606). Following the precedent of S26
(#17486), S27 (#17505), S28 (#17544), S29 (#17580), this PR is submitted
build-pending.

The change is purely structural:
1. The new conclusion uses only Real arithmetic (`|·|`, `<`, `∃`) — no
   new imports needed.
2. The corollary's proof body is byte-identical (still
   `divergence_from_lebesgue_growth _ (chebyshev_lebesgue_growth p q hp hq hq_pos)`)
   — the conclusion-type change unifies with the new statement
   automatically.
3. The sorry remains at the body of `divergence_from_lebesgue_growth` and
   continues to elaborate as a placeholder for the new (weaker) goal.

No external Lean callers exist (verified via grep over `proofs/`):
`erdos_1941_divergence_from_growth` is referenced only in this file's
docstrings and gallery JSONs/markdowns (text mentions only).

## Sorry inventory after S30

`Erdos1151OQ04.lean` (2610 lines, **1 sorry**):

  1. `divergence_from_lebesgue_growth` — Banach–Steinhaus on
     `C[-1, 1] →L[ℝ] ℝ`. Conclusion now in unboundedness form.

## Test plan

- [x] `wc -l proofs/Proofs/Erdos1151OQ04.lean` returns 2610.
- [x] `grep -c "^\s*sorry\b" proofs/Proofs/Erdos1151OQ04.lean` returns 1.
- [x] `python3 -c "import json; json.load(open(...erdos-1151-oq-04.json))"`
      validates without error.
- [x] No external Lean callers of `erdos_1941_divergence_from_growth` or
      `divergence_from_lebesgue_growth` (grep over `proofs/`).
- [ ] Docker build of `Proofs.Erdos1151OQ04` succeeds (build-pending).
