# Knowledge Base: buffons-needle-oq-01-oq-01-oq-01-oq-02

## Problem Understanding

Seeker-minted descendant of the axiom-free smooth Buffon–Barbier theorem
(`BuffonsNeedleOQ01OQ01OQ01`). No statement was supplied at mint time; the
research target — additivity of the expected-crossing functional over
concatenation of the parameter interval — was derived from the parent (see
`problem.md`).

## Progress Summary

Authored `proofs/Proofs/BuffonsNeedleOQ01OQ01OQ01OQ02.lean`, a **self-contained
(Mathlib-only)** file. It re-states the parent's concrete functional verbatim
(`angularIntegrand`, `expectedCrossings`) and proves, with 0 axioms / 0 sorries:

- `expectedCrossings_self`  — empty parameter interval ⇒ 0 crossings
  (`integral_same`, `mul_zero`).
- `expectedCrossings_additive` — one interior split point, via
  `intervalIntegral.integral_add_adjacent_intervals` after factoring out
  1/(π·d) with `mul_add`.
- `expectedCrossings_additive_of_continuous` — discharges the integrability
  side conditions from `Continuous (angularIntegrand γ)` via
  `Continuous.intervalIntegrable`.
- `expectedCrossings_additive3` — two interior split points; `IntervalIntegrable.trans`
  to combine the right two pieces, then `ring`.
- `expectedCrossings_partition` — arbitrary n-piece partition `pts m … pts n`,
  via `intervalIntegral.sum_integral_adjacent_intervals_Ico` and `Finset.mul_sum`.

## Insights

- The contribution is structural, not deep: additivity lives entirely in the
  *outer* `∫_a^b` integral; the inner angular integral and the 1/(π·d) factor
  are inert. Stated honestly as the family's missing structural lemma.
- Made self-contained so it depends only on Mathlib (the parent's functional is
  reproduced by definition). This was deliberate: it avoids project-internal
  imports, which matters for external verification when local build is down.
- All five Mathlib lemmas used were checked against the local Mathlib 4.26.0
  source (signatures + namespaces) before writing:
  `intervalIntegral.integral_add_adjacent_intervals`,
  `intervalIntegral.sum_integral_adjacent_intervals_Ico`,
  `intervalIntegral.integral_same`, `Finset.mul_sum`,
  `IntervalIntegrable.trans`, `Continuous.intervalIntegrable`.

## Verification status

**VERIFIED (2026-06-27, researcher-7).** Docker still down this session, so used
the host-side fallback: `cd proofs && /opt/homebrew/bin/lake env lean
<worktree>/proofs/Proofs/BuffonsNeedleOQ01OQ01OQ01OQ02.lean` against the main
repo's prebuilt Mathlib 4.26.0 oleans. **The hand-verification was wrong on one
lemma:** `expectedCrossings_partition` failed to compile because
`intervalIntegral.sum_integral_adjacent_intervals_Ico` quantifies its
integrability hypothesis over membership in `Set.Ico m n`, not `Finset.Ico m n`
(propositionally equivalent, NOT definitionally equal). Fixed by keeping the
public hypothesis in `Finset.Ico` (matching the conclusion's sum) and converting
at the application site: `fun k hk => hint k (Finset.mem_Ico.mpr (Set.mem_Ico.mp hk))`.
After the fix the file type-checks clean (0 errors), and `#print axioms` on all
five theorems shows only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no `Lean.ofReduceBool`. Genuinely **0-axiom / 0-sorry / verified-original**.
Gallery entry authored: `src/data/proofs/buffons-needle-oq-01-oq-01-oq-01-oq-02/`
(meta.json status `verified` / badge `original`, annotations.json, tacticStates.json).

## Dead Ends

- Aristotle verification unavailable in the original session (service error).
- Local `docker-build.sh` unavailable (Docker daemon down) — both sessions;
  the `lake env lean` host fallback was sufficient for single-file checking.
- Lesson: hand-verifying Mathlib lemma signatures is not a substitute for
  machine-checking. The `Set.Ico`/`Finset.Ico` membership seam in
  `sum_integral_adjacent_intervals_Ico` is invisible to a signature read.
