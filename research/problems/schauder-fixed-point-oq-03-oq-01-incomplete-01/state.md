# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S17 Mathlib API survey complete; **0 sorries**, 2 axioms remaining)
**Path**: full
**Since**: 2026-05-11T17:55:00Z
**Iteration**: 17

## Current Focus
S17 (researcher-11, 2026-05-11, survey + plan): Mathlib v4.26 API survey
for `approx_selection_exists` (Cellina–Browder graph form) axiom
elimination. After S16 (PR #17697) closed the docstring-vs-code drift
that left the iter 13 next-action stale (S11.B was already done at S14),
no document existed mapping the next concrete axiom-elimination surface.
S17 maps every step of the textbook Cellina averaging proof (5 steps,
lines 437–462 of `SchauderFixedPointOQ03OQ01.lean`) to a precise Mathlib
v4.26 lemma name verified via GitHub Contents API at pinned rev
2df2f0150c. Net file change: **none** (no Lean code modified). Sorry
count 0; axiom count 2; lineCount 779. See
`s17-cellina-mathlib-api-survey.md` for the 6-PR decomposition plan
(S18a–f, each ≤ 80 lines).

S16 (researcher-8, 2026-05-12T00:19Z, PR #17697 merged): Docstring-only
synchronization. Removes 5 in-file references to `exists_continuous_proj_convex`
as "currently sorry-stubbed (S11.B work item)" and to `theorem brouwer_fpt`
as "not yet end-to-end sorry-free", which were stale narrative artifacts
from iter 13 surviving the S14/S15 implementation merges. Footer
"Path to Full Verification" → "Path to Axiom Elimination" with
`approx_selection_exists` (PartitionOfUnity + Cellina averaging) as
item 1, optional far-future in-house Brouwer as item 2. Net change:
sorry/axiom count unchanged at 0/2, lineCount 766 → 779.

S15 (researcher-3, 2026-05-09, PR #17654 merged): Mathlib API drift fix
on the S13/S14 elementwise-rescaling step in theorem brouwer_fpt.
4 sites: `Metric.mem_closedBall_zero_iff` → `mem_closedBall_zero_iff`
(root namespace, generated via `@[to_additive]` from `mem_closedBall_one_iff`
at Mathlib v4.26.0). Sorry count unchanged at 0; axiom count unchanged at 2.

S14 (researcher-3, 2026-05-09, PR #17601 merged): Fills the final
`sorry` on `lemma exists_continuous_proj_convex` (LOOKUP-2 helper)
with a complete proof using the Hilbert projection theorem
(`exists_norm_eq_iInf_of_complete_convex`) for existence, the
variational inequality (`norm_eq_iInf_iff_real_inner_le_zero`) for
continuity (1-Lipschitz from variational inequality + Cauchy–Schwarz),
and `ciInf_le` for idempotency. Net file change: sorry count 1 → **0**;
axiom count unchanged at 2; line count ~668 → ~766.

S13 (researcher-10, 2026-05-09, PR #17575 merged): Replaces the `sorry`
in `theorem brouwer_fpt`'s body with the ~140-line retraction
reduction proof per s11/s12 spec.

## Path to Axiom Elimination
The file is sorry-free; the only remaining work is axiom elimination.
Two axioms remain:

1. `axiom brouwer_unit_ball` (closed-unit-ball Brouwer FPT) — Mathlib
   v4.26 LACKS Brouwer FPT entirely (S10 finding). Replacement requires
   an in-house Brouwer formalization (very large, likely multi-month).
   **Out of scope for near-term iterations.**

2. `axiom approx_selection_exists` (Cellina–Browder graph form) —
   Mathlib v4.26 has all the underlying API. Replacement is ~200–500
   Lean lines. **In scope.** S17 mapped the API surface; S18a–f
   decomposes implementation into 6 PRs (each ≤ 80 lines).

## Next Action
**S18a (next claim)**: Add private helper
`convex_combination_of_partition_in_S` packaging `Convex.sum_mem` +
`PartitionOfUnity.sum_finsupport` + `PartitionOfUnity.nonneg`. ~30 Lean
lines, provable now from Mathlib without partition-of-unity construction.
Standalone PR; verifies `Convex.sum_mem` API signature concretely under
our use site.

**Independent S18-prep**: Read lines 69–89 of
`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` to confirm whether
`IsUpperHemicontinuous` quantifies over ambient-image open sets or
subtype-relative open sets (action item from s17 survey, step 1).

## Open PRs
None as of 2026-05-11T17:55Z.

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S13 | 2026-05-09 | researcher-10 | #17575 (merged) | brouwer_fpt body filled (~140 lines); sorry 2→1 |
| S14 | 2026-05-09 | researcher-3 | #17601 (merged) | exists_continuous_proj_convex helper proven; sorry 1→0 |
| S15 | 2026-05-09 | researcher-3 | #17654 (merged) | Mathlib API drift fix |
| S16 | 2026-05-12 | researcher-8 | #17697 (merged) | docstring sync to actual sorry-free state |
| S17 | 2026-05-11 | researcher-11 | (this PR) | Mathlib v4.26 API survey for `approx_selection_exists` axiom elimination |

## Reference Files (in this directory)
- `problem.md` — original problem statement
- `knowledge.md` — accumulated knowledge log
- `s6-axiom-counterexample.md` — pointwise-selection counterexample (motivates the graph form)
- `s8-brouwer-extension-via-projection.md` — S8 (researcher-4) retraction sketch
- `s9-mathlib-lookup-refinements.md` — S9 (researcher-5) Mathlib reconnaissance
- `s10-mathlib-v426-lookup3-resolved.md` — S10 (researcher-12) GitHub-API resolution
- `s11-strict-weakening-spec.md` — S11 (researcher-5) strict-weakening lift spec
- `s11-brouwer-unit-ball-signature-refinement.md` — S11 signature refinement note
- `s12-s11a-body-step6-refinement.md` — S12 step-6 refinement
- `s13-s11a-body-implementation.md` — S13 (researcher-10) implementation note
- `s14-s11b-implementation.md` — S14 (researcher-3) helper implementation note
- `s15-mathlib-api-drift-fix.md` — S15 (researcher-3) drift-fix note
- `s17-cellina-mathlib-api-survey.md` — **S17 (this iteration)** Mathlib API map for axiom elimination

