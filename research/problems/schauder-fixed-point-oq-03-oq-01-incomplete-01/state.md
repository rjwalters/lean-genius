# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ORIENT (axiom revision needed)
**Path**: full
**Since**: 2026-05-08T15:30:00Z
**Iteration**: 5

## Current Focus
S6 (researcher-6, 2026-05-08): Mathematical analysis surfaces a critical
issue with the chosen proof strategy. The axiom `approx_selection_exists`
is **false as stated** under USC + convex values alone. A 1-D counterexample
shows no continuous pointwise `(1/3)`-approximate selection exists for
`F : [-1,1] → 2^[-1,1]` with `F(0)=[0,1]`, `F(t>0)={0}`, `F(t<0)={1}`.
See `s6-axiom-counterexample.md` for the full analysis (verbatim
definitions, USC verification, no-`f` proof via continuity-at-zero IVT,
and the Cellina–Browder graph-form salvage).

## Active Approach
Revise the axiom to the provable graph form (Cellina–Browder) and rethread
`kakutani_from_brouwer` through it (≈10-line edit using triangle
inequality, with the helper `approx_fixedpoint_implies_fixedpoint`
unchanged). Only after that is the PartitionOfUnity proof of the
*graph form* tractable.

## Attempt Count
- Total attempts: 2
- Approaches tried:
  - S2 documentation (researcher-3, #16731);
  - S3 full proof submission (researcher-11, #16784);
  - S4 build verification + meta sync (researcher-10);
  - S5 PR flush off fresh main (researcher-?, content already on main);
  - S6 axiom-strength counterexample analysis (researcher-6, this PR).

## Blockers
None at the math level — the path forward (graph-form axiom + 10-line
`kakutani_from_brouwer` patch) is concrete. The PartitionOfUnity proof
itself remains a separate, larger Mathlib-API task.

## Next Action
S7: edit `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`:

1. Add `IsGraphApproxSelection` definition (graph form, see analysis doc).
2. Restate `approx_selection_exists` to use the graph form. Update
   docstring to cite Cellina–Browder and remove the (incorrect) pointwise
   step-6 sketch.
3. Patch `kakutani_from_brouwer` to chain
   `dist(x', y) ≤ dist(x', x₀) + dist(x₀, f_ε(x₀)) + dist(f_ε(x₀), y) < 2ε`
   when feeding `approx_fixedpoint_implies_fixedpoint` (substitute ε ↦ 2ε
   in the outer existential — harmless).
4. Verify build via Docker (`./proofs/scripts/docker-build.sh
   Proofs.SchauderFixedPointOQ03OQ01`).
5. (Optional, S8+) Attempt the PartitionOfUnity proof of the graph form.

A separate follow-up should also note that `brouwer_fpt`'s extension from
Mathlib's unit-ball Brouwer to general compact convex `S` is provable
via a retraction argument and is the easier of the two axioms.
