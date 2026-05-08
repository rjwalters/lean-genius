# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (graph-form axiom in place; build pending)
**Path**: full
**Since**: 2026-05-08T16:55:00Z
**Iteration**: 7

## Current Focus
S7 (researcher-9, 2026-05-08): Implements the salvage path identified by
S6 — replace the (provably-false) pointwise `IsApproxSelection` with the
Cellina–Browder graph form `IsGraphApproxSelection`, restate Axiom 2 in
graph form (Cellina 1969, Browder 1968), and patch `kakutani_from_brouwer`
with a triangle-inequality `ε ↦ 2·(ε/2) = ε` step so the helper
`approx_fixedpoint_implies_fixedpoint` is unchanged.

## Active Approach
With the axiom now stated in the form actually provable from USC + convex
values (the Cellina–Browder graph selection), the next layer of work is
the PartitionOfUnity proof of the graph-form axiom itself, which uses
`Mathlib.Topology.PartitionOfUnity` plus the standard Cellina averaging
argument. That proof is a separate, larger Mathlib-API task; this S7
pass changes only the axiom statement and the reduction.

## Attempt Count
- Total attempts: 7
- Approaches tried:
  - S2 documentation (researcher-3, #16731);
  - S3 full proof submission (researcher-11, #16784);
  - S4 build verification + meta sync (researcher-10);
  - S5 PR flush off fresh main (#16883);
  - S6 axiom-strength counterexample analysis (researcher-6, #17265);
  - S7 graph-form axiom + 10-line kakutani_from_brouwer patch (this PR).

## Blockers
- **Build verification deferred**: Docker build not run locally
  (`proofs/.lake` self-cycle symlink trap, see researcher-9 memory note —
  `feedback_researcher_lake_symlink_broken.md`). All Mathlib lemma names
  used in the patch are well-established (`dist_triangle`, `dist_comm`,
  `dist_self`, `linarith`, `Set.mem_univ`); CI is the ground truth.

## Next Action
**S8 (PartitionOfUnity proof of `approx_selection_exists` graph form)**:

1. Set up the Cellina averaging construction:
   - For `x ∈ S`, pick `y_x ∈ F x` and a neighborhood `U_x` with
     `F U_x ⊆ ε`-thickening of `F x` (UHC).
   - Compactness extracts a finite subcover `U_{x_1}, …, U_{x_k}`.
   - Build a subordinate partition of unity `{φ_i}` via
     `Mathlib.Topology.PartitionOfUnity`.
   - Define `f x := Σ φ_i(x) · y_{x_i}` (convex combination, lands in `S`).
2. Verify the graph bound: at any `x`, pick `i` with `φ_i x > 0`; then
   `x ∈ U_{x_i}` and `(x_i, y_{x_i})` is a graph point of `F` within `ε`
   of `(x, f x)`.
3. Discharge the axiom in Lean.

This is a sizable Mathlib-API task and is best treated as its own session.

A separate follow-up should also note that `brouwer_fpt`'s extension from
Mathlib's unit-ball Brouwer to general compact convex `S` is provable
via a retraction argument and is the easier of the two axioms.
