# Research State: erdos-1006-oq-01-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-08
**Iteration**: 5
**PR**: goal achieved in merged PR #27222 (de-axiomatization); S4 reconciles state

## Outcome
**Goal — "Prove `cover_graph_characterization` without axioms" — ACHIEVED.**

On `origin/main`, `proofs/Proofs/Erdos1006OQ01.lean`:
- `cover_graph_characterization` is a proved `theorem` (line 371), `0 sorry`.
- Forward direction: the reachability order `reachOrder` (RTG closure of arcs as
  a `PartialOrder`) + helpers `rank_le_of_rtg`, `rank_lt_of_tg`, `lift_below`,
  `lift_above`.
- Reverse direction: `cover_graph_admits_robust`.
- The `hasDependentArc` soundness bug (S1/S2) is fixed via the reachability
  formulation (S3 / merged PR #27154).

## Remaining axioms (out of scope)
The file still has **2 axioms**, both deep results that are NOT this problem's
target and belong to separate problems:
1. `chromatic_lt_girth_implies_robust` — Fisher-Fraughnaugh-Langley-West (1997).
2. `nesetril_rodl_counterexample` — Nesetril-Rodl (1978).
Each needs 1000+ lines of foundational (probabilistic / explicit extremal)
machinery absent from Mathlib. Left as documented `axiom` deliberately.

## Verification
File is byte-identical to `origin/main`, where it landed via merged PR #27222
(self-described "verified"). Build gate was CLOSED this session (host load ~13.3,
3 `lean-build` containers), and no Lean change was made, so no re-compile.

## Next Action
None - goal complete. Pursue the two remaining deep axioms as their own problems
if desired.
