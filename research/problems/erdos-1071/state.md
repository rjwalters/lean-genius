# Current State

**Phase**: COMPLETED
**Since**: 2026-05-17T05:23Z (S4 STATE-SYNC: long-completed slug + research-JSON drift catchup)
**Iteration**: 4

## Current Focus

Registry / pool / state.md reconciliation. The Lean formalization has been
complete since PR #10880 (`Erdős #1071: add Zorn existence proof + Danzer
axiom`, merged 2026-04-21, T−26d). `research/registry.json` records the
slug as `COMPLETED`/`graduated` since 2026-03-24, but the per-slug research
JSON (`src/data/research/problems/erdos-1071.json`), the pool, and this
state.md all retained pre-completion fields. S4 makes them all agree.

## Active Approach

None — formalization complete.

`proofs/Proofs/Erdos1071Problem.lean` (323 lines) formalizes Erdős and
Tóth's question on maximal packings of unit segments in the unit square.
It proves:

1. **Existence of a maximal packing** (`exists_maximal_packing`) via
   Zorn's lemma on the partial order of packings under set inclusion, using
   `Set.zorn_subset` and a chain-union lemma (`packing_chain_union`).
2. **Witness packing** (`packing_singleton` + `horizontalMidSegment`) showing
   the maximal-packing set is non-empty (`maximal_packing_nonempty`).
3. **Structural framework**: `UnitSegment` (ℝ×ℝ endpoints with
   `unit_length: euclidDist = 1`), `IsPacking`, `IsMaximalPacking`,
   `AreDisjoint`/`EndpointDisjoint`, `IsFinitePacking`,
   `IsCountablyInfinitePacking`, plus 23 supporting theorems/lemmas
   (Euclidean distance algebra, convexity of the unit square, segment-in-
   square reasoning).

Part (a) of Erdős' question — *does a finite maximal packing exist?* — is
the Danzer result (`$10 prize`). It is *axiomatized* in
`danzer_finite_maximal_packing` (Erdos1071Problem.lean:295). The axiom
states the existence of a finite maximal packing of unit segments in the
unit square. This is one assumption — Mathlib does not currently contain
Danzer's construction. Reducing this to a constructive `theorem` would be
a substantial geometric-combinatorics formalization project.

Part (b) — *is there a region $R$ admitting a countably infinite maximal
packing of unit segments?* — remains the OPEN Erdős conjecture. It is
*stated* in the file (`Region`, `IsRegionPacking`, `IsMaximalRegionPacking`)
but not assumed true: no axiom claims the answer.

## Blockers

The only remaining "blocker" to a `verified` badge is Danzer's $10-prize
construction, which has not been formalized in Mathlib and is unlikely
to be a session-scale task. Status `axiomatized` (badge `axiom`) honestly
reflects the 1 standing assumption. The OPEN part (b) is correctly stated
as a `Prop`, not assumed.

## Next Action

None for the slug — graduated and gallery-complete. Optional future work
(not required for completion):

- **Constructive Danzer**: replace `axiom danzer_finite_maximal_packing`
  with a concrete witness. Danzer's published configuration uses a finite
  arrangement of segments and a geometric maximality argument. Estimated
  ~500–1500 LOC of Mathlib-style geometry.
- **Region-packing examples**: concrete `Region` witnesses for part (b) —
  e.g., spirals or wedge sequences with countably many disjoint unit
  segments. Even non-maximal countably-infinite-packing examples would
  strengthen the file's narrative of the open question.
- **Convexity/measure refinements**: tighten `unitSquare_convex` to use
  `Convex` directly rather than `nlinarith` on the four boundary
  inequalities (cosmetic).

S4 itself is doc-only: no Lean edit, no gallery `meta.json` edit, no
sibling-slug edit, no proof regression. After merge, the pool entry will
be re-flipped to `completed` via `claim-problem.sh update erdos-1071
completed`.

## Attempt Counts

- Total attempts: 4 (Sessions 1–3 = the four Lean-bearing PRs #6190 /
  #6993 / #7633 / #10880 collapsed by older convention to "iteration 3",
  S4 = this STATE-SYNC = +1)
- Current approach attempts: 0
- Approaches tried: 2 (axiomatic skeleton → Zorn + Danzer-axiom split)
