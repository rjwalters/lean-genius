# Research State: shapley-folkman

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-04-27
**Iteration**: 1

## Current Focus
Stable, fully verified formalization of the Shapley-Folkman lemma.

- `proofs/Proofs/ShapleyFolkman.lean`: 1238 lines, 8 theorems, 0 axioms, 0 sorries
- `proofs/Proofs/ShapleyFolkmanAristotle.lean`: 81 lines, 8 theorems, 0 axioms, 0 sorries
- `proofs/Proofs/ShapleyFolkmanOQ03.lean`: 203 lines, 5 theorems, 0 axioms, 0 sorries

Main theorem proved by WF induction on total minCaraDepth. Docker build passes.
Originally formalized in PR #7333; final clean build / WF induction landed in
PR #12242. Targeting Mathlib contribution (mathlib4#14427).

## Active Approach
None — formalization complete.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
None — formalization is complete and verified. Future work is the Mathlib
upstream contribution (separate workstream).
