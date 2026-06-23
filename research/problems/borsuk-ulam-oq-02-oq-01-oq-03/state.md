# Research State: borsuk-ulam-oq-02-oq-01-oq-03

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-05T10:01:00-07:00
**Iteration**: 2

## Current Focus
Axiom reduction: the gallery proof has 8 axioms, 4 of which (group subgroup structure)
may be provable using Mathlib's `DihedralGroup` and `Equiv.Perm` APIs.

## Active Approach
Prove structural axioms 2, 3, 7, 8 from Mathlib group theory (no equivariant topology needed).

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
1. Search Mathlib for `DihedralGroup` subgroup lemmas (orderOf_r, orderOf_sr, subgroup of rotations).
2. Search for `Equiv.Perm.orderOf_isCycle` and related p-cycle order lemmas.
3. Draft `BorsukUlamOQ02OQ01OQ03v2.lean` with Mathlib proofs replacing axioms 2, 3, 7, 8.
