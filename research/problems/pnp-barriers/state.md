# Research State: pnp-barriers

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-03-14
**Iteration**: 4

## Current Focus
Axiom elimination in PNPBarriersSound.lean (21→15 axioms).

## Active Approach
Abstract complexity class definitions with barrier theorems. Identifying axioms derivable from other axioms or model structure.

## Attempt Count
- Total attempts: 4
- Current approach attempts: 4
- Approaches tried: 1

## Blockers
- Remaining 15 axioms are mostly fundamental (BGS constructions, opaque Φ properties, program composition).
- Model limitations: algebraic extension unused, PH doesn't thread oracle through levels.

## Next Action
Consider proving P_rel_subset_NP_rel from definitions (currently axiom — may require program construction impossible with opaque Φ), or migrate barrier theorems from PNPBarriers.lean to Sound model.
