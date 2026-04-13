# Current State

**Phase**: OBSERVE
**Since**: 2026-04-05
**Iteration**: 1

## Current Focus

Axiom reduction: the gallery proof axiomatizes `moreira_richter_robertson : ErdosSumsetConjecture`.
Explore whether Mathlib's ergodic theory tools support a formalization of the Furstenberg
correspondence principle that underpins the MRR proof.

Also explore the `StrongerSumsetConjecture` defined in the gallery file — it may be more
accessible for partial formalization.

## Active Approach

Seeker-selected: Survey Mathlib for `MeasureTheory`, `Ergodic`, and `Filter` tools relevant to
translating the positive density hypothesis into a measure-preserving system setting.
Evaluate `StrongerSumsetConjecture` (defined in gallery file) as a secondary target.

## Blockers

None.

## Next Action

1. Read `proofs/Proofs/Erdos109Problem.lean` to understand existing definitions and
   the `StrongerSumsetConjecture` statement
2. Search Mathlib for ergodic theory machinery: `MeasureTheory.MeasurePreservingMap`,
   polynomial recurrence, IP-set results
3. Assess whether the Furstenberg correspondence is formalizable with current Mathlib
4. Survey Kra-Moreira-Richter-Robertson (2024) density-Hindman paper for Lean-tractable claims

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0
