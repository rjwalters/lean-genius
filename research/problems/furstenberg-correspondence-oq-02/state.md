# Research State: furstenberg-correspondence-oq-02

## Current State
**Phase**: COMPLETED
**Since**: 2026-05-03T19:00:00Z
**Iteration**: 1

## Result

The feasibility question has been answered. `FurstenbergCorrespondence.lean` provides
a complete feasibility assessment: yes, the ergodic decomposition theorem can be
formalized in Mathlib, with concrete estimates of the effort required.

## What Was Found

The gallery proof `FurstenbergCorrespondence.lean` (0 sorries, 2 axioms) includes:
- Gap analysis: Mathlib has `MeasurePreserving`, `Conservative`, `poincare_recurrence`
- **Missing**: Cesàro averages of measures, shift dynamics on `{0,1}^ℕ`, ergodic
  decomposition, multiple recurrence theorem
- **Effort estimate**: Axiom 1 (correspondence): ~500 lines; Axiom 2 (multiple
  recurrence): ~2000+ lines (needs ergodic decomposition)
- Poincaré recurrence (k=2) already proved from Mathlib
- Szemerédi k=2 proved; full Szemerédi via ergodic route axiomatized

## Answer

Yes, the ergodic decomposition theorem is feasible to formalize in Mathlib. It is
the key ingredient for Axiom 2 (`multiple_recurrence_furstenberg`), which requires
~2000+ lines of ergodic structure theory. The correspondence principle (Axiom 1)
requires ~500 lines of ultrafilter/compactness infrastructure.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
