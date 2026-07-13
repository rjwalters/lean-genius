# Research State: dirichlets-theorem-oq-03-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27
**Iteration**: 2

## Current Focus
Structural skeleton of the Linnik constant formalized axiom-free as a critical-exponent
theory (DirichletsTheoremOQ03OQ01.lean, namespace LinnikAdmissible). VERIFIED.

## Active Approach
Abstract admissible-exponent set over a base ≥ 1; ray + sandwich + monotonicity of the
infimum, with the deep number theory isolated to an explicit nonemptiness hypothesis.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Docker build host corrupt — verified via offline `lake env lean` against Mathlib oleans
(exit 0; `#print axioms` ⇒ propext/Classical.choice/Quot.sound only).

## Next Action
Optional follow-ups: decide whether the critical exponent is attained (Ici vs Ioi at the
endpoint); feed a concrete admissible witness into linnik_threshold to reduce parent axioms.
