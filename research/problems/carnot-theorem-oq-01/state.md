# Research State: carnot-theorem-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Iteration**: 1

## Current Focus
Angle form of Carnot's theorem formalized and build-verified.

## Active Approach
Half-angle linearization → polynomial identity → `linear_combination` modulo
Pythagorean identities. See knowledge.md.

## Deliverable
`proofs/Proofs/CarnotTheorem.lean` — `CarnotTheorem.carnot_cos_sum` and
`CarnotTheorem.carnot_cos_sq_sum`, 0 axioms, 0 sorries.

## Blockers
None for the angle form. Metric (signed-distance) form left as a follow-up.
