# Research State: birthday-problem-oq-01-oq-01-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 2

## Current Focus
Non-uniform generalization surveyed. Precise formal target fixed:
`E[X] = C(n,2)·Σpₖ²` with the sharp result `Σpₖ² ≥ 1/d` (uniform minimizes
expected collisions, via Cauchy–Schwarz).

## Active Approach
Definitional model matching the parent's rigor (`collisionProb p = Σ (p k)²`,
`expectedCollisions n p = C(n,2)·collisionProb p`), plus the CS lower bound.
See knowledge.md "Recommended formal target (ACT plan)".

## Attempt Count
- Total attempts: 0 (survey only)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
ACT (writing/compiling `BirthdayProblemOQ01OQ01OQ03.lean`) is gated by the
2026-06-13 Docker/`lake build` verification outage. Math is BUILD-tractable
(<300 lines, the only non-trivial lemma — Cauchy–Schwarz — already exists at
`ProbMethodSecondMoment.lean:78`). No missing Mathlib infrastructure.

## Next Action
When Docker/verification is restored: implement T1–T4 from the ACT plan in
`proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean`, build via
`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ01OQ03`,
then promote status to completed.
