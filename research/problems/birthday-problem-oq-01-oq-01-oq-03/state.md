# Research State: birthday-problem-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (written, build-pending)
**Path**: full
**Since**: 2026-06-14
**Iteration**: 3

## Current Focus
Non-uniform generalization surveyed. Precise formal target fixed:
`E[X] = C(n,2)·Σpₖ²` with the sharp result `Σpₖ² ≥ 1/d` (uniform minimizes
expected collisions, via Cauchy–Schwarz).

## Active Approach
Definitional model matching the parent's rigor (`collisionProb p = Σ (p k)²`,
`expectedCollisions n p = C(n,2)·collisionProb p`), plus the CS lower bound.
See knowledge.md "Recommended formal target (ACT plan)".

## Attempt Count
- Total attempts: 1 (ACT-1 file written)
- Current approach attempts: 1
- Approaches tried: 1 (definitional model + CS port)

## Blockers
ACT-1 IS ALREADY DONE — do NOT re-write the file. The full T1–T4 Lean file
`proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean` was written in open draft
**PR #23219** (branch `research/birthday-oq-01-oq-01-oq-03-act1`). It contains:
`collisionProb`/`expectedCollisions` defs, `collisionProb_uniform`/
`expectedCollisions_uniform` (T1), `collisionProb_ge` (T2, CS lower bound),
`expectedCollisions_ge` (T4), `collisionProb_eq_of_uniform` (T3 forward). The
CS step is a verbatim ℝ-port of `ProbMethodSecondMoment.sq_sum_le_card_mul_sum_sq`.

The remaining blocker is purely verification: the 2026-06-13/14 Docker/
`lake build` outage persists (`docker info` hangs >40s, build wrapper cannot
clear its daemon gate; confirmed 2026-06-14 by researcher-2). The file is NOT
machine-checked, so it cannot be promoted to completed yet.

## Next Action
When Docker is restored:
`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ01OQ03`
on branch `research/birthday-oq-01-oq-01-oq-03-act1`. If green, mark PR #23219
ready-for-review and promote status to completed. The only remaining math gap
is T3's converse (equality ⟹ uniform, the CS equality case) — optional, fiddly,
and explicitly deferred per the ACT plan.
