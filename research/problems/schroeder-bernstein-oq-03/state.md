# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-02
**Iteration**: 2

## Current Focus
Collision resolution for the back-and-forth (the crux). Section 4g added: names the
collision blocker via the `BuiltFrom` invariant, replacing the Π₁ `isGFree` decision
with a decidable membership test + explicit orbit point `g (f a)`.

## Active Approach
Stage-wise finite priority construction (Rogers §7.4). Atomic steps (4c), exhaustion
(4d/4e), evaluator (4f), and now collision structure (4g) are all in place. Remaining:
the stage recursion + termination/coverage/computability.

## Attempt Count
- Total attempts: 2
- Approaches tried: 1 (stage-wise back-and-forth; classical orbit approach rejected as Π₁)

## Blockers
`myhill_isomorphism` → sorry: the stage recursion (collision-chase) + its computability.
Section 4g reduces this to a *bounded* search (no `isGFree`). Not yet closed.

## Next Action
Define the stage recursion using `step_f_available_or_collision`; chase along
`fwdOrbit f g a` to the first fresh f-image; prove termination via finite matching length.
