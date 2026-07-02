# Research State: prime-gap-bounds-oq-02

## Current State
**Phase**: PROGRESS
**Iteration**: 2

## Current Focus
Feasibility assessment of "Rosser–Schoenfeld bounds on π(x) from explicit zero-free
regions". Split the problem into an achievable 0-axiom upper bound and a blocked
lower bound; identified the exact Mathlib API and the obstacle.

## Active Approach
Explicit Chebyshev **upper** bound on π: from Mathlib's `theta_le_log4_mul_x`
(θ x ≤ log 4 · x), derive `π(x) ≤ √x + (log 16)·x/log x` via the tail estimate
θ(x) ≥ (½ log x)(π(x) − π(√x)). 0-axiom. See knowledge.md.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (0-axiom feasibility mapping)

## Blockers
- **θ/ψ ↔ Nat.primeCounting bridge is not in Mathlib** (explicit TODO in
  `Chebyshev.lean`). Must be built (~120–160 lines) before the upper bound proof.
- **Chebyshev lower bound not in Mathlib** (also a TODO) → the lower half
  `x/log x < π(x)` and the sharp `1.25506` constant are blocked (need explicit PNT
  + zero-free region).

## Next Action
Implement the θ↔primeCounting bridge and the tail subset-sum estimate to prove the
0-axiom explicit upper bound `π(x) ≤ √x + (log 16)·x/log x`. Ship as `verified`;
leave the lower bound / sharp constant as disclosed open directions.
