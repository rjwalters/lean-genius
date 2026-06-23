# Research State: shapley-folkman-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 2

## Current Focus
Build-free ORIENT under the Docker + Aristotle verification blackout. Pinned
the precise gap between the gallery parent and Starr's metric bound, mapped the
Mathlib bearer landscape, and produced a durable numerical verification of the
bound (constant, m-independence, sharpness).

## Active Approach
Approach 1 (problem.md): Shapley-Folkman decomposition + per-summand radius
bound + sqrt(min(m,n)) ℓ² aggregation. The combinatorial half already exists in
the parent file as `sum_close_to_convexHull`; the open work is the *metric*
upgrade (replace each convexified summand by a nearest point of S_i and bound
the aggregate displacement).

## Attempt Count
- Total attempts: 1 (ORIENT survey + numerical verification)
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Docker down + Aristotle 404 (verification blackout, 2026-06-14): no Lean
  build possible this session. No `.lean` committed.

## Next Action
ACT (when a backend is up): formalize the metric bound on top of
`sum_close_to_convexHull`. Define `rad`/circumradius via `Metric.diam` or a
minimum-enclosing-ball, prove the per-summand displacement bound, then the
sqrt(min(m,n)) aggregation (the only genuinely new lemma). See knowledge.md for
the bearer map and the empirically-confirmed constant.
