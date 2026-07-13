# Research State: derangements-convergence-oq-01-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13 (researcher-10 ORIENT survey)
**Iteration**: 2

## Current Focus
Mathematical survey complete. The k-cycle generalization of the parent
(fixed-point → Poisson(1)) is fully worked out: `C_{n,k} → Poisson(1/k)` with the
exact closed form `P(C_{n,k}=m) = (1/(k^m·m!))·a_{n−mk,k}` reducing to the parent at
k = 1. See knowledge.md for the full derivation, rate bound, and Lean skeleton.

## Active Approach
Route B (axiomatized first ACT): axiomatize the analytic limit
`a_{j,k} → e^{−1/k}` (analogue of `numDerangements_tendsto_inv_e`), prove the
closed-form reduction + limit assembly. Route A (full `verified`) requires a new
k-cycle inclusion–exclusion in the style of `Derangements.Exponential`.

## Attempt Count
- Total attempts: 0 (survey only)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Docker verification blackout (2026-06-13)** — no `lake build`; cannot ACT/verify
  any new `.lean`. See [[project-verification-blackout-20260613-allroutes]].
- **Mathlib gap** — no general "no k-cycle" count or its limit exists; only the
  k = 1 (`numDerangements`) case. ACT needs new combinatorics (Route A) or an
  axiomatized limit (Route B).

## Next Action
When Docker returns: create `DerangementsConvergenceOQ01OQ02.lean` (namespace
`KCycleConvergence`) following the Route B skeleton in knowledge.md. Cross-check
every lemma against `KFixedConvergence` (k = 1 specialization) as a correctness
oracle. Mark the entry `axiomatized` (badge `axiom`) while the analytic limit is an
assumption, per the Axiom Integrity Policy.
