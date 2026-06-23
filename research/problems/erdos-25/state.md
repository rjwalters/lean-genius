# Current State

**Phase**: ACTIVE_RESEARCH
**Since**: 2026-05-08
**Iteration**: 2

## Current Focus

Strengthen the structural toolkit around `sievedSet` and surface a clean
*reduction*: ErdosProblem25 follows from natural-density existence of
sieved sets. This isolates a sufficient condition expressed in a more
classical density notion than `HasLogDensity`.

## Active Approach

Three additions to `Erdos25Problem.lean`:

1. `sieve_monotone_set`: Generalization of `sieve_monotone` from a single
   index to a Set of indices. Same proof, more general statement.
2. `sieved_set_logDensity_of_naturalDensity`: Direct corollary of the
   axiomatized `naturalDensity_implies_logDensity` specialized to sieved sets.
3. `LogDensityExists_of_naturalDensity`: Existence of natural density gives
   existence of log density.
4. `erdos_25_via_naturalDensity`: If every sieved set has natural density,
   then ErdosProblem25 holds. Pure reduction; provides a sufficient condition
   in classical-density terms. The converse fails by
   `exists_logDensity_no_naturalDensity` — log-density existence is strictly
   weaker — so the natural-density question is harder, but every special
   case proved on the natural-density side propagates to Erdős #25.

## Blockers

- Build verification deferred (broken `proofs/.lake` symlink in main repo).
  Marked PR as build pending per convention.

## Next Action

Iteration 3 candidates:
- Prove `sievedSet σ` has natural density when σ has only finitely many
  *distinct* moduli (use sieve_monotone_set + the periodic structure).
- Prove the union of pairwise-coprime modular exclusions has natural density
  via inclusion-exclusion (CRT step).
- Concrete instance: define `sieveAllMultiples : seq_n i = i+2, seq_a i = 0`,
  prove `sievedSet sieveAllMultiples = {0, 1}`, conclude log density 0 via a
  finite-set argument.

## Attempt Counts

- Total attempts: 2 (iteration 1 was initial axiomatization, this is iter 2)
- Current approach attempts: 1
- Approaches tried: structural lemmas (monotonicity), reduction to natural
  density
