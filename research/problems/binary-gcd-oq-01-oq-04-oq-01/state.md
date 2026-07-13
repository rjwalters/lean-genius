# Research State: binary-gcd-oq-01-oq-04-oq-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-05T12:42:00-07:00
**Iteration**: 1

## Current Focus

Characterize the complete worst-case inputs for the Binary GCD algorithm — those where
the odd-subtraction case triggers maximally — and prove an exact step-count formula
or sharp lower bound matching the O(log(a+b)) upper bound.

The parent `binary-gcd-oq-01-oq-04` demonstrated that (1, 2^n - 1) achieves exactly n
steps. This question asks: what is the *full* worst-case structure? Can we characterize
all families achieving the tight bound?

## Active Approach

None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers

None identified yet.

## Next Action

1. Read `proofs/Proofs/BinaryGcdOQ01OQ04.lean` to understand the tight lower bound proof
2. Read `proofs/Proofs/BinaryGcd*.lean` to survey existing step-count machinery
3. Formulate what "exact worst-case" means: exact step-count formula, or just tighter bound?

## Key Context

- Parent proof (binary-gcd-oq-01-oq-04): shows binaryGcdSteps 1 (2^n - 1) = n by induction
- Gallery proof binary-gcd-oq-01 establishes O(log b) upper bound
- Known: (1, 2^n - 1) achieves n steps; question is whether this is the unique family
  or whether there are other infinite families achieving tight bounds
- Connection to Stern-Brocot tree / Calkin-Wilf tree: worst-case paths may correspond
  to specific trajectories in the binary GCD DAG
