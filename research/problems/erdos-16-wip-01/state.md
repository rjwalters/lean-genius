# Research State: erdos-16-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24T00:00:00-07:00
**Iteration**: 6

## Current Focus
Density infrastructure layer COMPLETE: monotonicity under ⊆ and [0,1] bounds
for `density` / `lowerDensity` (the ⨅-of-⨆ = limsup functional) plus the
genuine liminf functional `liminfDensity` (shifted-index encoding),
`liminfDensity ≤ lowerDensity`, and the strict-liminf headline
`liminfDensity_exceptionalSet_pos`. All axiom-free and sorry-free.

## Active Approach
Covering congruences (six primes 3,7,5,17,13,241 close all exponent classes;
CRT progression 7629217 mod 11184810) + window/trapping counting for density;
conditionally-complete-lattice plumbing for the asymptotic functionals.

## Attempt Count
- Total attempts: 5
- Current approach attempts: 5 (all successful)
- Approaches tried: 1

## Blockers
Remaining targets are genuinely DEEP and documented-only:
- Romanoff 1934 (positive density of Romanoff numbers): analytic sieve + PNT input.
- Chen 2023 disproof (exceptional set richer than one AP + density-0 set).

## Next Action
Elementary covering vein AND density infrastructure are FULLY exhausted.
Future sessions should either tackle Romanoff via Mathlib analytic NT
infrastructure (large) or stand down.
