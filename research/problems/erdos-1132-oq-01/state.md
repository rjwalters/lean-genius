# Research State: erdos-1132-oq-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-05T13:26:15-07:00
**Iteration**: 1

## Current Focus

Axiom reduction: the parent proof `erdos-1132` axiomatizes two classical results from
approximation theory: `bernstein_density_theorem` (Bernstein 1931) and `erdos_max_theorem`
(Erdős 1961). Primary target: prove `erdos_max_theorem` — that the maximum of the Lebesgue
function Λ_n over [-1,1] exceeds (2/π)log(n) - C for some constant C.

## Active Approach

Seeker-selected: Explore Mathlib's polynomial and analysis infrastructure for Lagrange
interpolation and Chebyshev polynomials. Assess whether a proof of `erdos_max_theorem`
is feasible via Chebyshev orthogonality or a concrete equidistant-nodes calculation.
Most tractable entry point: show Λ_n diverges at a specific point for equidistant nodes.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action

1. Read `proofs/Proofs/Erdos1132Problem.lean` in full — understand existing definitions
   (`lebesgueFunction`, `lebesgueConstant`, `InfiniteNodeSequence`, `denseGoodPoints`)
2. Search Mathlib for Chebyshev polynomial tools: `Polynomial.Chebyshev.T`, orthogonality
3. Search Mathlib for `Real.iSup` machinery needed for the Lebesgue constant supremum
4. Assess Approach B (equidistant nodes, concrete Λ_n(0) calculation) as quickest win
