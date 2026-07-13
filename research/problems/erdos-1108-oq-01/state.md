# Research State: erdos-1108-oq-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-05T15:53:25-07:00
**Iteration**: 1

## Current Focus

Explore whether the Brindza-Erdős (1991) bound (for fixed r terms, the largest
factorial index in a powerful factorial sum is bounded) can be formalized in Lean.
The gallery proof `Erdos1108Problem.lean` provides clean definitions with 0 axioms.

## Active Approach

Axiom-reduction approach: add `brindza_erdos_bound` as an axiom, then derive
consequences for the finiteness of `KthPowersInFactorialSums 2`.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action

1. Read `proofs/Proofs/Erdos1108Problem.lean` — understand current definitions
   (`FactorialSums`, `KthPowersInFactorialSums`, `PowerfulFactorialSums`)
2. Search Mathlib for `Nat.factorization_factorial` (Legendre formula for p-adic
   valuation of n!)
3. Define `brindza_erdos_bound` as an axiom with the correct Lean type
4. Attempt to derive `(KthPowersInFactorialSums 2).Finite` from the axiom
5. Survey `Mathlib.NumberTheory` for Baker-type results on linear forms in logarithms
