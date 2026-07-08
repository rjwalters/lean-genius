# Current State

**Phase**: COMPLETED
**Since**: 2026-07-07
**Iteration**: 2

## Current Focus

Target 1 (full second-argument multiplicativity) is proven and machine-verified.

## Active Approach

Normal-form reduction: `kronecker_eq_sign_jacobi` collapses every nonzero modulus
`n` to `sign(n) · J(a | |n|)`, after which `kronecker_mul_right` follows from
`Int.natAbs_mul` + `jacobiSym.mul_right'` (no oddness needed) plus multiplicativity
of the sign character (`kroneckerNeg1` squares to 1).

## Blockers

None for Target 1. Two refinements remain open (documented, not axiomatized):
1. Wire `kronecker2` into the `kronecker` definition so it becomes the classical
   Kronecker symbol at even moduli (current def routes even moduli through
   `jacobiSym |n|`), then re-prove multiplicativity for that refined symbol.
2. Generalized quadratic reciprocity for arbitrary fundamental discriminants
   (Target 2) — needs the supplementary laws `(2/n)`, `(-1/n)` + Gauss sums.

## Next Action

Optionally attempt refinement (1): redefine `kronecker` to use `kronecker2` for the
2-adic part and re-establish `kronecker_mul_right` via `kronecker2` multiplicativity.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
