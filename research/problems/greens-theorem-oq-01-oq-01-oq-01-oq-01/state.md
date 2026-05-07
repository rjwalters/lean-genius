# Research State: greens-theorem-oq-01-oq-01-oq-01-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-05-07T00:00:00+03:00
**Iteration**: 4

## Outcome
**PROVED**: `iteratedIntervalIntegral_order_independent` from first principles, 0 sorries, 0 axioms.

## What Was Proved

- `continuous_param`: parameterized iterated integral is continuous (DCT induction on n)
- `integrable_swap_pair`: integrability for the 2-variable Fubini swap
- `swap01_cons_eq`: Fin arithmetic for the 0↔1 transposition computation
- `swap_outer_two`: Fubini swap of integration positions 0 and 1
- `iteratedIntervalIntegral_perm_tail`: inner permutation reduction (IH inside outer integral)
- `iter_integral_swap_zero`: integral identity for any transposition swap(0,k)
- `iter_integral_swap_any`: integral identity for any transposition swap(x,y)
- `iteratedIntervalIntegral_order_independent`: main theorem via swap_induction_on

## Approach
- Decomposed via `Equiv.Perm.swap_induction_on`: every permutation = product of transpositions
- Each transposition handled by `iter_integral_swap_any` (uses Fubini + IH)
- Continuity proved by DCT (`continuousAt_of_dominated_interval`, compact bound)

## Attempt Count
- Total attempts: 4 sessions
- Approaches tried: 1 (Fubini + swap decomposition — succeeded)

## Blockers
None. All sorries resolved.

## Follow-Up
- oq-01: Remove redundant `axiom iteratedIntervalIntegral_order_independent` from parent file
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean`. Requires restructuring that file to not
  use the axiom internally (or introducing a Core file).
