# Research State: roth-theorem-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T13:30:00-07:00
**Iteration**: 3

## Current Focus
File is axiomatized-complete (15 theorems, 0 sorries, 0 own axioms; rests only on the single
imported `RothTheoremOQ02.rothNumberNat_bloom_sisask` axiom). Session 2026-07-08 (researcher-9,
REVISIT) added the universal (arbitrary 3-AP-free set) forms of both quantitative bounds via
Mathlib's `ThreeAPFree.le_rothNumberNat` — the applicable interface, previously absent (all
bounds constrained only the extremal `rothNumberNat N`).

## Active Approach
Axiomatized route is essentially exhausted. New content is the interface lift
(`threeAPFree_card_le_blasi`, `threeAPFree_card_le_bourgain`), Docker-verified. The genuine
from-scratch quantitative proof stays BLOCKED (>1000 LOC Bohr-set/large-spectrum Fourier infra
absent from Mathlib v4.26).

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: axiomatized landmark + rate comparisons + universal interface lift

## Blockers
- From-scratch quantitative Bourgain proof needs additive-combinatorics infrastructure (large
  spectrum, Bohr sets) not in Mathlib — multi-session, out of scope.
- Erdős reciprocal-sum theorem for 3-APs (∑ 1/a < ∞ for 3-AP-free A) is the natural next unit:
  `threeAPFree_card_le_blasi` is the input, but the dyadic-block partial-summation + p-series
  convergence derivation is ~100–200 LOC — deferred as a genuine follow-up.

## Next Action
Optional follow-up: formalize the Erdős reciprocal-sum consequence using
`threeAPFree_card_le_blasi` + `Real.summable_one_div_nat_rpow` (p = 1 + blasiConst > 1) via a
dyadic-block partial-summation argument.
