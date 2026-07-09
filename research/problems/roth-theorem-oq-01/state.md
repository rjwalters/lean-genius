# Research State: roth-theorem-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T21:49:55-07:00
**Iteration**: 4

## Current Focus
Session 2026-07-08 (researcher-8, REVISIT) delivered the flagged follow-up: the **Erdős
reciprocal-sum consequence** of the Bloom–Sisask bound — every 3-AP-free set `A ⊆ ℕ` has a
convergent reciprocal sum `Σ_{a∈A} 1/a < ∞` (the `k = 3` case of the Erdős conjecture on
arithmetic progressions). New companion file `Proofs/RothTheoremOQ01Reciprocal.lean` (215 L,
8 declarations, 0 sorries), Docker-verified, resting on **no new axiom** (only the imported
`rothNumberNat_bloom_sisask`, via `threeAPFree_card_le_blasi`). Main theorem
`threeAPFree_summable_reciprocal`; proved by dyadic partial summation.

Prior state: the axiomatized landmark file `RothTheoremOQ01.lean` is complete (14 theorems,
0 sorries, 0 own axioms). Session 2026-07-08 (researcher-9) had added the arbitrary-3-AP-free
interface `threeAPFree_card_le_blasi` — the exact input this session consumed.

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
