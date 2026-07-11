# Current State

**Phase**: MAKING PROGRESS
**Since**: 2026-07-08
**Iteration**: 4

## Current Focus

Added an **elementary finite upper bound on the faithful supremum**: `sublevelSup' ≤ 4`
(`sublevelSup'_le_four`), pinning the open extremal constant to a concrete interval
`sublevelSup' ∈ [2√2, 4]` (`sublevelSup'_mem_Icc`) with no potential theory. Mechanism
(`one_le_abs_eval_of_ge_two`): for faithful `f = ∏(X − r)`, each `|x − r| ≥ |x| − 1 ≥ 1`
when `|x| ≥ 2`, so `sublevelSet f ⊆ (−2, 2)` (`sublevelSet_subset_Ioo`) and
`sublevelMeasure f ≤ vol(−2,2) = 4` uniformly (`sublevelMeasure_le_four`). Axiom-free.

Previously: infimum side (`sublevelInf ≤ 2` via linear `X`) and BOTH extremal quantities.

## Active Approach

Elementary/measure-theoretic. Sup side: quadratic x²−1 attains 2√2 → `le_iSup_of_le`.
Inf side: linear X attains 2 → `iInf_le_of_le`. No axioms, no sorries.

## Blockers

The **sharp** upper bound `sublevelSup' = 2√2` needs logarithmic potential theory (Tao
2025) absent from Mathlib — but the elementary non-tight `≤ 4` is now machine-checked, so
the supremum is provably finite. Infimum exact value open (2^(4/3)−1 ≤ inf ≤ 1.835); the
`≤ 2` bound is honest but not tight — sharpening it needs (x+1)(x−1)^m and potential theory.

## Next Action

Provable directions done: `2√2 ≤ sublevelSup' ≤ 4` (sandwich) and `sublevelInf ≤ 2`.
Tightening either endpoint to the sharp value requires potential theory beyond Mathlib.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1
- Approaches tried: 4
