# Current State

**Phase**: ACT
**Since**: 2026-04-27T00:00:00Z
**Iteration**: 5

## Current Focus

File in stable state: 1 axiom (R3k_exponential_lower from Ageron et al. 2021),
0 sorries, 11 theorems including R(3;1)=3, R(3;2)=6, monotonicity,
inductive upper bound, factorial upper bound. All small values PROVED
(not axiomatized). Single remaining axiom is the deep cited Schur-number
construction.

## Active Approach

Path to eliminate the remaining axiom: doubling construction
R(3;k+1) ≥ 2·R(3;k) - 1, giving R(3;k) ≥ 2^k + 1 by induction. Suffices
for the ∃ c > 1 existential statement (with c = 2).

## Blockers

None — doubling construction is provable but ~150 lines of Lean.

## Next Action

Add `forces_mono` lemma (vertex monotonicity for ForcesMonochromaticTriangle)
as building block. Follow-up session: full doubling construction to
eliminate the last axiom.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: pigeonhole induction (Ramsey), explicit constructions
  (R(3,3)=6), monotonicity via castLE, factorial upper bound via induction
