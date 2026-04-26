# Current State

**Phase**: COMPLETED
**Since**: 2026-04-26T00:00:00+00:00
**Iteration**: 2

## Current Focus

WIP04 written and build running. Axiom-free proof of general nonderogatory cyclic vector theorem
via primary decomposition. Eliminates the `nonderogatory_similar_to_companion` axiom from WIP01.

## Active Approach

Primary decomposition via Bezout projections:
1. For each prime power factor p_i^{e_i}, construct v_i = F_i(M)w_i (F_i = complementary product)
2. Combine as v = sum v_i
3. Extract r(M)v_i = 0 via CRT/Bezout projection
4. Apply WIP03's pow_irred_dvd_of_annihilated to get p_i^{e_i} | r
5. Apply Finset.prod_dvd_of_coprime to get minpoly | r, contradicting deg(r) < n

## Result

**WIP04**: `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean`
- 352 lines, 0 sorries, 0 axioms (pending build verification)
- Namespace: `GeneralCyclicVector`
- Main theorem: `nonderogatory_general_has_cyclic_vector`

## Blockers

RESOLVED: No PID structure theorem needed.
Remaining: To eliminate factored-form hypothesis, need UFD factorization of minpoly K M.

## Next Action

After build passes:
1. Commit, push, create PR
2. Follow-up: generalize to eliminate factored-form input hypothesis

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (primary decomposition via Bezout projections — SUCCESS)
