# Research State: cayley-hamilton-cyclic-vector-all-fields

## Current State
**Phase**: COMPLETED (axiom-free pending one routine sorry)
**Path**: full
**Since**: 2026-04-27 (PR #13041 axiom elimination)
**Iteration**: 2

## Current Focus
Gallery file `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean` is V2 axiom-free:
0 axioms, 1 routine sorry (`monic_factored_form`, UFM API navigation, ~50 lines, Aristotle-suitable).
Mathematical content is fully verified via WIP04 primary decomposition.

## Active Approach
V2: Route through WIP04's `GeneralCyclicVector.nonderogatory_general_has_cyclic_vector`
(primary decomposition + Bezout/CRT). The single remaining sorry is purely Mathlib API.

## Attempt Count
- Total attempts: 2 (V1 axiomatized, V2 axiom eliminated)
- Approaches tried: V1 Route B (axiom), V2 primary decomposition (axiom-free modulo routine sorry)

## Blockers
None mathematical. The remaining sorry is routine UFM API.

## Next Action
Submit `monic_factored_form` to Aristotle (routine UFM API, ~50 lines). Closing it
brings the file to 0 sorries / 0 axioms.
