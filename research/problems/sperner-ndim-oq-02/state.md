# Research State: sperner-ndim-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-04-23T00:00:00Z
**Iteration**: 2

## Current Focus

Architecture decision and approach implementation. Previous session (2026-04-22) discovered
`boundary_doors_odd` is **false as stated** due to oriented vs unoriented simplex issue.
Recommendation: Option C — define `SpernerTriangulation` instance for Freudenthal grid
using unoriented simplices, apply abstract `SpernerNDim.sperner`.

## Active Approach

**Option C: SpernerTriangulation instance**
- Define `FreudenthalComplex d N` with unoriented simplices (vertex sets)
- Prove the three `SpernerTriangulation` axioms
- Apply `SpernerNDim.sperner`

## Attempt Count
- Total attempts: 1 (prior analysis session, no proof code written)
- Current approach attempts: 0
- Approaches tried: 1 (analysis revealed Option A/B/C)

## Blockers
None (architectural path is clear from knowledge.md).

## Next Action

1. Read `proofs/Proofs/SpernerNDim.lean` — understand `SpernerTriangulation` structure definition
2. Read `proofs/Proofs/SpernerGrid.lean` — understand existing `Vertex`, `GridSimplex`, adjacency
3. Define unoriented Freudenthal simplex type (as `Finset (Vertex d N)`)
4. Verify `SpernerTriangulation` axioms are provable for this type
5. Write the companion `SpernerNDimFreudenthal.lean` or extend `SpernerGrid.lean`
