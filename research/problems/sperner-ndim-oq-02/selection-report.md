# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 28 available, 559 in-progress, 1405 completed, 3 graduated, 1 blocked

## Selected Problem

- **ID**: sperner-ndim-oq-02
- **Name**: n-Dimensional Sperner: Boundary-Door Oddness by Dimensional Induction
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY — existing knowledge.md has rich prior analysis)
- **Status**: available

## Selection Rationale

1. **Highest composite among truly fresh, unclaimed candidates**: After excluding
   `sqrt2-minpoly-oq-02` (near-topic duplicate of `sqrt2-minpoly-oq-01` selected this batch),
   `sperner-ndim-oq-02` leads at composite=68 (tractability 6×10 + significance 8).
2. **Rich prior analysis available**: The knowledge.md has a detailed session from 2026-04-22
   identifying that `boundary_doors_odd` is false as stated (orientation issue) and
   proposing three concrete fix options. The researcher starts ORIENT phase, not OBSERVE.
3. **Domain diversity**: Last 5 batch selections cover group theory, algebraic number theory,
   ring theory, convex geometry, information theory. This adds combinatorics/topology.
4. **Clear architectural path**: Option C (SpernerTriangulation instance for Freudenthal grid)
   is identified as cleanest, with specific Lean files and axioms to prove.

## Rejection Summary

- **Candidates considered**: 28 available
- **Excluded (claimed)**: erdos-476-oq-05-wip-01, triangle-angle-sum-oq-03 (2 problems)
- **Excluded (this-batch near-duplicate)**: sqrt2-minpoly-oq-02 (same Eisenstein/minimal-poly topic as oq-01 just selected)
- **Excluded (RICH knowledge tier)**: sperner-ndim-oq-04 (19 items), lebesgue-measure-oq-06 (27 items)
- **Excluded (moonshot tractability ≤ 2)**: sophie-germain-oq-01, twin-primes-special-oq-01, weak-goldbach-oq-01
- **Candidates rejected total**: 8
- **Confidence**: high (clear score gap: 68 vs 67 for second place, plus prior analysis advantage)

## Related Gallery Proofs

- `sperner-ndim`: Direct parent — the abstract `SpernerNDim.lean` is the infrastructure to use
- `sperner-ndim` (via `SpernerGrid.lean`): Contains the false `boundary_doors_odd` sorry
- `brouwer-fixed-point`: Downstream theorem this enables

## Suggested First Steps

1. **Read `SpernerTriangulation` definition** in `proofs/Proofs/SpernerNDim.lean` to understand
   the exact axioms needed for the instance
2. **Scout `SpernerGrid.lean`** for the `Vertex d N` and `GridSimplex` definitions —
   specifically understand the unoriented simplex structure `{v : Finset (Vertex d N) | ...}`
3. **DECIDE**: Write `SpernerNDimFreudenthal.lean` defining an unoriented `FreudenthalComplex`
   and prove it satisfies `SpernerTriangulation`; apply `SpernerNDim.sperner`

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 28 |
| In Progress | 559 |
| Completed | 1405 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

- **Pool depth**: adequate (28 available, well above threshold of 15)
- **Note**: 36 unmerged seeker branches suggest many prior selections awaiting deployer merge
- **Recommendation**: Pool healthy for now; monitor as deployers merge pending branches
- **Next refresh recommended**: Next 30-min cycle if available drops below 15
