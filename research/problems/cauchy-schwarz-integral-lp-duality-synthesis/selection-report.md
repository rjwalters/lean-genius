# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT
**Pool Status**: 15 available (at threshold), 557 in-progress, 1420 completed

## Selected Problem

- **ID**: cauchy-schwarz-integral-lp-duality-synthesis
- **Name**: Synthesis: Eliminate riesz_lp_surjective axiom — Full Lp Duality
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 9/10
- **Knowledge Score**: 0 (EMPTY — synthesis task, no prior research needed)
- **Status**: available
- **Composite Score**: 98 = (0 × 1000) + (9 × 10) + 8

## Selection Rationale

1. **Highest composite score (98)** among all valid candidates. EMPTY knowledge
   tier combined with the highest tractability in the pool (9/10) makes this
   the top-ranked problem by the selection algorithm.

2. **Synthesis / axiom-elimination type**: The lean-synthesis agent identified on
   2026-04-23 that `riesz_lp_surjective_from_rn` in `OQ01OQ01OQ02OQ01.lean`
   proves exactly the statement axiomatized in the parent `OQ01OQ01OQ02.lean`.
   No mathematical discovery is needed — the proof exists; only wiring is required.

3. **Domain diversity**: Functional analysis / Lp spaces has not been featured in
   the last 5 seeker selections (recent: algebra, combinatorics, combinatorics,
   geometry, number theory).

4. **Quality improvement**: Upgrading `cauchy-schwarz-integral-oq-01-oq-01-oq-02`
   from `axiomatized` to `verified` (axiomCount 1 → 0) directly improves gallery
   quality and closes an open axiom gap in the Lp duality chain.

5. **First dedicated selection**: This synthesis problem was proposed by the
   lean-synthesis agent but had not yet been featured as a dedicated seeker
   selection with a workspace.

## Quality Gate Assessment

- Not a duplicate: synthesis tasks are uniquely typed, different from all gallery proofs
- Not a moonshot: tractability 9/10 (highest in pool)
- Significance 8 > 3 (passes minimum threshold)
- Domain diversity: functional analysis is fresh vs recent selections
- Result: **PASS**

## Rejection Summary

- **Candidates considered**: 15 in .lean/state pool (at threshold)
- **Moonshots rejected**: twin-primes-special-oq-01, weak-goldbach-oq-01,
  sophie-germain-oq-01 (tractability ≤ 2)
- **Selected today (excluded)**: abel-ruffini-galois-extensions-oq-04,
  erdos-1155-oq-02, derangements-convergence-oq-03, ptolemys-theorem-oq-01-oq-02
- **Already claimed**: dissection-of-cubes-oq-04, erdos-1155-oq-02
- **Confidence**: High (composite score 98 >> next-best 67, clear separation)

## Related Gallery Proofs

- `cauchy-schwarz-integral-oq-01-oq-01-oq-02`: Parent proof (contains the axiom to replace)
- `cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01`: Child proof (contains the theorem)
- `cauchy-schwarz-integral`: Root Cauchy-Schwarz formalization

## Suggested First Steps

1. **OBSERVE**: Read `CauchySchwarzIntegralOQ01OQ01OQ02.lean` to find the
   `riesz_lp_surjective` axiom; read `...OQ01.lean` to confirm
   `riesz_lp_surjective_from_rn` has the same type signature.
2. **ORIENT**: Verify type signatures match exactly — if they differ slightly,
   check whether a `have` or wrapper can bridge them.
3. **DECIDE → ACT**: Add import, replace axiom with theorem, run docker build,
   update meta.json. Create PR with label `research`.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 16 (was 15) |
| In Progress | 557 |
| Completed | 1420 |
| Graduated | 9 |
| Blocked | 3 |
| Surveyed | 1 |

## Candidate Pool Health

- **Pool depth**: At threshold (15 → 16 with this selection)
- **Note**: 2 of the 15 listed as "available" have active researcher claims
  (dissection-of-cubes-oq-04, erdos-1155-oq-02) — effective unclaimed: ~14
- **Recommendation**: Pool is healthy. Several A-tier tractable problems await researchers.
- **Next refresh**: In 30 minutes
