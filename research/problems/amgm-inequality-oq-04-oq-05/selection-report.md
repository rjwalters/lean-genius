# Problem Selection Report

**Date**: 2026-04-26
**Mode**: SELECT (pool replenishment)
**Pool Status**: 15 available (at threshold), 558 in-progress, 1434 completed, 8 graduated, 4 blocked

## Selected Problem

- **ID**: `amgm-inequality-oq-04-oq-05`
- **Name**: Formalize Brent-Salamin Formula: π via AGM and Legendre's Relation
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 58
- **Status**: available (new addition)

## Selection Rationale

1. **Analysis domain underrepresented**: Current pool is heavy on number theory (Sophie
   Germain, Goldbach, Twin Primes, Erdős #1001) and combinatorics (Szemerédi). The
   Brent-Salamin formula adds a beautiful analysis/computational mathematics entry.

2. **Gallery chain completion**: The `amgm-inequality-oq-04` tree formalizes AGM
   convergence; this would crown the chain with the most famous application of AGM theory
   (the π formula). Direct continuation of existing formalization work.

3. **Historical and computational significance**: Salamin-Brent (1976) was a landmark
   algorithm. The formula is elegant and connects AGM, elliptic integrals, and π.

4. **EMPTY knowledge tier**: Fresh problem, no prior research notes. Ready for OBSERVE.

## Rejection Summary

- **Domain repetition avoided**: Not Erdős, Szemerédi, or Cayley-Hamilton family
- **Tractability filter**: Score 58 is above significance threshold (≥ 3)
- **Not claimed**: No active lock file
- **Confidence**: medium (clear selection rationale, but AGM prerequisites may be missing)

## Related Gallery Proofs

- `amgm-inequality-oq-04`: Parent — AGM iteration convergence, quadratic rates
- `amgm-inequality-oq-04-oq-02`: Legendre's relation (prerequisite to check)
- `amgm-inequality-oq-04-oq-03`: Gauss AGM theorem (prerequisite to check)

## Suggested First Steps

1. **OBSERVE**: Read `src/data/proofs/amgm-inequality-oq-04/` and sub-proofs oq-02, oq-03
   to understand what prerequisites are already formalized
2. **ORIENT**: Check Mathlib's `intervalIntegral` and `Analysis.SpecialFunctions` for
   K(k) (complete elliptic integral of the first kind) definitions
3. **DECIDE**: If oq-02 (Legendre) and oq-03 (Gauss AGM theorem) exist as proofs,
   assemble Brent-Salamin as a corollary. If not, document the prerequisite gap.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 18 |
| In Progress | 558 |
| Completed | 1434 |
| Graduated | 8 |
| Blocked | 4 |

## Initialized

- [x] Problem registered in `research/db/knowledge.db` (status: available)
- [x] Pool synced: `research/candidate-pool.json` updated (49 available)
- [x] Pool synced: `.lean/state/candidate-pool.json` updated (18 available)
- [x] Research workspace created: `research/problems/amgm-inequality-oq-04-oq-05/`
- [x] `problem.md` populated with formal statement, approaches, and references
- [x] `state.md` set to OBSERVE phase
- [x] Ready for /researcher
