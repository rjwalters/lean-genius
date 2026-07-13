# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 34 available, 559 in-progress, 1403 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: ballot-problem-oq-03-oq-01-oq-01-oq-01
- **Name**: LGV Lemma: Jacobi-Trudi Identity — Schur Polynomials as Determinants
- **Tier**: B
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available (newly registered)

## Selection Rationale

1. **EMPTY knowledge tier** — no prior research; highest-priority tier in ranking algorithm
2. **Algebraic combinatorics** — domain not recently selected on this branch (recent
   selections: analysis, geometry, number theory, calculus, convex analysis, graph theory)
3. **Gallery infrastructure exists** — parent proof `ballot-problem-oq-03-oq-01` (LGV
   lemma) provides the exact building block needed for the Jacobi-Trudi combinatorial proof
4. **Composite score 68** = 0 (EMPTY tier) + (6 × 10) + 8 = 68, third-highest among
   newly-added fresh candidates
5. **Genuine Mathlib gap** — `MvPolynomial.schurPolynomial` exists but Jacobi-Trudi is
   unlikely to have a formalized proof; this could be a real Mathlib contribution

## Rejection Summary

- **Candidates considered**: 34 available (32 prior + 2 newly added)
- **Candidates rejected**: moonshots (sophie-germain, twin-primes, weak-goldbach: tract≤2),
  claimed problems (sperner-ndim-oq-04, solution-of-cubic-oq-05, fourier-series-oq-02-oq-02,
  erdos-476-oq-05-wip-01), recently-completed sqrt2-minpoly-oq-02 (PR #11766)
- **Confidence**: medium (composite=68 is solid but not dramatically higher than alternatives)

## Related Gallery Proofs

- `ballot-problem-oq-03-oq-01`: LGV lemma — direct dependency, provides path determinant formula
- `ballot-problem-oq-03-oq-01-oq-02`: LGV applied to Catalan numbers — technique reference

## Suggested First Steps

1. **OBSERVE**: Check Mathlib for `MvPolynomial.schurPolynomial` and SSYT formalization;
   read `ballot-problem-oq-03-oq-01.lean` to understand the LGV API
2. **ORIENT**: Confirm whether SSYT ↔ NI-path bijection has infrastructure in Mathlib or
   gallery; identify the minimal new definitions needed
3. **DECIDE**: Choose between direct LGV application (requires SSYT bijection) vs.
   algebraic approach via transfer matrix (avoids bijection, more abstract)

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 34 |
| In Progress | 559 |
| Completed | 1403 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

- **Pool depth**: adequate (34 available, above threshold of 15)
- **Recommendation**: Pool healthy — 2 new problems added this cycle from gallery extract
- **Next refresh**: standard 30-minute interval

## Initialized

- [x] Research workspace created
- [x] problem.md populated
- [ ] Ready for /researcher
