# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 26 available, 558 in-progress, 1408 completed, 3 graduated, 1 blocked

## Selected Problem

- **ID**: solution-of-cubic-oq-05
- **Name**: Solution of the Cubic: Connection to Quartic via Resolvent Cubic
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Composite score 67** — tied for highest among fresh candidates (no prior selection
   report). All available problems have EMPTY knowledge tier (score=0 in JSON registry),
   so ranking reduces to `(tractability × 10) + significance`.

2. **Concrete cross-proof connection** — the resolvent cubic provides a precise algebraic
   bridge between two existing gallery proofs: `SolutionOfCubic.lean` (Wiedijk #37) and
   `GeneralQuartic.lean` (Wiedijk #46). The theorem statement is already specified in the
   workspace; the first step is clear.

3. **Tractability 6/10** — the resolvent cubic identity is a polynomial algebra fact that
   Lean's `ring` tactic and `Polynomial.eval` API can handle. No deep Mathlib gaps
   expected for the algebraic manipulation layer.

4. **Domain diversity** — algebra (polynomial theory) is underrepresented in the
   current fresh-selection batch. Recent selections cover analysis, number theory, graph
   theory, Szemerédi, and sqrt2-minimal-polynomials. This adds a new direction.

## Rejection Summary

- **Candidates considered**: 26 available problems
- **Candidates rejected (moonshot, tract ≤ 2)**: weak-goldbach-oq-01, twin-primes-special-oq-01, sophie-germain-oq-01 — tractability too low for autonomous research
- **Candidates rejected (diversity — Szemerédi saturation)**: szemeredi-full-oq-01, szemeredi-full-oq-02, szemeredi-counting-oq-02, szemeredi-regularity-oq-02
- **Candidates rejected (active claim)**: erdos-476-oq-05-wip-01
- **Candidates already selected (have prior report)**: sperner-ndim-oq-02, minkowski-fundamental-theorem-oq-04, and 14 others from the 2026-04-23 batch
- **Confidence**: medium (three candidates tied at score=67; domain diversity tiebreak)

## Related Gallery Proofs

- `solution-of-cubic`: The parent Cardano cubic proof — provides `cardano_formula_is_root`
- `general-quartic`: Ferrari quartic formalization — provides `ferrari_factorization` and
  `resolventCubic` definition; the connection theorem bridges these two files directly

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/SolutionOfCubic.lean` and `proofs/Proofs/GeneralQuartic.lean`
   to understand the current API surface. Find `cardano_formula_is_root` and
   `GeneralQuartic.resolventCubic`.

2. **ORIENT**: Verify that `GeneralQuartic.resolventCubic` is defined as a `Polynomial ℂ`
   and that `Polynomial.eval` works cleanly. Check whether `ring` tactic can close the
   polynomial identity for the factorization equation.

3. **DECIDE**: Draft `quartic_factors_given_resolvent_root` — start with the depressed
   quartic case (`q = 0`), prove the factorization identity symbolically, then generalize.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 26 |
| In Progress | 558 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

- Pool depth: **adequate** (26 available, threshold=15)
- Domain coverage: algebra, combinatorics/algebra, geometry being added this cycle
- Recommendation: Pool healthy; no gallery refresh needed
- Next refresh recommended: next scheduled cycle (~30 min)

## Initialized

- [x] Research workspace exists (`research/problems/solution-of-cubic-oq-05/`)
- [x] problem.md populated
- [x] state.md: OBSERVE phase
- [x] Ready for /researcher
