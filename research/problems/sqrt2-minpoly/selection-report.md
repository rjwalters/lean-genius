# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 25 available, 560 in-progress, 1405 completed, 3 graduated, 3 blocked

## Selected Problem

- **ID**: sqrt2-minpoly
- **Name**: Minimal Polynomial of √2 over ℚ
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 8/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among unclaimed candidates (86)**: Tractability 8/10 is
   excellent for autonomous Lean research. All 25 available problems have EMPTY knowledge
   tiers (score 0), so composite reduces to `(tractability × 10) + significance`. Score 86
   is 9 points above the next-best unclaimed candidate (minkowski at 77).

2. **EMPTY knowledge tier**: No prior research accumulated in this workspace — fresh
   territory. The problem was initialized in OBSERVE phase today (2026-04-22T19:23:25+02:00)
   with 0 attempts and no knowledge entries.

3. **Natural bridge in the √2 family**: The gallery has `sqrt2-irrational` (irrationality of √2),
   `sqrt2-from-axioms` (axiom-level), and `sqrt2-plus-sqrt3-irrational` (the parent). The
   minimal polynomial result provides the algebraic structure that explains *why* √2 is
   irrational and sets up the degree-2 extension ℚ(√2)/ℚ. It bridges irrationality proofs
   to field extension theory.

4. **Strong Mathlib API coverage**: `Polynomial.minpoly`, `Polynomial.Irreducible`,
   `Real.sqrt`, and `Polynomial.aeval` are all mature Mathlib APIs. The key steps — showing
   X²-2 vanishes at √2, showing it is irreducible by rational root theorem, and invoking
   minimality — have well-supported Lean tactics. High tractability reflects this.

5. **Domain diversity**: The last 3 seeker selections were shapley-folkman (economics/
   combinatorics), newton-inductive-step (q-binomials/algebra), and napoleons-theorem
   (geometry). Algebraic number theory is underrepresented; no diversity penalty applies.

## Ranking Summary (top candidates, all EMPTY tier)

| ID | Sig | Tract | Composite | Notes |
|----|-----|-------|-----------|-------|
| sqrt2-plus-sqrt3-irrational-oq-03 | 6 | 9 | 96 | CLAIMED — active lock |
| **sqrt2-minpoly** | **6** | **8** | **86** | **SELECTED** |
| minkowski-fundamental-theorem-oq-04 | 7 | 7 | 77 | Runner-up |
| triangle-angle-sum-oq-03 | 6 | 7 | 76 | Recently selected |
| sperner-ndim-oq-02 | 8 | 6 | 68 | A-tier open question |
| szemeredi-regularity-oq-02 | 8 | 6 | 68 | A-tier open question |
| triangle-angle-sum-oq-02 | 8 | 6 | 68 | A-tier open question |
| erdos-476-oq-05-wip-01 | 7 | 6 | 67 | Tractability drops 1 |
| newton-inductive-step-oq-03 | 7 | 6 | 67 | Recently selected |
| shapley-folkman-oq-03 | 7 | 6 | 67 | Recently selected |
| solution-of-cubic-oq-05 | 7 | 6 | 67 | Tractability drops 1 |

Note: `sqrt2-minpoly` appeared as "completed" in `.lean/state/candidate-pool.json` (stale
sync) but shows `available` in the database (`research/db/knowledge.db`). The database
is the source of truth; the pool file lags awaiting deployer sync.

## Rejection Summary

- **Candidates considered**: 26 (25 from pool + 1 corrected from database)
- **Candidates rejected**: 25
  - `sqrt2-plus-sqrt3-irrational-oq-03` (score 96): active claim exists — not available
  - `minkowski-fundamental-theorem-oq-04` (score 77): 9-point gap behind; outranked
  - `triangle-angle-sum-oq-03` (score 76): recently selected (5th-most-recent commit)
  - A-tier open conjectures (szemeredi, twin-primes, weak-goldbach, sophie-germain):
    all have tractability ≤ 6; composite scores ≤ 68; unsuitable for autonomous research
  - All remaining B/C tier: lower composite scores, outranked by `sqrt2-minpoly`
- **Confidence**: high — 9-point gap between selected (86) and runner-up (77)

## Related Gallery Proofs

- `sqrt2-irrational`: Parent irrationality proof — states √2 ∉ ℚ. The minimal polynomial
  proof provides the algebraic structure behind the irrationality result.
- `sqrt2-plus-sqrt3-irrational`: Gallery entry for √2+√3; spawned `oq-03` (the degree-4
  minimal polynomial result over ℚ). This selection is the degree-2 analogue.
- `cayley-hamilton-minpoly`: General minimal polynomial theory (Cayley-Hamilton, rational
  canonical form). Contains reusable Lean lemmas about `Polynomial.minpoly`.
- `sqrt2-from-axioms`: Axiom-based construction of √2 — relevant API context.

## Suggested First Steps

1. **OBSERVE**: Check `Mathlib.RingTheory.Algebraic.Basic` for `minpoly` API.
   Key: `Polynomial.minpoly.dvd`, `Polynomial.minpoly.irreducible`, `Polynomial.minpoly.eq_X_pow_sub_C_of_isSplittingField`.
   Also check if `Polynomial.minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2` is already in Mathlib.

2. **ORIENT**: Survey `proofs/Proofs/Sqrt2PlusSqrt3Irrational.lean` for the degree-4
   minimal polynomial technique. The degree-2 case is simpler and the same API applies.
   Check `cayley-hamilton-minpoly` lemmas for reusable `minpoly` infrastructure.

3. **DECIDE**: Primary approach — use `Polynomial.minpoly.unique` or prove directly:
   (a) Show `aeval (Real.sqrt 2) (X^2 - C 2) = 0` (root verification)
   (b) Show `X^2 - C 2` is irreducible over ℚ (rational root theorem, degree 2)
   (c) Conclude via minimality. Alternative: check if `Irreducible (X^2 - C (2:ℚ))`
   is already available via `Polynomial.irreducible_of_eisenstein_criterion`.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 25 |
| In Progress | 561 |
| Completed | 1404 |
| Graduated | 3 |
| Blocked | 1 |
| **Total** | **1994** |

## Candidate Pool Health

Pool has 25 available problems — above the 15-problem minimum threshold.

- **Pool depth**: adequate (25 available vs. 15 threshold)
- **Recommendation**: Pool healthy; recent seeker activity (5 selections in recent runs)
  has built good depth across tractability tiers
- **Next refresh recommended**: When available count drops below 15; current mix includes
  tractable B-tier problems and aspirational A-tier problems
