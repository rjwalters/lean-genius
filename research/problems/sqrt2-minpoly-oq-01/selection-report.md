# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 28 available, 559 in-progress, 1405 completed, 3 graduated

## Selected Problem

- **ID**: sqrt2-minpoly-oq-01
- **Name**: Minimal Polynomial of √n over ℚ: Eisenstein Generalization
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 9/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score of all unselected available problems**: Score 97 (tractability 9 × 10 + significance 7). Top-ranked problem after excluding active claims, open conjectures with tractability ≤ 2, RICH knowledge problems, and the last 5 seeker-selected problems.
2. **Extremely high tractability (9/10)**: The problem is a direct parameterization of the existing gallery proof `sqrt2-minpoly` (n=2 case). The proof strategy — Eisenstein at a prime p with p|n, p²∤n — is fully specified. All required Mathlib infrastructure exists: `Polynomial.irreducible_of_eisenstein_criterion`, `minpoly.unique`, `Real.sqrt_sq`.
3. **Domain diversity**: Algebraic number theory has had limited recent coverage. Most recent 3 selections span economics (shapley-folkman), information theory (shannon), and geometry (isoperimetric) — algebraic number theory is fresh.
4. **Clear quality**: Not an open conjecture, not a shallow notation variant. The result is parametric over all non-perfect-square integers — theory-level with natural Mathlib PR potential.

## Quality Gate

- Near-duplicate of recent completions? **No** — `sqrt2-minpoly-oq-02` (k-th roots) was recently selected but is NOT completed; and oq-01 (square roots of n) is distinct in scope from oq-02 (k-th roots of n). Different generalization directions.
- Shallow specialization? **No** — `minpoly ℚ (√n) = X²-n` for arbitrary non-square n covers all square-free integers; the gallery only has n=2.
- One-off example check? **No** — parametric over infinitely many inputs.
- Significance ≥ 3? **Yes** (7/10).
- Last 3 selections same domain? **No** — recent: economics, information theory, geometry.

## Rejection Summary

- **Candidates considered**: 28 available
- **Active claims excluded**: 2 (`erdos-476-oq-05-wip-01`, `triangle-angle-sum-oq-03`)
- **Open conjectures rejected (tractability ≤ 2)**: 3 (`sophie-germain-oq-01`, `twin-primes-special-oq-01`, `weak-goldbach-oq-01`)
- **RICH knowledge (lower priority)**: 2 (`lebesgue-measure-oq-06` score 27, `sperner-ndim-oq-04` score 19)
- **Recently seeker-selected**: 5 (chinese-remainder, shapley-folkman, shannon, isoperimetric, szemeredi-regularity)
- **Confidence**: high — score spread between this candidate (97) and next-best (88 for sqrt2-minpoly-oq-02, domain-adjacent) or 68 for others is large.

## Related Gallery Proofs

- `sqrt2-minpoly`: Direct parent — proves the n=2 case using Eisenstein at p=2
- `sqrt2-irrational`: Alternate irrationality proof via divisibility
- `sqrt2-plus-sqrt3-irrational`: Related irrationality result via field extension degree
- `algebraic-numbers-countable`: Context for minimal polynomial degree arguments

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/Sqrt2MinPoly.lean` — map the n=2 proof structure and identify which Mathlib lemmas were used for Eisenstein application.
2. **ORIENT**: Scout for `Nat.minFac` and related prime factoring lemmas to extract a prime p with p|n and p²∤n from the non-square hypothesis `¬ IsSquare n`.
3. **DECIDE**: Draft the main theorem with `sorry`s for sub-lemmas: (a) prime witness existence, (b) Eisenstein application, (c) conclusion via `minpoly.unique`.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 28 |
| In Progress | 559 |
| Completed | 1405 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

- Pool depth: **adequate** (28 available, well above threshold of 15)
- Recommendation: Pool healthy; no refresh needed this cycle.
- Next refresh recommended: When available count drops below 15.
