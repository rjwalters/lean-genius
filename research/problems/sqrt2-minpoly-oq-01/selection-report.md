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

1. **Highest composite score in pool**: Score 97 ((tractability 9 × 10) + significance 7) — no other available candidate comes close. The next best eligible candidates (newton-inductive-step-oq-03, fair-games-theorem-oq-02-oq-01-oq-01) score 66-67, a 30+ point gap. This is the clear top pick by the algorithm.
2. **Knowledge tier EMPTY, not previously seeker-selected**: Despite the workspace being initialized, no seeker selection commit exists for this problem. The knowledge.md is boilerplate-only (21 lines, 0 knowledge items), meaning no research has actually been conducted.
3. **Highly tractable, well-scoped generalization**: The n=2 case (`minpoly ℚ (√2) = X² - 2`) is already proven in `proofs/Proofs/Sqrt2MinPoly.lean`. The general case requires only: (a) finding a prime p | n with p² ∤ n (exists since n is non-square), (b) applying `Polynomial.irreducible_of_eisenstein_criterion` at p — the same lemma used in the parent proof. No new mathematical ideas needed, only parameterization.
4. **Domain diversity**: Last 3 seeker selections were economics/optimization (shapley-folkman), geometry (isoperimetric), and combinatorics (szemeredi-regularity). Algebraic number theory has had no coverage in recent cycles. No domain penalty applies.
5. **Mathlib PR candidate**: A general `minpoly_sqrt_n` theorem is natural and reusable. This increases the significance of the work beyond the gallery entry itself.

## Quality Gate

- Near-duplicate of recent completions? **No** — `sqrt2-minpoly-oq-02` (k-th roots) was selected 7 days ago but not completed. oq-01 (square roots) is a distinct sibling: different Lean statement, different edge case analysis (non-perfect-square vs. k-th root irreducibility). Not the same problem.
- Shallow specialization? **No** — generalizing from n=2 to all non-square n requires parameterizing the prime selection machinery; `Nat.minFac` or a custom prime witness must be used and bridged to Eisenstein. This is substantive Lean formalization work.
- One-off example check? **No** — the theorem is universal over all positive non-square integers; directly reusable.
- Significance ≥ 3? **Yes** (7/10)
- Last 3 same domain? **No** — algebraic number theory; completely fresh relative to recent selections.

## Rejection Summary

- **Candidates considered**: 22 (all available, minus claimed)
- **Candidates rejected**: 21
  - `erdos-476-oq-05-wip-01`, `triangle-angle-sum-oq-03`: **claimed** — currently locked
  - `shapley-folkman-oq-03`, `isoperimetric-theorem-oq-03`, `szemeredi-regularity-oq-02`, `triangle-angle-sum-oq-02`: **selected in this batch** — already committed this session
  - `sqrt2-minpoly-oq-02`, `solution-of-cubic-oq-05`, `minkowski-fundamental-theorem-oq-04`: **recent 7-day selections** — avoid within 7 days per diversity policy
  - `sperner-ndim-oq-02`: **architectural block** — `boundary_doors_odd` proved false; workspace needs redesign before fresh research
  - `lebesgue-measure-oq-06` (score 27, RICH), `sperner-ndim-oq-04` (score 19, RICH): **knowledge-tier penalty** (composite ≈ -2932); only revisit if new approach identified
  - `napoleons-theorem-oq-02`, `ptolemys-complex-proof-oq-02`, `ptolemys-theorem-oq-01-oq-02`, `triangle-angle-sum-oq-03` (claimed): **geometry domain penalty** — 2 of last 3 selections were geometry; avoid same domain
  - `szemeredi-counting-oq-02`, `szemeredi-full-oq-01`, `szemeredi-full-oq-02`: **Szemerédi domain over-selected** (31 selections in last 7 days) — significant penalty
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: **intractable open conjectures** (tractability 2) — no realistic Lean path
  - `hurwitz-theorem-oq-04`: **speculative connections** (Lie group theory); tractability 4, sig 7 → composite 47
  - `liouville-theorem-oq-04`: tractability 4 → composite 47; p-adic extensions require more Mathlib infrastructure
  - `newton-inductive-step-oq-03`, `fair-games-theorem-oq-02-oq-01-oq-01`, `sylow-theorem-oq-02`, `divisibility-truncation-general-oq-03`: scores 56-67 — all well below sqrt2-minpoly-oq-01's 97
- **Confidence**: **high** — 30+ point gap between top candidate and next eligible; no tiebreaker needed

## Related Gallery Proofs

- `sqrt2-minpoly`: Direct parent proof — proves n=2 case; this is the verbatim template to generalize
- `sqrt2-irrational`: Alternate irrationality proof via divisibility; Eisenstein approach is cleaner
- `sqrt2-plus-sqrt3-irrational`: Field extension degree argument; related infrastructure
- `algebraic-numbers-countable`: Uses `minpoly` degree bounds; shares API surface

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/Sqrt2MinPoly.lean` in full — identify the exact Eisenstein invocation and `minpoly` API calls used for n=2. Document the proof structure in knowledge.md.
2. **ORIENT**: Search Mathlib for `Polynomial.irreducible_of_eisenstein_criterion` (in `Mathlib.RingTheory.Eisenstein.Basic`) and `minpoly.unique` — confirm argument signatures. Check if `Real.sqrt_sq` handles the `(sqrt n)^2 = n` step for general n.
3. **DECIDE**: Choose between (a) direct Eisenstein parameterization over a prime p | n, p² ∤ n using `Nat.minFac` as the prime witness, or (b) using `minpoly.eq_of_irreducible_of_monic` with irrationality derived first. Approach (a) is more direct.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 28 |
| In Progress | 559 |
| Completed | 1405 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

Pool has 28 available problems against a threshold of 15 — **healthy**.

- Pool depth: adequate (28 available, 87% above threshold)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Next refresh recommended: when available count drops below 20
