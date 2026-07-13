# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 60 available, 559 in-progress, 1405 completed, 3 graduated

## Selected Problem

- **ID**: shapley-folkman-oq-03
- **Name**: Shapley-Folkman Theorem: Economic Application Formalization (Starr Norm Bound)
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 EMPTY (structured items); knowledge.md has preliminary research notes
- **Status**: available

## Selection Rationale

1. **Top composite score among eligible candidates**: Score 67 ((tractability 6 × 10) + significance 7). After excluding claimed problems (`erdos-476-oq-05-wip-01`, `triangle-angle-sum-oq-03`), today's batch selections (`triangle-angle-sum-oq-02`, `liouville-theorem-oq-04`, `szemeredi-regularity-oq-02`, `isoperimetric-theorem-oq-03`, `shannon-channel-coding-oq-02-oq-04`), and recent 7-day selections (`sqrt2-minpoly-oq-02`, `solution-of-cubic-oq-05`, `minkowski-fundamental-theorem-oq-04`), this ties for the highest score with several others.
2. **Domain diversity tiebreaker**: Tied candidates include geometry (Ptolemy variants — excluded: geometry over-selected today), q-combinatorics (Newton — overlaps with combinatorics, heavily selected). Economics/optimization has zero coverage this week — completely fresh domain.
3. **Well-scoped corollary with existing infrastructure**: The `knowledge.md` shows the parent `ShapleyFolkman.lean` (814 lines) already formalizes the counting bound (`sum_close_to_convexHull`). OQ-03 asks for the metric/norm bound (Starr 1969, Lemma 1): `‖z - z*‖ ≤ √d · max_i diam(co(Aᵢ) \ Aᵢ)`. This is a well-defined corollary, not speculative research.
4. **No blocker**: The 1 remaining sorry in the parent proof (Case B WF descent, line 704) does not block the Starr bound path — it's a separate lemma. The Starr bound can be proved using `sum_close_to_convexHull` as a black box.

## Quality Gate

- Near-duplicate of recent completions? **No** — the Starr norm bound (metric version) is mathematically distinct from the core counting lemma in the gallery.
- Shallow specialization? **No** — converting counting ≤ d non-convex components to a metric bound `‖z - z*‖ ≤ √d · diam` requires non-trivial functional analysis infrastructure (inner product space norms, diameter of convex hull, Cauchy-Schwarz).
- One-off example check? **No** — theory-level; results extend to any finite-dimensional inner product space.
- Significance >= 3? **Yes** (7/10)
- Last 3 same domain? **No** — economics/optimization has no recent selections.

## Rejection Summary

- **Candidates considered**: 14 (after filtering claimed, today's batch, and 7-day near-duplicates)
- **Candidates rejected**: 13
  - `newton-inductive-step-oq-03`, `ptolemys-complex-proof-oq-02`, `ptolemys-theorem-oq-01-oq-02`: composite 67, equal — rejected on domain diversity (geometry, q-combinatorics already covered recently)
  - `fair-games-theorem-oq-02-oq-01-oq-01`: composite 66 — lower significance (6/10)
  - `szemeredi-counting-oq-02`: composite 58 — tractability 5; Szemeredi domain over-selected (31 times in 7 days)
  - `napoleons-theorem-oq-02`, `sylow-theorem-oq-02`: composite 57 — tractability 5
  - `divisibility-truncation-general-oq-03`: composite 56 — significance 6/10
  - `hurwitz-theorem-oq-04`: composite 47 — tractability 4; Lie group connection speculative
  - `szemeredi-full-oq-01`, `szemeredi-full-oq-02`: composite 38-49 — Szemeredi over-selected + low tractability
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: composite 27-28 — tractability 2; open conjectures
  - `sperner-ndim-oq-02`: prior research found `boundary_doors_odd` claim is FALSE — architectural fix needed first
  - `sperner-ndim-oq-04` (RICH 19 items), `lebesgue-measure-oq-06` (RICH 27 items): deprioritized by knowledge tier
- **Confidence**: medium (3-way tie resolved by diversity tiebreaker)

## Related Gallery Proofs

- `shapley-folkman`: Parent proof (1 sorry remaining in Case B) — provides `sum_close_to_convexHull` needed as the counting backbone
- `minkowski-fundamental-theorem`: Minkowski sum and lattice infrastructure
- `caratheodory-theorem`: Carathéodory decomposition underlies the counting lemma

## Suggested First Steps

1. **OBSERVE**: Audit Mathlib's `InnerProductSpace` API for `inner_mul_le_norm_mul_norm` (Cauchy-Schwarz) and `Metric.diam_convexHull` bounds — the Starr bound proof will need these
2. **ORIENT**: Read `ShapleyFolkman.lean` `sum_close_to_convexHull` theorem interface — determine the exact API for extracting the ≤d component bound and converting to a norm bound
3. **DECIDE**: Choose between formalizing the full Starr bound statement or a simplified version: `∃ y ∈ ∑ i, S i, ‖x - y‖ ≤ √(finrank ℝ E) * max_i diam (convexHull (S i))`

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 60 |
| In Progress | 559 |
| Completed | 1405 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

Pool has 60 available problems against a threshold of 15 — **healthy**.

- Pool depth: adequate (60 available, 4× above threshold)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Next refresh recommended: when available count drops below 20
