# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 23 available, 562 in-progress, 1407 completed, 3 graduated

## Selected Problem

- **ID**: szemeredi-regularity-oq-02
- **Name**: Szemerédi Regularity: Frieze-Kannan Weak Regularity Comparison
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top composite score among eligible candidates**: Score 68 ((tractability 6 × 10) + significance 8). After excluding claimed problems (`erdos-476-oq-05-wip-01`, `triangle-angle-sum-oq-03`), the already-selected-in-this-batch group (`triangle-angle-sum-oq-02`, `liouville-theorem-oq-04`, `shapley-folkman-oq-03`, `solution-of-cubic-oq-05`), and yesterday's selection (`minkowski-fundamental-theorem-oq-04`), this is the highest-scoring unclaimed candidate.
2. **EMPTY knowledge tier**: No research has been accumulated on this specific problem yet — the workspace was initialized but no insights recorded. Immediate value in establishing first observations.
3. **Domain diversity**: Recent batch selections covered geometry, number theory, combinatorics, and algebra. Frieze-Kannan weak regularity is additive combinatorics / extremal graph theory — a distinct domain. The last 3 batch selections (liouville, shapley-folkman, solution-of-cubic) are all different domains, so no diversity penalty applies.

## Quality Gate

- Near-duplicate of recent completions? **No** — Frieze-Kannan weak regularity (exponential-size partitions, cut-norm approximation) is mathematically distinct from the full Szemerédi regularity formalization in the gallery.
- Shallow specialization? **No** — the Frieze-Kannan result (1999) is a substantive simplification with a genuinely different proof strategy; comparing it to full regularity in Lean 4 is a real research question.
- Significance >= 3? **Yes** (8/10)
- Last 3 same domain? **No** — passes diversity check.

## Rejection Summary

- **Candidates considered**: 16 (after filtering claimed and already-selected)
- **Candidates rejected**: 15
  - `newton-inductive-step-oq-03`, `ptolemys-complex-proof-oq-02`, `ptolemys-theorem-oq-01-oq-02`: composite score 67 — below top candidate; narrower mathematical scope
  - `fair-games-theorem-oq-02-oq-01-oq-01`: composite score 66 — lower significance (6/10)
  - `szemeredi-counting-oq-02`: composite score 58 — lower tractability; the counting step is harder to isolate than the regularity structure itself
  - `napoleons-theorem-oq-02`, `sylow-theorem-oq-02`: composite score 57 — tractability 5, below top group
  - `divisibility-truncation-general-oq-03`: composite score 56 — lower significance and tractability
  - `szemeredi-full-oq-01`, `isoperimetric-theorem-oq-03`, `hurwitz-theorem-oq-04`: composite score 48-49 — tractability 4
  - `szemeredi-full-oq-02`: composite score 38 — tractability 3
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: composite score 27-28 — tractability 2; open conjectures without clear Lean formalization path
- **Confidence**: high (8-point gap between #1 and #2)

## Related Gallery Proofs

- `szemeredi-regularity`: The full Szemerédi regularity lemma — this oq-02 investigates whether Frieze-Kannan is a simpler alternative or stepping stone
- `szemeredi-theorem`: The density theorem — Frieze-Kannan weak regularity can be used for some applications of the full regularity lemma
- `szemeredi-core`: Core definitions and shared infrastructure relevant to all Szemerédi variants

## Suggested First Steps

1. **OBSERVE**: Survey Mathlib for existing `cutNorm` or `Finpartition` API — determine what's already formalized vs what must be defined from scratch
2. **ORIENT**: Read the Frieze-Kannan 1999 paper statement and compare to the full regularity lemma statement in the gallery `szemeredi-regularity` proof
3. **DECIDE**: Determine whether to (a) define `cutNorm` and prove weak regularity independently, (b) derive Frieze-Kannan as a corollary of full regularity, or (c) formalize a comparison lemma showing one implies the other up to constants

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 23 |
| In Progress | 562 |
| Completed | 1407 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

Pool has 23 available problems against a threshold of 15 — **adequate**.

- Pool depth: adequate (23 available, 53% above threshold)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Next refresh recommended: when available count drops below 20
