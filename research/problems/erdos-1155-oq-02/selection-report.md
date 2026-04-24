# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT
**Pool Status**: 33 available, 558 in-progress, 1419 completed, 9 graduated

## Selected Problem

- **ID**: erdos-1155-oq-02
- **Name**: Erdős #1155 OQ2 — Limiting Distribution of f(n)/n^{3/2}
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge base, never seeker-selected**: This problem has no research history in this cycle and has not been formally selected before. All other EMPTY-knowledge candidates with higher composite scores (e.g., `cauchy-schwarz-integral-oq-01-oq-03-oq-01` at composite 76, `dissection-of-cubes-oq-04` at 57) were selected in the prior seeker batch (2026-04-23). To avoid 24-hour re-selection of the same problems, this is the highest-priority fresh EMPTY candidate.

2. **Domain diversity**: Recent selections covered geometry (ptolemy), combinatorics/analysis (derangements), discrete geometry (minkowski), and analysis (cauchy-schwarz). Probabilistic combinatorics and graph theory (triangle-removal process, limit laws) is underrepresented in recent selections.

3. **Tractable partial result**: While the full distributional limit of f(n)/n^{3/2} is open, the problem identifies achievable sub-goals: (a) variance bound via the second-moment method, or (b) formal Lean infrastructure for the random process. These are concrete deliverables within Lean 4 / Mathlib.

## Quality Gate

- Near-duplicate of recent completions? **No** — probabilistic graph theory is distinct from completed gallery proofs.
- Shallow specialization? **No** — OQ2 of Erdős #1155 targets the distributional limit, substantively different from the Θ(n^{3/2}) bound in the parent proof.
- Significance ≥ 3? **Yes** (6/10).
- Last 3 selections same domain? **No** — passes diversity check.

## Rejection Summary

- **Candidates considered**: 33 available
- **Candidates rejected**: 32
  - `sophie-germain-oq-01`, `twin-primes-special-oq-01`, `weak-goldbach-oq-01`: Open conjectures, tractability 2 — quality gate
  - `szemeredi-full-oq-02`: tractability 3, WEAK knowledge → composite -962 — low tractability
  - `sperner-ndim-oq-04`: active `.lock` claim
  - `erdos-268-incomplete-01`, `erdos-476-oq-05-wip-01`: parent problems have active `.lock` claims — conservative skip
  - `lebesgue-measure-oq-06`: RICH knowledge (247 lines, Banach-Tarski analysis) → composite ≈ -2932 — deprioritized
  - `shannon-channel-coding-oq-04`: malformed problem.md (empty description), selected 2026-03-22 but never worked on — data quality issue
  - All 2026-04-23 batch selections: 24-hour diversity cooldown applied
  - `derangements-convergence-oq-03`: selected today at 08:18 CEST — too recent
  - `ptolemys-theorem-oq-01-oq-02`: selected today — too recent
- **Confidence**: medium (score gap between EMPTY-tier fresh candidates is small; `erdos-1155-oq-02` is selected by elimination as the freshest EMPTY problem)

## Related Gallery Proofs

- `erdos-1155`: Parent proof — triangle-removal Θ(n^{3/2}) bound; provides the process definition and basic bounds

## Suggested First Steps

1. **OBSERVE**: Locate `erdos-1155` in the gallery and review how the triangle-removal process is modeled in Lean 4; identify what probability space is used (if any)
2. **ORIENT**: Search Mathlib for `Finset.card` + probability measure infrastructure; check if `ProbabilityTheory` or `MeasureTheory` has random graph process primitives
3. **DECIDE**: Choose between (a) variance bound formalization — show E[f(n)²] ≤ C·n³ to get concentration — or (b) formal statement of distributional convergence using `CDF` or `DistributionOf` in Mathlib

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 33 |
| In Progress | 558 |
| Completed | 1419 |
| Graduated | 9 |
| Blocked | 3 |

## Candidate Pool Health

- Pool depth: **adequate** (33 available > threshold 15, 2.2× above minimum)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Next refresh recommended: next scheduled seeker run (~30 min)
