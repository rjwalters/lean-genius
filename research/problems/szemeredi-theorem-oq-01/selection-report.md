# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 16 available, 533 in-progress, 1238 completed, 1 blocked

## Selected Problem

- **ID**: szemeredi-theorem-oq-01
- **Name**: What is the optimal bound for 3-AP-free sets (Kelley-Meka direction)
- **Tier**: B
- **Significance**: 8/10
- **Tractability**: 4/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest remaining significance among unselected candidates**: All other top-scoring candidates (score ≥ 66) already have selection-reports written today. `szemeredi-theorem-oq-01` (sig=8, tract=4, composite=48) is the last EMPTY-tier problem without a formal selection this cycle.
2. **Research frontier problem**: The Kelley-Meka 2023 breakthrough on 3-AP-free sets (almost polynomial bounds via higher-order Fourier analysis) is among the most significant recent advances in additive combinatorics. Formalizing even a fragment — density statements, exponential bounds, or the connection to cap-set problem — would be a genuine contribution.
3. **Domain diversity**: Additive combinatorics is distinct from the previous selections (analysis, algebra, probability, number theory). No diversity penalty applies.
4. **Not claimed**: No active `.lock` file; fresh workspace from bulk initialization.

## Rejection Summary

- **Candidates considered**: 16 available
- **Candidates rejected**:
  - `unit-distance-independence-oq-02`: CLAIMED (active lock file)
  - `prime-gap-bounds-oq-03`: RICH knowledge tier (93 lines) — deprioritized to -2923
  - 13 problems (arithmetic-series-oq-00, brouwer-fixed-point-oq-04-oq-04, buffons-needle-oq-01-oq-04, erdos-ko-rado-oq-04, erdos-szekeres-oq-01, euler-identity-oq-01-oq-04, factor-remainder-nullstellensatz-oq-02, mean-value-theorem-oq-04, taylor-sincos-convergence-oq-01, taylor-theorem-oq-02, triangular-reciprocals-oq-02, vietas-formulas-oq-02, wolstenholme-theorem-oq-03): already selected earlier today
  - `szemeredi-theorem-oq-01`: **SELECTED** (highest significance among remaining)
- **Confidence**: medium (tractability 4/10 reflects difficulty; lower confidence that a researcher can close this quickly)

## Related Gallery Proofs

- `szemeredi-theorem`: Szemerédi's theorem k=3 via Mathlib — direct parent; establishes the qualitative density result this problem quantifies
- `szemeredi-regularity`: Szemerédi Regularity Lemma — key technical tool underlying density approaches
- `szemeredi-core`: Core combinatorial infrastructure — supporting lemmas on arithmetic progressions
- `szemeredi-counting`: Counting lemma for AP detection — quantitative combinatorial backbone

## Suggested First Steps

1. **OBSERVE**: Survey existing `proofs/Proofs/Szemeredi*.lean` files to understand what density primitives and AP machinery already exist in the formalization. Check Mathlib for `additiveCombinatorics` or `density` API.
2. **ORIENT**: Read the Kelley-Meka paper abstract to understand the core claim: sets without 3-APs in {1,...,N} have size ≤ N/exp(Ω(log^{1/11} N)). Identify the simplest formalizable statement — likely the density bound rather than the full proof.
3. **DECIDE**: Choose a tractable target: (a) formalize the density statement as an axiomatized theorem with the bound as hypothesis, (b) prove a weaker exponential bound (Salem-Spencer style), or (c) formalize the connection between 3-AP-freeness and cap-set via tensor power trick.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 16 |
| In Progress | 533 |
| Completed | 1238 |
| Skipped | 0 |
| Blocked | 1 |

## Candidate Pool Health

Pool has 16 available problems — above the replenishment threshold of 5. Health is **adequate**.

- Pool depth: adequate (16 ≥ 5 threshold)
- Recommendation: Pool healthy; no immediate replenishment needed
- Next refresh recommended: when available count drops below 5
