# Problem Selection Report

**Date**: 2026-04-26
**Mode**: SELECT
**Pool Status**: 24 available, 555 in-progress, 1427 completed, 8 graduated, 5 blocked

## Selected Problem

- **ID**: szemeredi-counting-oq-02
- **Name**: Szemerédi Regularity: Hypergraph Counting Lemma Formalization
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Composite score 58** — highest among never-previously-selected, unclaimed candidates.
   Higher-scoring available problems were rejected:
   - `triangle-angle-sum-oq-03` (score 76): shallow Lean API exploration — "exploratory
     investigation" into `EuclideanGeometry.angle` degenerate cases, not mathematical research
   - `szemeredi-regularity-oq-02` (score 68): already selected 4× without progress (stale)
   - `cayley-hamilton-cyclic-vector-all-fields` (score 68): selected on master in last 48h (PR #12459)
   - `erdos-1-wip-01` (score 69): selected on master in last 48h (PR #12451)
   - `angle-trisection-oq-02-oq-01-oq-02-incomplete-01` (score 67): "formal statement to be added"
     — incomplete problem definition, quality gate rejection

2. **Domain diversity**: Recent selections were linear algebra (Cayley-Hamilton × 2), number
   theory (Erdős #1). This problem is extremal combinatorics / hypergraph theory — distinct domain.
   The last 3 selections were NOT from the same domain, so no diversity penalty; this is a
   natural complement.

3. **Builds on gallery infrastructure**: `szemeredi-hypergraph-core` already defines
   `SimplicialComplex`, k-graph density, and ε-regularity. The counting lemma is the natural
   next theorem. The gap from gallery to this result is non-trivial but well-defined.

4. **A-tier significance (8/10)**: The Nagle–Rödl–Schacht (2006) counting lemma is the
   core engine for hypergraph regularity proofs of Szemerédi's theorem. A Lean formalization
   of even the 3-uniform K₃ case would be notable and provide infrastructure for higher-order
   extremal results.

5. **Never previously selected**: Unlike `szemeredi-regularity-oq-02` (4 prior seeker selections
   with no progress), this problem is fresh — no prior selection report exists.

## Quality Gate

- Near-duplicate of recent completions? **No** — the hypergraph counting lemma (NRS 2006)
  is mathematically distinct from the graph regularity lemma and all recent selections.
- Shallow specialization? **No** — quantifying copies of a fixed hypergraph F in a regular
  k-graph is a substantive result with its own proof structure.
- Significance ≥ 3? **Yes** (8/10)
- Last 3 same domain? **No** — combinatorics after linear algebra + number theory.
- Incomplete definition? **No** — complete formal statement and problem description.

## Rejection Summary

- **Candidates considered**: 24 available (excluding 9 claimed)
- **Claimed (skipped)**: dissection-of-cubes-oq-04, hurwitz-theorem-oq-04,
  synthesis-curvature-ptolemy-2026-04-24, ballot-problem-oq-03-*, erdos-476-oq-05-wip-01,
  lebesgue-measure-oq-06, shannon-source-coding-oq-04, sperner-ndim-oq-04
- **Rejected — quality gate**: triangle-angle-sum-oq-03 (shallow Lean API),
  angle-trisection-oq-02-oq-01-oq-02-incomplete-01 (no formal statement),
  erdos-1001-oq-02-oq-01 (no formal statement), algebraic-numbers-countable-oq-04
  (no formal statement), basel-problem-oq-01-oq-01-oq-02-oq-01 (no formal statement)
- **Rejected — recently selected**: cayley-hamilton-cyclic-vector-all-fields (PR #12459),
  erdos-1-wip-01 (PR #12451), cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01 (PR #12440)
- **Rejected — stale / repeated selection**: szemeredi-regularity-oq-02 (4× selected, stuck)
- **Rejected — open conjectures (tractability ≤ 2)**: twin-primes-special-oq-01,
  weak-goldbach-oq-01, sophie-germain-oq-01
- **Confidence**: high — 10-point gap between this candidate (58) and next eligible (57, erdos-1001)

## Related Gallery Proofs

- `szemeredi-hypergraph-core`: Parent proof — provides SimplicialComplex, k-graph density, ε-regularity
- `szemeredi-regularity`: Graph regularity lemma — 2-uniform precursor and structural template
- `szemeredi-core`: Szemerédi theorem — downstream beneficiary of the counting lemma
- `roth-theorem-k3`: Roth's theorem — the 3-AP base case, relevant for NRS application

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/SzemerédiHypergraphCore.lean` to inventory current
   definitions of `kGraph`, `kGraphDensity`, `kGraphRegular`. Identify entry point for
   `∃ (F_copies : Finset _), F_copies.card ≈ d^{e(F)} * ∏|Vᵢ|`.

2. **ORIENT**: Focus on the 3-uniform triangle case first. Define "tripartite 3-graph"
   and state the triangle counting lemma: if H is ε-regular with density d on vertex
   sets V₁, V₂, V₃ with |Vᵢ| = n, then `triangles(H) ∈ ((d³ - f(ε))·n³, (d³ + f(ε))·n³)`.

3. **DECIDE**: Choose between (a) statement-only formalization targeting Aristotle, or
   (b) K₃ special case proof using double-counting and ε-regularity concentration bounds.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 24 |
| In Progress | 555 |
| Completed | 1427 |
| Graduated | 8 |
| Blocked | 5 |

## Candidate Pool Health

- Pool depth: **adequate** (24 available, threshold=15)
- Recommendation: Pool is healthy. No replenishment needed this cycle.
- Note: Several available problems have stale/repeated seeker selections and are stuck in
  OBSERVE with 0 attempts. Consider pruning or re-evaluating these if they remain idle.
- Next refresh recommended: when available count drops below 20

## Initialized

- [x] Research workspace exists (`research/problems/szemeredi-counting-oq-02/`)
- [x] problem.md populated with full NRS counting lemma description
- [x] state.md: OBSERVE phase
- [x] Ready for /researcher
