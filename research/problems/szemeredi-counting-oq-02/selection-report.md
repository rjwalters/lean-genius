# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 26 available, 557 in-progress, 1408 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: szemeredi-counting-oq-02
- **Name**: Szemerédi Regularity: Hypergraph Counting Lemma Formalization
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Composite score 58** — highest among unselected candidates in this cycle. All
   higher-scoring available problems already have selection reports from this session.

2. **Distinct from other Szemerédi selections this session** — `szemeredi-full-oq-02`
   (density bound) and `szemeredi-regularity-oq-02` (Frieze-Kannan comparison) were
   selected earlier. The hypergraph counting lemma is a different result: it quantifies
   copies of a fixed hypergraph F in an ε-regular k-graph. The Nagle-Rödl-Schacht (2006)
   counting lemma is the core engine of the hypergraph regularity proof of Szemerédi's
   theorem — it operates at a different level from the regularity lemma itself.

3. **Builds on existing gallery infrastructure** — `szemeredi-hypergraph-core` already
   defines `SimplicialComplex`, k-graph density, and ε-regularity. The counting lemma
   is the natural next theorem in this chain. The gap from gallery to this result is
   non-trivial but well-defined.

4. **A-tier significance** — the NRS counting lemma is a landmark result in extremal
   combinatorics. A Lean formalization of even the 3-uniform case would be noteworthy
   and would provide infrastructure for hypergraph Ramsey results.

## Rejection Summary

- **Candidates considered**: 7 remaining unselected available problems in this session
- **Moonshot candidates rejected** (tractability ≤ 2): twin-primes-special-oq-01,
  weak-goldbach-oq-01, sophie-germain-oq-01 — famous open conjectures, no tractable
  entry point for autonomous formalization
- **szemeredi-full-oq-01**: deferred — higher significance (9/10) but adds a third
  Szemerédi problem to the session; the Furstenberg ergodic approach is better suited
  for a future cycle when the hypergraph work is already underway
- **Confidence**: medium (the hypergraph counting lemma is substantive; a full proof is
  challenging at tractability 5, but the 3-uniform triangle-copy case is tractable)

## Related Gallery Proofs

- `szemeredi-hypergraph-core`: Parent proof — defines the k-graph regularity apparatus.
  The counting lemma extends this with the copy-counting theorem.
- `szemeredi-regularity`: Graph regularity lemma — the 2-uniform precursor.
- `szemeredi-core`: Core Szemerédi theorem — downstream beneficiary of the counting lemma.
- `roth-theorem-k3`: Roth's theorem — the 3-AP base case, relevant for the NRS application.

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/SzemerédiHypergraphCore.lean` to find current
   definitions of `kGraph`, `kGraphDensity`, `kGraphRegular`. Identify the entry point
   for formalizing `∃ (F_copies : Finset _), F_copies.card ≈ d^e(F) * ∏|Vᵢ|`.

2. **ORIENT**: Focus on the 3-uniform triangle case. Define "tripartite 3-graph" and
   "density of a tripartite 3-graph." State the triangle counting lemma: if H is
   ε-regular with density d on vertex sets V₁, V₂, V₃ with |Vᵢ| = n, then
   `triangles(H) ∈ ((d³ - f(ε)) * n³, (d³ + f(ε)) * n³)`.

3. **DECIDE**: The proof uses inclusion-exclusion on the bipartite graphs between pairs
   Vᵢ × Vⱼ. ε-regularity of each pair forces edge counts to concentrate. This may
   reduce to `Finset.card_sdiff` estimates and integer division bounds.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 26 |
| In Progress | 557 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

- Pool depth: **adequate** (26 available, threshold=15)
- Recommendation: Pool healthy. 6 available problems remain after this selection.
- Next refresh recommended: next scheduled cycle (~30 min)

## Initialized

- [x] Research workspace exists (`research/problems/szemeredi-counting-oq-02/`)
- [x] problem.md populated
- [x] state.md: OBSERVE phase
- [x] Ready for /researcher
