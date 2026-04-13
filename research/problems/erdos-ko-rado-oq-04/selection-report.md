# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 533 in-progress, 1238 completed

## Selected Problem

- **ID**: erdos-ko-rado-oq-04
- **Name**: Formalize Ellis-Friedgut-Pilpel EKR theorem for permutations
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among untouched candidates**: Composite = 57 (EMPTY tier: 0 penalty + tractability×10=50 + significance=7). All higher-scoring candidates (unit-distance-independence-oq-02: 78, mean-value-theorem-oq-04: 77, erdos-szekeres-oq-01/euler-identity-oq-01-oq-04/vietas-formulas-oq-02/taylor-theorem-oq-02: 76, triangular-reciprocals-oq-02: 75, factor-remainder-nullstellensatz-oq-02: 67, buffons-needle-oq-01-oq-04/wolstenholme-theorem-oq-03: 66) have been selected in earlier seeker runs today (verified via selection-report.md presence in seeker worktree and main branch history).

2. **EMPTY knowledge tier**: The knowledge.md and JSON for this problem contain only an unfilled template — first-time exploration. Highest priority tier.

3. **Strong gallery infrastructure**: The parent proof `erdos-ko-rado` (Erdős-Ko-Rado Theorem and Extremal Set Family Extensions) is in the gallery, axiomatized with 0 sorries. It defines intersecting families, star families, and formalizes EKR via Katona's cyclic permutation argument (axiomatized). OQ-04 extends to permutations — a mathematically distinct result.

4. **Domain diversity**: Recent seeker selections span algebraic combinatorics (factor-remainder-nullstellensatz-oq-02), combinatorial geometry (unit-distance-independence-oq-02), group theory (euler-identity-oq-01-oq-04), number theory (wolstenholme-theorem-oq-03), and analysis (taylor-sincos-convergence-oq-01). EKR for permutations draws on representation theory of Sₙ and spectral graph theory — distinct from all of these.

5. **Mathematically substantive**: The Ellis-Friedgut-Pilpel (2011) result proves that an intersecting family of permutations in Sₙ has size ≤ (n-1)!. The EFP proof uses character theory of Sₙ (eigenvalue of the derangement graph) and is a genuine extension of EKR beyond set systems. Tractability 5 reflects the depth of representation theory required.

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - `unit-distance-independence-oq-02` (78): selected in a prior run today
  - `mean-value-theorem-oq-04` (77): selected in a prior run today
  - `erdos-szekeres-oq-01`, `euler-identity-oq-01-oq-04`, `vietas-formulas-oq-02`, `taylor-theorem-oq-02` (76 each): selected today
  - `triangular-reciprocals-oq-02` (75): selected on this branch (committed)
  - `factor-remainder-nullstellensatz-oq-02` (67): selected on this branch (committed)
  - `buffons-needle-oq-01-oq-04`, `wolstenholme-theorem-oq-03` (66): selected on this branch or main today
  - `brouwer-fixed-point-oq-04-oq-04` (56): lower composite; Kakutani constructive content is niche topology
  - `szemeredi-theorem-oq-01` (48): tractability 4 — Kelley-Meka direction is frontier mathematics, not suitable for autonomous research
  - `prime-gap-bounds-oq-03`: MODERATE knowledge (93-line knowledge.md) → knowledge_tier=2 → score ~-1923; deprioritized
  - `taylor-sincos-convergence-oq-01`: MODERATE knowledge (14 JSON items) → score -1925
- **Confidence**: medium (score gap is only 1 point between erdos-ko-rado-oq-04 and brouwer-fixed-point-oq-04-oq-04 after all higher candidates excluded; both are valid but EKR permutations edges out on significance 7 vs 6)

## Related Gallery Proofs

- `erdos-ko-rado`: Direct parent — defines intersecting families, proves EKR via Katona axioms; provides key type definitions (IntersectingFamily, StarFamily, n-subsets).
- `ramseys-theorem`: Extremal combinatorics sibling; similar proof architecture (pigeonhole double-count arguments).
- `burnside-counting`: Group action / orbit counting infrastructure — tangentially useful for symmetry arguments on Sₙ.

## Suggested First Steps

1. **OBSERVE**: Read `src/data/proofs/erdos-ko-rado/meta.json` to understand existing Lean definitions. Identify what's in `Proofs/ErdosKoRado.lean`: IntersectingFamily type, starFamily predicate, and which axioms cover the cyclic permutation argument. Check what Mathlib has for `Equiv.Perm` (the Lean type for Sₙ), character theory (`RepresentationTheory`), and spectral graph theory.

2. **ORIENT**: The EFP theorem to formalize: "If F ⊆ Sₙ is 1-intersecting (any two permutations agree on at least one point), then |F| ≤ (n-1)!." The proof strategy is: (a) define the derangement graph D on Sₙ (edges = derangements), (b) use the eigenvalue method — the smallest eigenvalue of D determines the independence number bound, (c) identify |F| ≤ (n-1)! = |Sₙ|/n as the bound.

   Simpler alternative: the "junta" approach — EFP showed intersecting families are "juntas" (determined by behavior on one coordinate). This combinatorial reformulation may be easier to formalize than the spectral proof.

3. **DECIDE**: Assess whether to pursue (a) the spectral/representation-theory route (requires formalizing eigenvalues of Cayley graphs on Sₙ, likely infeasible without extensive Mathlib development), (b) the junta/combinatorial route (may have elementary arguments accessible), or (c) scope down to axiomatizing the bound (n-1)! with a clear statement and explicit axiomatic assumptions, as was done for the parent EKR proof.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 533 |
| Completed | 1238 |
| Blocked | 1 |

## Candidate Pool Health

- Pool depth: **adequate** (15 available ≥ threshold of 5)
- Recommendation: Pool healthy; no replenishment needed now. Note that most of the 15 available problems have been selected in today's seeker runs — the pool is being actively worked through. After researchers claim these problems, the available count will drop. Monitor for replenishment when available count falls below 5.
- Next refresh recommended: when available < 5 or after current batch is claimed
