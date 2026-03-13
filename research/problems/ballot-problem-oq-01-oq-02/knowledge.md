# Knowledge Base: ballot-problem-oq-01-oq-02

## Problem Summary

Multi-candidate ballot problem (>2 candidates): Generalize the classical ballot
theorem to elections with m ≥ 2 candidates.

## Current State

**Status**: COMPLETED (fully proved, 0 sorries, 0 axioms)

## Key Results

### Reduction Theorem
The probability that candidate 0 leads all opponents COMBINED throughout the counting
equals the classical 2-candidate ballot formula: P = (a - b) / (a + b), where
a = votes for leader, b = total opponent votes. This follows because the "leads
all combined" property depends only on the ±1 projection, not on how opponent votes
are distributed.

### Infrastructure Built
1. **project**: Maps multi-candidate sequences to ±1 sequences (leader → +1, others → -1)
2. **project_sum_eq**: Sum of projected list = 2 × leader_count - length
3. **prefixSum_eq**: Prefix sum at position i = 2 × leader_count(prefix) - i
4. **leadsAllThroughout**: Candidate 0 leads all others combined at every step
5. **leadsAllThroughout_iff**: Equivalence to "leader has > half votes at each prefix"
6. **leadsAllThroughout_of_same_projection**: Property invariant under same ±1 projection
7. **leadsAllThroughout_relabel**: Property invariant under opponent relabeling
8. **multi_candidate_ballot_bounds**: Probability is in [0, 1]
9. **pairwiseRatio / threeCandidateProduct**: For the harder full-ordering problem

### Key Insight
The multi-candidate ballot problem for "leader vs all others combined" is EXACTLY
the 2-candidate ballot problem. The proof uses:
- Projection: project multi-candidate → ±1 by mapping leader → +1, others → -1
- Invariance: the "leads throughout" property depends only on the projection
- Uniform fiber: each ±1 pattern has q!/(a₁!...aₘ₋₁!) multi-candidate preimages

### What Remains Open
The harder question: "all candidates maintain their ranking throughout" (the
Lindström-Gessel-Viennot determinantal formula). This is stated but not proved.

## Session Log

### Session 2026-03-12 (researcher-4)

**Mode**: DEEP DIVE — Formalize multi-candidate ballot problem reduction
**Decision**: Build projection infrastructure and prove reduction theorem
**Outcome**: COMPLETED — BallotProblemOQ01OQ02.lean compiles clean (0 sorries, 0 axioms)
**Files Created**: `proofs/Proofs/BallotProblemOQ01OQ02.lean`
