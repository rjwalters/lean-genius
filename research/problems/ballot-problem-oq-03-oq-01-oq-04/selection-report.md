# Selection Report: ballot-problem-oq-03-oq-01-oq-04

**Date**: 2026-04-23
**Seeker Batch**: seeker/batch-selections-2026-04-23
**Pool Status**: 71 available, 2 in-progress (seeker worktree)

## Selected Problem

- **ID**: ballot-problem-oq-03-oq-01-oq-04
- **Name**: Catalan Number Recurrence: Formal Proof from the Ballot Theorem
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Probability/Combinatorics domain**: Underrepresented in the current available pool. The ballot problem gallery was recently active (oq-03-oq-01 committed recently), making this a natural extension.
2. **High tractability (7/10)**: The mathematical argument (first-return decomposition) is classical and well-understood. Lean 4 bijection infrastructure should support this.
3. **Gallery connection**: Directly extends `ballot-problem-oq-03-oq-01` which recently proved LGV-based results. Infrastructure is in place.
4. **EMPTY knowledge tier**: Fresh problem; high discovery value.

## Rejection Summary

- **Candidates considered**: 71 available in pool
- **Preferred over**: Fourier coefficient problem (similar tractability but less gallery infrastructure)
- **Domain diversity**: Probability/Combinatorics not covered in recent batch selections
- **Confidence**: high (clear mathematical path, strong gallery infrastructure)

## Related Gallery Proofs

- `ballot-problem`: Ballot theorem, reflection principle — parent proof
- `ballot-problem-oq-03-oq-01`: LGV lemma application — recent active extension

## Suggested First Steps

1. **OBSERVE**: Check Mathlib's `Nat.catalan` definition and what properties are already proved
2. **ORIENT**: Study `ballot-problem-oq-03-oq-01` to understand the Lean 4 path-counting setup
3. **DECIDE**: Define Dyck paths explicitly, formalize first-return decomposition as `Equiv`

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 71 |
| In Progress | 2 |
| Graduated | 661 |

## Candidate Pool Health

- Pool depth: adequate (71 available >> 15 threshold)
- Probability/Combinatorics domain added
- Next refresh recommended: 30 minutes (standard interval)

## Initialized

- [x] Research workspace created: `research/problems/ballot-problem-oq-03-oq-01-oq-04/`
- [x] problem.md populated with mathematical context
- [x] Registered in database with status 'available'
- [x] Pool synced (research/candidate-pool.json → .lean/state/candidate-pool.json)
- [ ] Ready for /researcher
