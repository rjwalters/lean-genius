# Seeker Selection Report — Cycle 82

**Date**: 2026-04-23
**Selected**: `sperner-ndim-oq-04`
**Title**: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

---

## Selection Summary

| Field | Value |
|-------|-------|
| Composite Score | -932 (WEAK tier) |
| Significance | 8 / 10 |
| Tractability | 6 / 10 |
| Knowledge Tier | WEAK (4 files, ~17KB knowledge.md) |
| Domain | combinatorics / algorithms |
| Tier | A |

## Candidate Pool State

- Total available: 28
- After locking/recently-selected filter: 15 eligible
- After geometry exclusion (domain streak): 12 eligible
- After number-theory domain streak: 9 eligible
- After Szemerédi near-duplicate filter: 7 eligible

## Ranking (Top 5 Eligible)

| Rank | Score | Problem | Sig | Trt |
|------|-------|---------|-----|-----|
| #1 | -932 | **sperner-ndim-oq-04** | 8 | 6 |
| #2 | -933 | newton-inductive-step-oq-03 | 7 | 6 |
| #3 | -933 | ptolemys-complex-proof-oq-02 | 7 | 6 |
| #4 | -933 | ptolemys-theorem-oq-01-oq-02 | 7 | 6 |
| #5 | -934 | fair-games-theorem-oq-02-oq-01-oq-01 | 6 | 6 |

## Rejected Candidates

| Problem | Reason |
|---------|--------|
| triangle-angle-sum-oq-03 | geometry domain (recently excluded) |
| minkowski-fundamental-theorem-oq-04 | recently selected (today) |
| cauchy-schwarz-integral-oq-01-oq-03-oq-01 | recently selected |
| ballot-problem-oq-03-oq-01-oq-01-oq-01 | recently selected (cycle 81) |
| konigsberg-oq-02-oq-01 | recently selected |
| erdos-476-oq-05-wip-01 | LOCKED |
| fourier-series-oq-02-oq-02 | LOCKED |
| szemeredi-regularity-oq-02 | near-duplicate (Szemerédi) |
| szemeredi-counting-oq-02 | near-duplicate (Szemerédi) |
| szemeredi-full-oq-01 | near-duplicate (Szemerédi) |
| szemeredi-full-oq-02 | near-duplicate (Szemerédi) |
| twin-primes-special-oq-01 | recently selected + number-theory streak |
| weak-goldbach-oq-01 | recently selected + number-theory streak |
| sophie-germain-oq-01 | recently selected + number-theory streak |
| divisibility-truncation-general-oq-03 | number-theory domain streak |
| liouville-theorem-oq-04 | number-theory domain streak |

## Why sperner-ndim-oq-04 Wins

1. **Highest significance (8/10)** among eligible candidates — Kuhn's algorithm is the foundation of Lemke-Howson for Nash equilibria and Scarf's fixed-point method
2. **Good tractability (6/10)** — Core lemmas already proved; single sorry `kuhn_walk_result_not_in_visited` described as "TRIVIAL for Aristotle" in knowledge.md
3. **Domain diversity** — combinatorics/algorithms, not overrepresented in recent selections
4. **Active workspace** — 17KB knowledge.md with detailed session notes, clear next steps, and Lean file already at `proofs/Proofs/SpernerNDimOQ04.lean`
5. **Aristotle candidate** — The remaining sorry appears well-suited for automated proof search
6. **Distinguished from oq-05** — oq-05 (LOCKED) focuses on Mathlib contribution; oq-04 focuses on algorithm correctness proof

## Current State

The Lean file `proofs/Proofs/SpernerNDimOQ04.lean` (~290 lines) has:
- Proved: `fc_door_count_eq_one`, `nonfc_door_count_zero_or_two`, `nonfc_with_door_has_unique_exit`, `kuhn_path_terminates`
- Remaining: `kuhn_walk_result_not_in_visited` (non-revisiting invariant, TRIVIAL for Aristotle per session 6 notes)
- Removed: `kuhn_walk_reaches_fc` (was mathematically incorrect)

## Next Steps for Researcher

1. Attempt `kuhn_walk_result_not_in_visited` via Finset cardinality argument (visited set grows monotonically)
2. If Aristotle-compatible, submit for automated proof search
3. Complete `kuhnPathStart_is_fc` top-level correctness theorem
4. Verify gallery integration compiles: `./proofs/scripts/docker-build.sh Proofs.SpernerNDimOQ04`
