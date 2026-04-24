# Problem Selection Report

**Date**: 2026-04-22
**Mode**: SELECT
**Pool Status**: 30 available, 561 in-progress, 1404 completed, 3 graduated

## Selected Problem

- **ID**: minkowski-fundamental-theorem-oq-04
- **Name**: Minkowski Fundamental Theorem: Custom Lattice API vs ZLattice Comparison
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite among available, unclaimed, non-recently-selected candidates**: Composite score 77 (tractability 7 × 10 + significance 7), tied with `feuerbachs-theorem-defs-oq-04` but winning on domain diversity.
2. **Domain diversity**: Recent session selections covered geometry (triangle-angle-sum-oq-02, napoleons-theorem-oq-02), algebra (sqrt2-minpoly), and combinatorics (shapley-folkman-oq-03, newton-inductive-step-oq-03). This problem adds number theory / Lean API analysis — a distinct domain.
3. **Tractable and bounded**: The problem is not about proving new mathematics but about analysing and comparing two Lean formalization APIs. The source proof is complete (0 sorries, 662 lines), making the research scope well-defined.
4. **Mathlib alignment value**: A ZLattice-native reformulation would benefit the Mathlib community directly, making findings reusable without the custom `Lattice n` wrapper.

## Rejection Summary

- **Candidates considered**: 30 available (25 in pool JSON + 5 from DB not yet in pool JSON)
- **Candidates rejected**:
  - `sqrt2-plus-sqrt3-irrational-oq-03` (composite 96) — active claim lock present
  - `sqrt2-minpoly` (composite 86) — selected this session (commit 904edf6)
  - `triangle-angle-sum-oq-02` (composite 68) — selected this session (commit 5a99877)
  - `shapley-folkman-oq-03` (composite 67) — selected this session (commit 31c0a70)
  - `newton-inductive-step-oq-03` (composite 67) — selected this session (commit 1e1abc5)
  - `napoleons-theorem-oq-02` (composite 57) — selected this session (commit dcc6c36)
  - `feuerbachs-theorem-defs-oq-04` (composite 77, tied) — geometry domain, same as two recent selections; diversity penalty applied
  - `triangle-angle-sum-oq-03` (composite 76) — geometry domain, diversity penalty applied
  - Open conjectures (sophie-germain, twin-primes, weak-goldbach) — tractability ≤ 2, below threshold
- **Confidence**: high (7-point gap over next non-geometry candidate; diversity reasoning is clear)

## Related Gallery Proofs

- `minkowski-fundamental-theorem`: Parent proof — custom Lattice API + ZSpan bridge, 662 lines, fully verified (0 sorries, 0 axioms)

## Suggested First Steps

1. **OBSERVE**: Survey `Mathlib.Algebra.Module.ZLattice.Basic` and `Mathlib.Algebra.Module.ZLattice.Covolume` — list every `ZLattice` definition and theorem that overlaps with `Lattice n` in `MinkowskiFundamentalTheorem.lean`
2. **ORIENT**: Identify the key bridging point: does Mathlib's `ZLattice` have a `covolume` definition? Does `ZSpan.isAddFundamentalDomain` relate to `ZLattice`? Map the correspondence (or gap)
3. **DECIDE**: Determine whether a full refactoring is feasible within a few sessions, or whether a focused comparison document (without refactoring) is the better deliverable; draft a structured API comparison table

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 30 |
| In Progress | 561 |
| Completed | 1404 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

Pool is healthy and well above threshold.

- Pool depth: **adequate** (30 available vs. 15 threshold)
- Recommendation: Pool healthy — no immediate replenishment needed
- Next refresh recommended: in ~6 selections or when pool drops below 20 available
