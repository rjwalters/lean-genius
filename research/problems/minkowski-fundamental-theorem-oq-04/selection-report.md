# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 28 available, 561 in-progress, 1403 completed, 9 graduated, 3 blocked

## Selected Problem

- **ID**: minkowski-fundamental-theorem-oq-04
- **Name**: Minkowski Fundamental Theorem: Custom Lattice API vs ZLattice Comparison
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among all unclaimed candidates**: Composite score 77 (tractability 7 × 10 + significance 7) — no other unclaimed candidate with EMPTY knowledge scored higher.
2. **Concrete, bounded scope**: The problem is not about proving new mathematics but analysing and comparing two Lean formalization APIs. The parent proof (`minkowski-fundamental-theorem`) is complete at 662 lines with 0 sorries and 0 axioms, giving the researcher a solid base to work from.
3. **Domain diversity**: Recent 2026-04-23 seeker batches covered info theory, probability, group theory, discrete geometry, combinatorics, logic, set theory, graph theory, algebra, and analysis. Geometric number theory / Mathlib lattice API is a distinct subdomain.
4. **Mathlib alignment value**: ZLattice-native reformulations benefit the Mathlib community directly. This is a recurring design question (custom types vs canonical Mathlib structures) that produces reusable insights.
5. **Low-medium difficulty with clear entry points**: Can begin with a pure survey of `Mathlib.Algebra.Module.ZLattice.*` before any proof attempt.

## Rejection Summary

- **Candidates considered**: 28 available in pool
- **Candidates rejected**:
  - `lebesgue-measure-oq-06`, `triangle-angle-sum-oq-02`: RICH/MODERATE knowledge — deprioritized by algorithm
  - `shapley-folkman-oq-03`: MODERATE knowledge (12 items)
  - `szemeredi-*` (4 problems): Szemerédi domain overrepresented in today's selections
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: tractability=2 (barely tractable open conjectures)
  - `ballot-problem-oq-03-oq-01-oq-04`: CLAIMED
  - `cauchy-schwarz-integral-oq-01-oq-03-oq-01` (composite 76): second-best, functional analysis — good candidate but yields to minkowski on composite
- **Confidence**: high — clear 1-point score gap at top, distinct domain, no disqualifying factors

## Related Gallery Proofs

- `minkowski-fundamental-theorem`: Parent proof — the custom Lattice n API under comparison
- `fermat-two-squares` (derived from minkowski): Demonstrates downstream utility of lattice infrastructure
- `sperner-ndim-oq-04`: Uses similar Mathlib geometry-of-numbers infrastructure

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/MinkowskiFundamentalTheorem.lean` focusing on the `Lattice n` structure definition (lines ~1–80) and `Lattice.toModuleBasis` construction. Note what the custom API provides that Mathlib's `ZSpan` does not.
2. **ORIENT**: Survey `Mathlib.Algebra.Module.ZLattice.Basic` and `.Covolume`. List the key theorems available. Compare with what the custom proof uses.
3. **DECIDE**: Determine if a ZLattice-native proof is feasible in < 4 sessions, or if the comparison document alone is the valuable output.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 28 |
| In Progress | 561 |
| Completed | 1403 |
| Graduated | 9 |
| Blocked | 3 |
| **Total** | **2004** |

## Candidate Pool Health

Pool is healthy — 28 available (threshold: 15), with majority having EMPTY knowledge scores.

- **Pool depth**: adequate (28 ≥ 15)
- **Recommendation**: Pool healthy; no replenishment needed this cycle
- **Next refresh recommended**: Next 30-minute seeker cycle

## Initialized

- [x] Research workspace created (`research/problems/minkowski-fundamental-theorem-oq-04/`)
- [x] problem.md populated
- [x] state.md initialized (OBSERVE, iteration 1)
- [x] knowledge.md initialized
- [x] literature/README.md initialized
- [x] Database entry verified (`available`)
- [x] candidate-pool.json synced
- [ ] Ready for /researcher
