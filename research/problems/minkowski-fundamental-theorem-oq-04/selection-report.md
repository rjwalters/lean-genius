# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 30 available, 555 in-progress, 1408 completed, 7 graduated, 4 blocked

## Selected Problem

- **ID**: minkowski-fundamental-theorem-oq-04
- **Name**: Minkowski Fundamental Theorem: Custom Lattice API vs ZLattice Comparison
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among all unclaimed candidates**: Composite score 77 (tractability 7 × 10 + significance 7) — the only Tier B problem with both tractability 7 and significance 7 and EMPTY knowledge.
2. **Concrete, bounded scope**: Not about proving new mathematics but analysing two Lean formalization APIs. The parent proof (`minkowski-fundamental-theorem`) is complete at 662 lines with 0 sorries and 0 axioms, giving the researcher a solid base.
3. **Domain diversity**: Recent seeker selections covered geometry (triangle-angle-sum), analysis (Erdős #268), exponential sums (Erdős #512), graph theory (Königsberg), and combinatorics (Szemerédi regularity). Geometric number theory / Mathlib lattice API is a distinct subdomain not recently represented.
4. **Mathlib alignment value**: ZLattice-native reformulations benefit the Mathlib community directly. This is a recurring design question (custom types vs canonical Mathlib structures) that produces reusable insights.
5. **Low-medium difficulty with clear entry points**: Can begin with a pure survey of `Mathlib.Algebra.Module.ZLattice.*` before any proof attempt.

## Rejection Summary

- **Candidates considered**: 30 available in pool
- **Candidates rejected**:
  - `sperner-ndim-oq-04`: RICH knowledge (248 kb_lines) — deprioritized by algorithm
  - `szemeredi-*` (4 problems, composite 38–58): Szemerédi domain overrepresented in recent selections — diversity penalty
  - `erdos-512-incomplete-01`, `szemeredi-regularity-oq-02`: WEAK knowledge but recently selected
  - `triangle-angle-sum-oq-03`: Just selected (most recent seeker commit)
  - `cauchy-schwarz-integral-oq-01-oq-03-oq-01` (composite 76): Previously selected in prior run — already queued
  - `ballot-problem-oq-03-oq-01-oq-04` (composite 76): Active researcher claim
  - `weak-goldbach-oq-01`, `twin-primes-special-oq-01`, `sophie-germain-oq-01`: tractability ≤ 2 — barely tractable open conjectures
- **Confidence**: high — clear score separation at top, distinct domain, no disqualifying factors

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
| Available | 30 |
| In Progress | 555 |
| Completed | 1408 |
| Graduated | 7 |
| Blocked | 4 |
| **Total** | **2004** |

## Candidate Pool Health

Pool is healthy — 30 available (threshold: 15), all initialized workspaces.

- **Pool depth**: adequate (28 ≥ 15)
- **Recommendation**: Pool healthy; no replenishment needed this cycle
- **Next refresh recommended**: Next 30-minute seeker cycle

## Initialized

- [x] Research workspace created (`research/problems/minkowski-fundamental-theorem-oq-04/`)
- [x] problem.md populated
- [x] state.md initialized (OBSERVE, iteration 1)
- [x] knowledge.md initialized
- [x] literature/README.md initialized
- [x] Database entry verified (`available`, tier B, sig 7, tract 7)
- [x] candidate-pool.json synced
- [ ] Ready for /researcher
