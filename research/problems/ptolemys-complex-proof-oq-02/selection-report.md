# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 27 available, 559 in-progress, 1406 completed

## Selected Problem

- **ID**: ptolemys-complex-proof-oq-02
- **Name**: Ptolemy Theorem: Sine Addition Formula Connection via Chord Tables
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among unselected candidates**: Score = 67 (tractability=6 ×10 + significance=7), tied with ptolemys-theorem-oq-01-oq-02 but preferred as a "connection" problem with a clearer formalization path.
2. **EMPTY knowledge tier**: No prior research exists for this problem, making it high-priority per the selection algorithm.
3. **Concrete formalization target**: The sine addition formula sin(α+β) = sin α cos β + cos α sin β has direct Mathlib representation (`Real.sin_add`); the Ptolemaic derivation via cyclic quadrilateral gives a constructive proof path.
4. **Domain diversity**: Geometry/trigonometry — distinct from recent batch selections (combinatorics: Szemerédi, Sperner; algebra: minpoly, cubic; analysis: Lebesgue, Isoperimetric).
5. **Gallery connection**: Derives from `ptolemys-complex-proof` (Ptolemy's Inequality via Complex Numbers), which already has formal Lean infrastructure to build on.

## Rejection Summary

- **Candidates considered**: 9 remaining unselected available problems
- **Candidates rejected**: 6
  - `twin-primes-special-oq-01`: REJECTED — open conjecture (tractability=2, moonshot)
  - `weak-goldbach-oq-01`: REJECTED — open conjecture (tractability=2, moonshot)
  - `sophie-germain-oq-01`: REJECTED — open conjecture (tractability=2, moonshot)
  - `szemeredi-full-oq-02`: REJECTED — 4th Szemerédi-family selection in batch, diversity penalty applied
  - `sqrt2-minpoly-oq-01`: already selected earlier in batch (score=97, committed previously)
  - `sqrt2-minpoly-oq-02`: already selected earlier in batch (score=87, committed previously)
- **Confidence**: medium (two candidates tied at score=67; ptolemys-theorem-oq-01-oq-02 is the runner-up)

## Related Gallery Proofs

- `ptolemys-complex-proof`: The parent proof — Ptolemy's Inequality via Complex Numbers — provides formal context and complex-number machinery
- `ptolemys-theorem-oq-01`: Classical Ptolemy theorem formalization; base case for this connection
- `triangle-angle-sum`: Triangle geometry infrastructure in Lean 4, relevant for inscribed angle reasoning

## Suggested First Steps

1. **OBSERVE**: Read the `ptolemys-complex-proof` Lean source to understand the existing complex-number formulation; identify what chord-length and angle representations are available
2. **ORIENT**: Survey Mathlib for `Real.sin_add`, `Complex.abs`, inscribed angle theorem, and cyclic quadrilateral lemmas (`Inscribed`, `EuclideanGeometry`)
3. **DECIDE**: Determine whether to derive sin addition formula directly from the existing Ptolemy inequality proof, or formalize the classical chord-table construction independently

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 27 |
| In Progress | 559 |
| Completed | 1406 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

- Pool depth: **adequate**
- Recommendation: Pool is healthy; remaining unselected available problems: ptolemys-theorem-oq-01-oq-02, fair-games-theorem-oq-02-oq-01-oq-01, hurwitz-theorem-oq-04, divisibility-truncation-general-oq-03, plus 3 moonshots
- Next refresh recommended: Next seeker invocation (30 minutes)

## Initialized

- [x] Research workspace created (2026-04-22, exists)
- [x] problem.md populated with formal statement and context
- [x] state.md set to OBSERVE phase
- [x] Ready for /researcher
