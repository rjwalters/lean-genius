# Problem Selection Report

**Date**: 2026-04-26
**Mode**: SELECT (pool replenishment)
**Pool Status**: 15 available (at threshold), 558 in-progress, 1434 completed, 8 graduated, 4 blocked

## Selected Problem

- **ID**: `basel-problem-oq-04-oq-03`
- **Name**: Formalize Probabilistic Statement: Pr[gcd(m,n)=1] = 6/π² via Mathlib Measure Theory
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 68
- **Status**: available (new addition)

## Selection Rationale

1. **Highest composite score among new candidates**: Score of 68 (ties with
   `cayley-hamilton-cyclic-vector-all-fields` and `lebesgue-measure-oq-06`). Among the
   3 new problems added this cycle, this has the highest tractability × significance.

2. **Probabilistic number theory domain**: The pool lacks probabilistic interpretations
   of number theory. This problem elegantly bridges ζ(2) = π²/6 (gallery) with a
   probabilistic density statement.

3. **Mathlib tractability**: `Nat.Coprime`, `Nat.gcd`, Möbius function in
   `NumberTheory.ArithmeticFunction`, and the gallery's `basel-problem` proof of ζ(2) = π²/6
   provide strong foundations.

4. **EMPTY knowledge tier**: Fresh problem, no prior research notes. Ready for OBSERVE.

5. **Domain diversity**: Recent selections were Erdős diophantine (erdos-1001-oq-02-oq-01)
   and Erdős subset sums (erdos-1-wip-01). Probabilistic number theory is a new domain.

## Rejection Summary

- **Domain repetition avoided**: Not Erdős, Szemerédi, Cayley-Hamilton, or AMGM family
- **Quality gate passed**: Significance 8 ≥ threshold 3, tractability 6 is good
- **Not claimed**: No active lock file
- **Confidence**: high (clear proof path via Möbius inversion + gallery ζ(2) result)

## Related Gallery Proofs

- `basel-problem`: ζ(2) = π²/6 — core ingredient
- `basel-problem-oq-04`: Euler product formula (parent context)
- `infinitude-of-primes`: Prime enumeration context

## Suggested First Steps

1. **OBSERVE**: Read `src/data/proofs/basel-problem/` and `basel-problem-oq-04/` to
   understand what's formalized about ζ(2) = π²/6 and the Euler product
2. **ORIENT**: Search Mathlib for `Nat.ArithmeticFunction.moebius`,
   `Nat.ArithmeticFunction.cardDistinctFactors`, and density/Cesàro API
3. **DECIDE**: Choose between Möbius approach (cleaner) vs. Euler product approach
   (more direct but harder). Draft the `Filter.Tendsto` formal statement.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 18 |
| In Progress | 558 |
| Completed | 1434 |
| Graduated | 8 |
| Blocked | 4 |

## Initialized

- [x] Problem registered in `research/db/knowledge.db` (status: available)
- [x] Pool synced: `research/candidate-pool.json` updated (49 available)
- [x] Pool synced: `.lean/state/candidate-pool.json` updated (18 available)
- [x] Research workspace created: `research/problems/basel-problem-oq-04-oq-03/`
- [x] `problem.md` populated with formal statement, approaches, and references
- [x] `state.md` set to OBSERVE phase
- [x] Ready for /researcher
