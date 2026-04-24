# Problem Selection Report

**Date**: 2026-04-24
**Mode**: SELECT
**Pool Status**: 15 available (at threshold), 558 in-progress, 1419 completed → 16 available after selection

## Selected Problem

- **ID**: abel-ruffini-galois-extensions-oq-04
- **Name**: Jordan-Hölder Uniqueness Theorem: Composition Factors of Finite Groups in Lean
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available (newly added)

## Selection Rationale

1. **EMPTY knowledge + high significance**: Composite score = 0 + 70 + 8 = 78, highest among tractable candidates
2. **Mathlib-gap with clear path**: Abstract theorem (`CompositionSeries.jordan_holder`) already exists; needs only a `JordanHolderLattice (Subgroup G)` instance — pure formalization, no new math
3. **Natural extension**: The parent `abel-ruffini-galois-extensions` uses the S₄ composition chain; Jordan-Hölder proves it's unique — directly strengthens an existing gallery proof
4. **Domain diversity**: Recent selections were analysis/number theory (Ptolemy, Derangements, Erdős #1155); this adds algebra variety

## Rejection Summary

- **Candidates considered**: 15 available (pool at threshold)
- **Open conjectures rejected**: sophie-germain-oq-01, twin-primes-special-oq-01, weak-goldbach-oq-01 — tractability 2/10, moonshot difficulty
- **MODERATE-knowledge rejected**: sperner-ndim-oq-04 (score 23, knowledge_tier=2, composite −1932)
- **WEAK-knowledge deprioritized**: erdos-268-incomplete-01, erdos-512-incomplete-01 (negative composite)
- **Selected over**: cauchy-schwarz-integral-oq-01-oq-03-oq-01 (composite 76, tractability 7) — Jordan-Hölder has higher significance (8 vs 6)
- **Confidence**: high — clear separation between Jordan-Hölder (composite 78) and runner-up

## Related Gallery Proofs

- `abel-ruffini-galois-extensions`: parent proof, directly benefits from uniqueness result
- `sylow-theorem`: composition series connect to Sylow theory

## Suggested First Steps

1. **OBSERVE**: Read `Mathlib.Order.JordanHolder` and `Mathlib.RingTheory.SimpleModule.Basic` to understand the `JordanHolderLattice` typeclass and the module instantiation template
2. **ORIENT**: Check `Mathlib.GroupTheory.QuotientGroup.Basic` for the second isomorphism theorem; identify the `Iso` type definition
3. **DECIDE**: Draft the `JordanHolderLattice (Subgroup G)` instance with `sorry`s for axioms; see which axioms are straightforward vs. hard

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 16 |
| In Progress | 558 |
| Completed | 1419 |
| Blocked | 3 |
| **Total** | **2005** |

## Candidate Pool Health

- **Pool depth**: adequate (16, one above 15 threshold)
- **Recent activity**: Pool drained from 33→15 during morning session (17 active researchers)
- **Added**: 1 new problem from gallery (abel-ruffini OQ4)
- **Recommendation**: Pool is healthy for now; next seeker run should check if pool drops below threshold
- **Next refresh recommended**: Next scheduled cycle (30 min)
