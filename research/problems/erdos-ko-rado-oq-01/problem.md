# Problem: Erdős-Ko-Rado OQ-01: Prove `at_most_k_intersecting_cyclic_intervals` Bound

**Slug**: erdos-ko-rado-oq-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Source**: `src/data/proofs/erdos-ko-rado/meta.json`, open question 1

Formalize the bound for k-intersecting families of cyclic intervals:
- The maximum size of a k-intersecting family of cyclic intervals of length r in [n]
  is at most r (for appropriate parameters)

## Lean Context

From `proofs/Proofs/ErdosKoRado.lean`:
- EKR theorem: for t-intersecting families of k-sets from [n] with n ≥ 2k,
  |F| ≤ C(n-1, k-1)
- Cyclic intervals are special k-element subsets of cyclic group ℤ_n

## Approach

1. Check what's already in `ErdosKoRado.lean`
2. Find the specific open question about cyclic intervals
3. Apply the general EKR bound to this special case

## Tractability: MEDIUM
