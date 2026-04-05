# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 4 available, 1094 in-progress, 1225 completed

## Selected Problem

- **ID**: binary-gcd-oq-01-oq-04-oq-01
- **Name**: Exact worst-case analysis of Binary GCD algorithm
- **Tier**: C
- **Significance**: 5/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Concrete foundation**: Parent `binary-gcd-oq-01-oq-04` proved `binaryGcdSteps 1 (2^n - 1) = n` with 0 axioms, 0 sorries — a tight lower bound family. The OQ01 child asks for the *complete* characterization of all worst-case input families, a natural next step with a clear starting point.
2. **Rich theoretical structure**: Connection to Stern-Brocot / Calkin-Wilf tree is mathematically deep — worst-case paths in the Binary GCD DAG likely correspond to Fibonacci-like trajectories, with theory-level implications for algorithm analysis.
3. **Highest composite score among eligible candidates**: Composite 65 (tract 6 × 10 + sig 5) vs cayley-hamilton-minpoly-oq-02-oq-02-oq-01 (58), borsuk-ulam-oq-02-oq-01-oq-03 (56). All candidates had knowledge tier EMPTY, so tiebreaker is composite.
4. **Domain diversity**: Algorithms / discrete mathematics — different from the three most recent selections (erdos-1008: graph theory, erdos-1069: combinatorial geometry, dissection-of-cubes: geometry).
5. **Fresh workspace**: Initialized today (2026-04-05), OBSERVE phase, 0 attempts. No active claim.

## Rejection Summary

- **Candidates considered**: 18 in pool JSON, but 13/18 were "in-progress" in database (pool JSON was stale). Effective available candidates: 5 per DB.
- **Rejected — proof already complete**: `angle-trisection` — `AngleTrisection.lean` has 0 sorries, 0 axioms; nothing for researcher to do.
- **Skipped — recently selected (cooldown)**: `dissection-of-cubes` (3rd most recent seeker commit), `hilbert-10-oq-03` (5th most recent).
- **Lower composite**: `cayley-hamilton-minpoly-oq-02-oq-02-oq-01` (58 — A-tier but no Lean file yet for this OQ, tract 5), `borsuk-ulam-oq-02-oq-01-oq-03` (56 — 9 axioms requiring equivariant topology not in Mathlib).
- **Confidence**: medium (binary-gcd wins cleanly on composite score; cayley-hamilton is stronger mathematically but lower tractability)

## Related Gallery Proofs

- **binary-gcd-oq-01**: Upper bound O(log b) — the bound this problem aims to tightly characterize
- **binary-gcd-oq-01-oq-04**: Direct parent — proves (1, 2^n-1) achieves exactly n steps (complete, 0 axioms, 0 sorries)
- **binary-gcd-oq-01-oq-03**: Worst-case verification results — survey for existing step-count machinery

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/BinaryGcdOQ01OQ04.lean` in full. Understand the (1, 2^n-1) tight family proof via one-step lemma induction. Inventory all step-count lemmas across `BinaryGcdOQ01*.lean` files.
2. **ORIENT**: Map the Binary GCD recursion onto a path in the Calkin-Wilf tree. Identify whether (1, 2^n-1) is the *unique* worst-case family or whether Fibonacci-like pairs (Fib(n), Fib(n+1)) also achieve tight bounds.
3. **DECIDE**: Attempt to prove `binaryGcdSteps a b ≤ binaryGcdSteps 1 (2^(⌊log₂ b⌋) - 1)` for all a ≤ b — establishing (1, 2^n-1) as the extremal family. Check if Mathlib has Fibonacci-step-count lemmas for Euclidean-style algorithms.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 4 |
| In Progress | 1094 |
| Completed | 1225 |
| **Total** | **1646** |

## Candidate Pool Health

- **Pool depth**: LOW (4 available, below the 5-problem threshold)
- **Note**: Pool JSON was stale before this run — 13 problems listed as "available" in pool JSON were "in-progress" in database. Pool has been synced to DB state.
- **Recommendation**: Replenishment needed. Next cycle should run `npx tsx .lean/scripts/extract-problems.ts --json` to surface new candidates from gallery.
- **Priority candidates for replenishment**: `erdos-1027` (1 axiom, unclaimed in-progress), `erdos-1026` (2 axioms, unclaimed), `cayley-hamilton-minpoly-oq-02-oq-02-oq-01` (A-tier, available).
- **Next refresh recommended**: immediately (pool depth critical)
