# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 71 listed available (23 truly unselected), 2 in-progress, 661 graduated

## Selected Problem

- **ID**: binary-gcd-oq-01-oq-01
- **Name**: Binary GCD Total Cost Model Formalization
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Pool situation**: The candidate pool is nearly exhausted — 48 of 71 "available" problems have already been selected by prior seeker runs on master but the local pool hasn't been synced. Only 23 problems remain truly unselected, all with composite score ≤ 57.

2. **Top score among genuinely unselected candidates**: After filtering out problems already selected on master (verified via git log), `binary-gcd-oq-01-oq-01` is among the highest composite-score unselected problems (56, tied with 22 others). Selected over peers for domain diversity (algorithms/complexity — distinct from recent Galois theory, graph theory, analysis, and combinatorics selections).

3. **Concrete formalization target**: The goal is to formalize a total cost model for Stein's binary GCD algorithm — measuring total bit-operation cost as the product of step count × bit-operations per step. This is a well-defined question with known asymptotic results (Brent 1976, Knuth TAOCP). Unlike open conjectures, the mathematics here is established; the challenge is encoding the cost model in Lean 4.

4. **Workspace already exists**: A partial workspace (problem.md, state.md) was initialized previously. Adding knowledge.md and literature/ completes the setup.

## Rejection Summary

- **Candidates considered**: 23 truly unselected available problems
- **Rejected for code cleanup**: `abel-ruffini-oq-04-oq-01-oq-05` (vestigial lemma removal, not mathematics)
- **Rejected for blocked status**: `cantor-diagonalization-oq-03-oq-01-oq-05` (requires future Mathlib features)
- **Rejected as open questions**: `erdos-1-oq-02-oq-03/04`, `erdos-1-oq-03-*`, `erdos-10-oq-*`, `basel-problem-oq-01-oq-03-oq-02` (asking "can X be done" rather than "formalize known Y")
- **Confidence**: low (all 23 remaining candidates are tied at composite=56; selection is primarily domain-diversity-driven)

## Related Gallery Proofs

- `binary-gcd`: Parent proof — Binary GCD algorithm formalization
- `euclidean-algorithm`: Related GCD algorithm (Euclidean variant)

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/BinaryGcd.lean` to understand existing Binary GCD formalization
2. **ORIENT**: Survey Mathlib's `Int.GCD` and `Nat.Coprime` APIs; check what cost/complexity infrastructure exists
3. **DECIDE**: Define a `totalCost` function as `stepCount × bitsPerStep` and explore whether Lean 4 / Mathlib has the infrastructure for bit-length analysis

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available (listed) | 71 |
| Truly unselected | 23 |
| In Progress | 2 |
| Graduated | 661 |

## Candidate Pool Health

**Pool health: CRITICAL**

- Most "available" problems in the local pool were already selected by prior seeker runs on master (48/71)
- The pool JSON has not been synced with master's completed/in-progress state
- Only 23 truly unselected problems remain, all at composite=56-57 (B tier, sig=5-6, tract=5)
- **Recommendation**: Refresh pool from gallery (`npx tsx .lean/scripts/extract-problems.ts --json`) and sync database from master before next seeker run
- **Next refresh recommended**: Immediately — pool depth is critical
