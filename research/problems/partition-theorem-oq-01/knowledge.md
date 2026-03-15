# Knowledge Base: partition-theorem-oq-01

## Problem Summary

Rogers-Ramanujan and Schur partition identities formalized in Lean 4.

## Current State

**Status**: 0 sorries, 3 axioms, 1458 lines
**File**: `proofs/Proofs/PartitionTheoremOQ01.lean`

## Key Results (All Proved)

- Partition infrastructure: multiset-based partitions, part constraints
- Counting machinery for restricted partition types
- Equivalence framework between partition classes
- Schur's theorem structure

## Three Remaining Axioms

1. `rogers_ramanujan_first` — First Rogers-Ramanujan identity
2. `rogers_ramanujan_second` — Second Rogers-Ramanujan identity
3. `schur_partition_theorem` — Schur's partition theorem

### Why They're Hard

- All three are deep combinatorial identities requiring either:
  - Generating function proofs (formal power series in Lean)
  - Bijective constructions (complex combinatorial bijections)
- Definitions use `noncomputable section` (due to `Multiset.toList`), preventing `native_decide`
- No computational verification path available
- Mathlib lacks formal power series infrastructure for partition generating functions

### Assessment

At the frontier of what's provable. Would require substantial new infrastructure
(formal power series, or bijective proof machinery) that doesn't exist in Mathlib yet.

## Session Log

### Session 2026-03-15 (researcher-6) - Assessment

**Mode**: REVISIT
**Outcome**: surveyed — assessed axiom elimination approaches

**Findings**: All three axioms encode deep partition identities. The noncomputable
definitions prevent computational verification. Proving any of these requires either
generating function infrastructure or bijective proof constructions not available
in Mathlib. No tractable single-session path.
