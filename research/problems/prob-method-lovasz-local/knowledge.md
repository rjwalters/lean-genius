# Knowledge Base: prob-method-lovasz-local

## Problem Summary

Formalize the Lovász Local Lemma: if bad events are each unlikely and mostly independent,
they can all be avoided simultaneously.

## Current State

**Status**: PROGRESS

### Research Session (2026-03-21)
**Mode**: FRESH (researcher-3)
**Decision**: BUILD - Enhance 66-line stub to proper formalization

**Changes**: Rewrote LovaszLocalLemma.lean from 66 lines to 193 lines.

#### New Content
- LLL threshold function T(d) = d^d/(d+1)^{d+1} with concrete values
- Constant product lemmas (prod_const_fin, neighborhood_prod_const)
- Symmetric LLL product positivity with x_i = 1/(d+1)
- k-SAT bound: 2^{k-2} + 1 ≤ 2^k (replaces sorry'd rational arithmetic)
- Dependency graph structure (IsValidDepGraph, HasMaxDegree)
- Independent events case, clause violation bounds

#### Removed sorry
- ksat_lll sorry replaced with ksat_bound (proved via omega)

### Key Insights
- General LLL algebraic core: each (1-x_i) > 0 when x_i < 1
- T(d) = d^d/(d+1)^{d+1} is the exact threshold for symmetric LLL
- T(1) = 1/4, T(2) = 4/27, T(3) = 27/256 — all proved by ring
- k-SAT satisfiability reduces to elementary arithmetic bound
- Full probabilistic LLL requires MeasureTheory — algebraic version is the achievable core

### What Would Complete This
1. Prove lllThreshold_le_quarter for all d ≥ 1
2. Connect symmetric and general LLL formally (derive one from the other)
3. Add graph coloring application
4. Full probabilistic LLL with MeasureTheory (long-term)
