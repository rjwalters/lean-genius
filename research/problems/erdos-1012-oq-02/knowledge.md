# erdos-1012-oq-02: Vertex-Pancyclicity Strengthening

## Problem Summary

**Open Question**: Can Woodall's pancyclicity result (cycles of all lengths 3 to n-k) be strengthened to vertex-pancyclicity (every vertex on every cycle length)?

**Status**: SURVEYED - 8 proved theorems, 2 axioms, 3 sorries.

## Session 2026-03-18 - Survey

**Mode**: REVISIT (file existed from prior session)
**Outcome**: surveyed, enriched knowledge

### Current Architecture
- **Definitions**: hasCycleThroughVertex, isVertexPancyclicUpTo, isVertexPancyclicGraphUpTo, pancyclicSpectrum
- **Axioms**: Bondy VP (1971), Woodall VP strengthening
- **Proved**: 8 structural theorems (monotonicity, implications, consequences)
- **Sorries**: 3 (arithmetic + Walk API)

### Remaining Sorries Analysis

1. **threshold_k0_exceeds_turan** (easiest): C(n-1,2)+2 >= n^2/4+1 for n>=3
   - Math: 2(n-1)(n-2) >= n^2-4 iff (n-2)(n-4) >= 0
   - True for n>=4; n=3 by decide
   - Lean challenge: Nat.choose expansion + natural division arithmetic

2. **threshold_exceeds_turan_for_small_k** (harder): General k<=n/4 case
   - Requires showing C(n-k-1,2) + C(k+2,2) + 1 >= n^2/4 + 1
   - More complex binomial arithmetic

3. **vertex_pancyclic_implies_connected** (Walk API): VP -> Connected
   - Strategy: every vertex on n-cycle (Hamiltonian) -> all vertices reachable
   - Walk.IsCycle of length n visits all n vertices
   - Extract Walk v u from cycle for any u

4. **spectrum_size_lower_bound** (counting): |spectrum ∩ [3,m]| >= m-2
   - Need Set.ncard of intersection with Icc
   - The spectrum contains all of {3,...,m} by VP hypothesis

### Files
- `proofs/Proofs/Erdos1012OQ02.lean` (308 lines)
