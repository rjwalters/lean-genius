# Knowledge Base: ramsey-lower-bounds

## Problem Summary

Prove R(3,3) = 6 exactly by constructing the lower bound. The existing `RamseysTheorem.lean` had the upper bound via `ramseyBound 3 3 = 6`. This research added the lower bound: K_5 can be 2-colored without a monochromatic triangle.

## Current State

**Status**: COMPLETED

### What's Proven (no sorries)

1. **Pentagon coloring construction**
   - `absDiff5` - Helper for computing absolute difference mod 5
   - `absDiff5_symm` - Symmetry of absolute difference
   - `pentagonColoring` - Edge coloring of K_5 where red = adjacent in cycle, blue = non-adjacent

2. **No monochromatic triangles**
   - `pentagon_no_red_triangle_at` - No red triangle at any triple of vertices (exhaustive)
   - `pentagon_no_blue_triangle_at` - No blue triangle at any triple of vertices (exhaustive)
   - `pentagon_no_red_clique` - Pentagon coloring has no red 3-clique
   - `pentagon_no_blue_clique` - Pentagon coloring has no blue 3-clique

3. **Lower bound theorems**
   - `ramsey_3_3_lower_bound` - ¬HasRamseyProperty (Fin 5) 3 3
   - `ramsey_3_3_lower` - Same (alias)
   - `ramsey_3_3_at_least_6` - Existence form: ∃ coloring with no monochromatic triangle

### Key Mathematical Insight

The **pentagon coloring** (also known as the Paley graph construction for 5) is:
- Red edges: (0,1), (1,2), (2,3), (3,4), (4,0) - a 5-cycle
- Blue edges: (0,2), (0,3), (1,3), (1,4), (2,4) - another 5-cycle (complement)

Both red and blue graphs form cycles of length 5, and 5-cycles have no triangles.
This is verified by exhaustive case analysis using `fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all`.

### Combined Result

With existing theorems:
- `ramseyBound 3 3 = 6` (upper bound: R(3,3) ≤ 6)
- `ramsey_3_3_lower_bound` (lower bound: R(3,3) > 5)

We have **R(3,3) = 6 exactly**.

## Session Log

### 2026-01-01 Session 1 (Research Iteration)

**Mode**: FRESH
**Problem**: ramsey-lower-bounds
**Prior Status**: available

**What we did**:
1. Selected from 5 available problems based on tractability
2. Read existing RamseysTheorem.lean to understand infrastructure
3. Implemented pentagon coloring construction
4. Proved symmetry lemma for absolute difference
5. Proved no red triangle at any triple (exhaustive)
6. Proved no blue triangle at any triple (exhaustive)
7. Combined into ramsey_3_3_lower_bound theorem
8. Added alternate formulations (ramsey_3_3_lower, ramsey_3_3_at_least_6)

**Literature reviewed**:
- [Mathlib SimpleGraph.Clique documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Clique.html)
- Pentagon coloring is classical construction (Paley graph for q=5)

**Key insight**:
The proof strategy is to define the coloring explicitly and verify by exhaustive case analysis that no monochromatic triangle exists. For Fin 5, this means checking all C(5,3) = 10 triples. The `fin_cases` tactic handles this automatically.

**New definitions/theorems**:
- `absDiff5` - absolute difference helper
- `absDiff5_symm` - symmetry lemma
- `pentagonColoring` - the explicit 2-coloring
- `pentagonColorAt` - point-wise accessor
- `isRedTriangle`, `isBlueTriangle` - triangle predicates
- `pentagon_no_red_triangle_at` - no red triangle (exhaustive)
- `pentagon_no_blue_triangle_at` - no blue triangle (exhaustive)
- `pentagon_no_red_clique` - no red 3-clique
- `pentagon_no_blue_clique` - no blue 3-clique
- `ramsey_3_3_lower_bound` - main lower bound
- `ramsey_3_3_lower` - alias
- `ramsey_3_3_at_least_6` - existence form

**Outcome**:
- RamseysTheorem.lean: ~602 lines (up from ~462)
- Added ~140 lines, 0 sorries
- File compiles successfully
- R(3,3) = 6 now fully established

**Files Modified**:
- `proofs/Proofs/RamseysTheorem.lean` (+140 lines)
- `research/candidate-pool.json` (status: completed)
- `research/problems/ramsey-lower-bounds/knowledge.md` - this file

**Next Steps**:
1. Could extend to R(3,4) = 9 with similar technique
2. Could add R(4,4) ≥ 18 (requires Paley graph of order 17)
3. General Ramsey lower bounds via probabilistic method (harder)

## Technical Notes

### Proof Strategy

1. Define coloring explicitly using `decide (condition)`
2. Prove symmetry `c.symm` using case analysis on ordering
3. Prove irreflexivity `c.irrefl` trivially (same vertex has diff = 0)
4. For no-triangle proofs, unfold definitions and use `fin_cases` + `simp_all`

### Why Pentagon Works

The pentagon is a **self-complementary** graph of odd order 5:
- It's 2-regular (each vertex has degree 2)
- Its complement is also 2-regular (each vertex has degree 2)
- Neither a cycle of length 5 nor its complement contains K_3

This is the unique 2-coloring (up to isomorphism) that avoids monochromatic K_3 on 5 vertices.

## File Location

`proofs/Proofs/RamseysTheorem.lean`
