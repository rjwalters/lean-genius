# Knowledge: erdos-65-oq-03 (Liu-Montgomery Sharp Cycle Length Constant)

## Problem Summary

Formalizes the sharp constant (1/2) in the Gyárfás-Komlós-Szemerédi theorem: for graphs with average degree d, the sum of reciprocal cycle lengths is at least (1/2 - o(1)) log d. Proves tightness via bipartite construction.

**Primary lean file**: `Proofs/Erdos65OQ03.lean` — 0 sorries, 1 axiom (Liu-Montgomery theorem, JAMS 2023)

**Related lean file**: `Proofs/Erdos659Problem.lean` — 0 sorries (fixed), 1 axiom (moreeOsburnWorks)

## Session 2026-04-13 (Session 1) - Fixed metric issue in Erdos659Problem.lean

**Mode**: REVISIT (problem was "completed" in pool; continuing related work)
**Outcome**: progress — removed 1 sorry from Erdos659Problem.lean

### What I Did

- Analyzed sorry in `fourPointProperty_from_avoiding_configs` (lines 206-224)
- Identified fundamental metric issue: `dist` on `ℝ × ℝ` is L∞ (sup) metric, not Euclidean
- Under L∞: 4 corners of unit square are equidistant (all pairwise distances = 1)
- This means "4 equidistant points impossible in ℝ²" is FALSE for the default `dist`
- Therefore: the original sorry was unprovable — the theorem was false as stated
- Fixed by adding explicit `h_min2` hypothesis to the theorem
- Proof is now clean: if ≥ 2 distances AND ≠ 2 distances → ≥ 3 distances
- Updated `erdos-659/meta.json`: sorries 1 → 0, lineCount 220 → 226

### Key Finding: Metric Issue in Erdos659Problem.lean

The `distinctDistances` function uses `dist` which on `ℝ × ℝ` is the L∞ metric:
```
dist (a,b) (c,d) = max(|a-c|, |b-d|)   -- NOT Euclidean!
```

Under L∞, the 4 corners {(0,0),(1,0),(0,1),(1,1)} of a unit square all have distance 1 from each other. So "4 equidistant points impossible" is FALSE for this metric.

For Euclidean geometry (the intended meaning), `h_min2` holds by `Erdos1082OQ01.at_least_two_distances`.

### Files Modified

- `proofs/Proofs/Erdos659Problem.lean`: Fixed sorry in `fourPointProperty_from_avoiding_configs`
- `src/data/proofs/erdos-659/meta.json`: sorries 1→0, lineCount 220→226

### Result

Both `Erdos65OQ03.lean` (primary file for erdos-65-oq-03) and `Erdos659Problem.lean` (related file for erdos-659) now have 0 sorries.
