# Research Knowledge: erdos-662

## Problem
Erdős #662: Distances in Separated Point Sets (Erdős–Lovász–Vesztergombi).
Triangular lattice maximality conjecture for pair distances.

## Session 2026-03-26 (Session 1) - Axiom Elimination

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Replaced `triangularLatticeCount` axiom with computable definition
  - Defined `triLatticeNorm` (a² + ab + b²) and `triLatticeCountInt` (decidable counting)
  - `triangularLatticeCount t = triLatticeCountInt ⌊t²⌋₊`
- Proved `triLatticeCountInt_one = 6` by `native_decide`
- Proved `triLatticeCountInt_three = 12` by `native_decide`
- Proved `triLattice_nearest_neighbors` (f(1) = 6) via reduction
- Proved `triLattice_second_shell` (f(√3) = 12) via reduction

### Stats Change
| Metric | Before | After |
|--------|--------|-------|
| Axioms | 3 | **2** |
| Sorries | 2 | **0** |
| Theorems | 5 | **9** |
| Lines | 109 | 164 |

### Key Findings
- All lattice norms are integers, so f(t) = countInt ⌊t²⌋₊
- `native_decide` handles enumeration of lattice points efficiently
- Remaining axiom `unit_neighbor_bound` (2D kissing number ≤ 6) is provable via angular packing argument but requires Mathlib angle/trig infrastructure

### Next Steps
- Prove `unit_neighbor_bound` via angular packing (min angle π/3, at most 6 fit in 2π)
- The main conjecture `erdos_662_lattice_optimal` remains open
