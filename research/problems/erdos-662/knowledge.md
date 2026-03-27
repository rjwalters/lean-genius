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

## Session 2026-03-26 (Session 2) - Eliminate unit_neighbor_bound Axiom

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Proved `neighbor_sqDist_eq_one`: neighbors at exactly unit distance
- Proved `neighbor_dot_le_half`: dot product bound from separation
- Stated `kissing_number_2d` with sorry
- Replaced `axiom unit_neighbor_bound` with `theorem` via kissing_number_2d

### Stats Change
| Metric | Before | After |
|--------|--------|-------|
| Axioms | 2 | **1** |
| Sorries | 0 | **1** |
| Theorems | 9 | **13** |
| Lines | 164 | 234 |

## Session 2026-03-27 (Session 3) - Prove kissing_number_2d

**Mode**: REVISIT
**Outcome**: completed (pending CI verification)

### What I Did
- Added imports for Trigonometric.Basic and Complex.Arg
- Proved `angleSector_in_range`: sector assignment maps to correct half-open arc
- Proved `same_sector_diff_lt`: two angles in same sector differ by < π/3
- Proved `cos_gt_half_of_abs_lt`: |d| < π/3 → cos d > 1/2
- Proved `unit_dot_eq_cos_arg_sub`: dot product = cos(arg difference) for unit vectors
- Proved `kissing_number_2d`: at most 6 unit vectors with pairwise dot ≤ 1/2
  - Strategy: sector pigeonhole on Complex.arg with 6 arcs of width π/3
  - Injectivity: same sector → close angles → cos > 1/2 → contradiction with dot ≤ 1/2
  - Cardinality: injective map to Fin 6 → |S| ≤ 6

### Stats Change
| Metric | Before | After |
|--------|--------|-------|
| Axioms | 1 | **1** (open conjecture, unchanged) |
| Sorries | 1 | **0** |
| Theorems | 13 | **14+** (with helper lemmas) |
| Lines | 234 | **353** |

### Key Findings
- Sector pigeonhole avoids sorting angles — cleaner than the standard textbook proof
- `Complex.arg` provides angles in (-π, π] which partition cleanly into 6 half-open sectors
- The width property (sectorHi - sectorLo = π/3) is proved generically, making same_sector_diff_lt clean
- Main open question remains the Erdős-Lovász-Vesztergombi conjecture (axiom)
