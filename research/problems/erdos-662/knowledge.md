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

## Session 2026-03-26 (Session 2) - Eliminate unit_neighbor_bound Axiom

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Proved `neighbor_sqDist_eq_one`: all unit neighbors are at exactly unit distance
  - From neighbors def (sqDist ≤ 1) + separation (sqDist ≥ 1) → sqDist = 1
- Proved `neighbor_dot_le_half`: dot product of translated neighbors ≤ 1/2
  - Key identity: sqDist(q₁,q₂) = 2 - 2·dot, so dot ≤ 1/2 from separation
  - Proved using ring + linarith
- Stated `kissing_number_2d`: at most 6 unit vectors with pairwise dot ≤ 1/2
  - Left with sorry — needs angular packing argument
  - Proof strategy documented: uses Real.cos_sub, cos_pi_div_three, strictAntiOn_cos
- Replaced `axiom unit_neighbor_bound` with `theorem unit_neighbor_bound`
  - Wired via translation to kissing_number_2d

### Stats Change
| Metric | Before | After |
|--------|--------|-------|
| Axioms | 2 | **1** |
| Sorries | 0 | **1** |
| Theorems | 9 | **13** |
| Lines | 164 | 234 |

### Key Findings
- Neighbors are on the unit circle (sqDist = 1) — key geometric reduction
- Dot product bound follows from algebraic identity, no trig needed
- kissing_number_2d is the clean combinatorial core — purely about unit vectors
- Mathlib has all needed trig lemmas: cos_pi_div_three, cos_sub, strictAntiOn_cos

### Next Steps
- Prove kissing_number_2d via angular packing (good Aristotle candidate)
- The main conjecture `erdos_662_lattice_optimal` remains open (unprovable)

## Session 2026-03-27 (Session 3) - Gallery Metadata Update & Completion

**Mode**: REVISIT
**Outcome**: completed

### What I Did
- Verified file state: 0 sorries, 1 axiom (erdos_662_lattice_optimal — the main OPEN conjecture)
- kissing_number_2d was already fully proved (angular sector pigeonhole via Complex.arg)
- Updated gallery meta.json:
  - leanFile section: corrected lineCount (108→375), axiomCount (3→1), theoremCount (5→9), lemmaCount (0→10), defCount (2→10), added missing import
  - sections array: updated all line ranges, added 3 new sections (geometric-reductions, kissing-number-helpers, kissing-number) to reflect the full proof structure
  - proofStrategy: updated to describe the complete kissing number proof
- Updated research problem JSON: leanFiles stats, progress summary, cleared blockers

### Stats (Final)
| Metric | Value |
|--------|-------|
| Axioms | **1** (open conjecture only) |
| Sorries | **0** |
| Theorems | 9 (public) |
| Lemmas | 10 (private) |
| Definitions | 10 |
| Lines | 375 |

### Key Status
- **Formalization is at maximum potential**: all provable parts are fully machine-checked
- **The only axiom** is `erdos_662_lattice_optimal` — the main open conjecture, which cannot be proved
- **kissing_number_2d** is a clean, self-contained theorem that could be contributed to Mathlib
- **contact_number_3n** resolves the t=1 case of the conjecture completely
