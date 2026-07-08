# Knowledge: erdos-214-incomplete-01

## Overview

Gallery entry `erdos-214` (Erdős #214: unit-distance-free sets & unit squares).
Juhász (1979) proved the complement of any unit-distance-free set contains a
congruent copy of any 4-point configuration (hence a unit square). The Lean entry
formalises the reduction from the stronger 4-point theorem; the deep theorem itself
is the single axiom `juhasz_stronger`.

## Status (researcher-3, 2026-07-08)

- **File was BROKEN on main** (parse error from an orphaned `/--` doc-comment at
  L71). Repaired → now builds. 0 sorries, 1 axiom.
- Added `dist_sq` (coordinate distance) and `scaledLattice_unitDistanceFree`
  (√2·ℤ² is unit-distance-free — non-vacuity witness).

## Key facts / techniques

- `Plane := EuclideanSpace ℝ (Fin 2)`; `dist p q := ‖p-q‖`.
- Coordinate distance: `unfold dist; rw [← dist_eq_norm, EuclideanSpace.dist_eq,
  Fin.sum_univ_two]; simp only [Real.dist_eq, sq_abs]` gives
  `√((p 0 - q 0)^2 + (p 1 - q 1)^2)`.
- `√2·ℤ²` unit-distance-free: dist² = `2·m`, m = (Δa)²+(Δb)² ∈ ℤ≥0; `2m=1` has no
  integer solution (`omega` after `exact_mod_cast`). Fold `2·m` as an `Int` cast in
  the `hX` equality, prove via `push_cast; nlinarith [Real.mul_self_sqrt …]`.
- ★ELABORATOR CRASH: the `ring`-based `hfac`+two-step-`rw` version SIGBUS'd (exit
  135). The single-`hX`-equality + `push_cast; nlinarith` version is crash-free.
- `Real.sqrt_eq_one : √x = 1 ↔ x = 1`; `Real.mul_self_sqrt (0≤x) : √x*√x = x`.

## Blockers

- `juhasz_stronger` (Juhász 1979 4-point theorem): deep incidence geometry, not in
  Mathlib. BLOCKED.

## References

- Lean: `proofs/Proofs/Erdos214Problem.lean` (namespace `Erdos214`)
- [Ju79] Juhász (1979); [Er83c] Erdős (1983)
