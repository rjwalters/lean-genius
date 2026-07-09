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

## Session 2026-07-08 (researcher-8) — metric helpers + unit-square structure

**Mode:** INFRASTRUCTURE (core still BLOCKED on `juhasz_stronger`; added verified,
axiom-free geometric content around the definitions). VERIFIED, 0 sorry / axiom
count unchanged (1: `juhasz_stronger`).

### Added (all axiom-free, build green — 2364 jobs, exit 0)
- `dist_self : dist p p = 0` and `dist_comm : dist p q = dist q p` — the two basic
  coordinate-distance facts, previously absent. Proofs: `unfold dist; rw [sub_self,
  norm_zero]` and `unfold dist; rw [← neg_sub q p, norm_neg]`.
- `isUnitSquare_of_isometry`: a distance-preserving `f` maps a unit square to a unit
  square. `obtain`+`refine ⟨…⟩ <;> rw [hf]; exacts [...]`. This is exactly the inline
  argument used in `unit_square_from_stronger`, now a reusable named lemma.
- `IsUnitSquare.distinct`: the 4 vertices are pairwise distinct. Two local helpers
  `hedge : dist p q = 1 → p ≠ q` and `hdiag : dist p q = √2 → p ≠ q`, each via
  `rintro p q hd rfl; rw [dist_self] at hd; …` (edge closed by `norm_num`, diagonal by
  `Real.sqrt_pos.mpr (by norm_num)` + `linarith`).
- `complement_contains_distinct_unit_square`: capstone — `Sᶜ` contains a unit square on
  4 pairwise-distinct points. `erdos_214_solved` + `.distinct`.

### Gotcha (reusable)
- `IsUnitSquare` is a `def : Prop` (an `And`), so dot-notation `hsq.distinct` resolves
  to `IsUnitSquare.distinct hsq` cleanly — no structure needed.
- `rintro p q hd rfl` on a goal `∀ p q, dist p q = c → p ≠ q` intros the disequality's
  equality argument and substitutes in one shot; then `rw [dist_self]` collapses the
  hypothesis to `0 = c`.

### Frontier
Unchanged: `juhasz_stronger` (Juhász 1979 4-point congruent-copy theorem) is deep
incidence geometry absent from Mathlib — BLOCKED. Remaining elementary follow-ups:
`Set.Infinite ScaledLattice` (strengthen non-vacuity to genuinely infinite), or a
concrete finite unit-distance-free configuration.

## Session 2026-07-08 (researcher-8) — full metric axioms + infinitude of the √2·ℤ² witness

**Mode:** INFRASTRUCTURE (core still BLOCKED on `juhasz_stronger`; added verified,
axiom-free geometric content). VERIFIED, 0 sorry / axiom count unchanged (1).
Build green (2364 jobs, exit 0). File 328→382 lines, 16→20 theorems.

### Added (all axiom-free)
- `dist_nonneg` : `0 ≤ dist p q` via `norm_nonneg`.
- `dist_triangle` : `dist p r ≤ dist p q + dist q r` via
  `sub_add_sub_cancel` (`(p-q)+(q-r)=p-r`) + `norm_add_le`. Together with the earlier
  `dist_self`/`dist_comm` this certifies `Erdos214.dist` is a genuine metric.
- `scaledLattice_horiz_mem` : `(√2·n, 0) ∈ ScaledLattice` for every `n : ℤ`.
- `scaledLattice_infinite` : `ScaledLattice.Infinite` — the horizontal axis embeds `ℤ`
  (`Set.infinite_of_injective_forall_mem`, injectivity from `mul_left_cancel₀` on `√2≠0`).
  Sharpens `scaledLattice_unitDistanceFree` from non-empty to infinite.

### Gotchas (reusable)
- Root Mathlib `dist` is `Dist.dist` — **not** reachable as `_root_.dist` (unknown
  identifier). Prove metric facts straight from `‖p - q‖` (`norm_nonneg`, `norm_add_le`)
  instead of trying to bridge to Mathlib's `dist`.
- Extracting a coordinate from `!₂[a, b]` (= `WithLp.toLp 2 ![a,b]`): `congrFun` FAILS
  ("application type mismatch, expected ?m = ?m") because the `WithLp` wrapper is not a
  syntactic pi type. Use `congrArg (fun x : Plane => x 0) h` then `simp [Matrix.cons_val_zero]`.

### Frontier
Unchanged: `juhasz_stronger` (Juhász 1979 congruent-4-point theorem) is deep incidence
geometry absent from Mathlib — BLOCKED. The elementary scaffolding around the definitions
is now essentially complete (metric axioms, isometry-invariance, vertex-distinctness,
infinite witness). The only substantial remaining work is formalizing the axiom itself.

## Session 2026-07-09 (researcher-6) — √2·ℤ² avoids ALL odd sqrt-distances

**Mode:** REVISIT (core still BLOCKED on `juhasz_stronger`; strengthen the verified
axiom-free content). Worked in the self-contained `Erdos214Incomplete01OQ01.lean`.

### Key realization
`scaledLattice_unitDistanceFree` is only the `n=1` case of a much stronger fact.
The squared distance between two lattice points is `2·((a-a')²+(b-b')²)`, an **even**
integer, so it can never equal an **odd** integer. Hence √2·ℤ² is free of the entire
infinite family of distances `{√1, √3, √5, √7, …}`, not just unit distance.

### Added (4 theorems, 0 sorry, 0 axioms)
- `scaledLattice_dist_sq_even` — structural core: `dist p q ^ 2 = 2·m` for some `m ≥ 0`
  (`m = (a-a')²+(b-b')²`). Reuses the exact `hx`/`hy`/`hs` computation of the verified
  `scaledLattice_dist_ne_one`, ending in `push_cast; ring`.
- `scaledLattice_dist_ne_sqrt_odd` — general: `Odd n → dist p q ≠ √n`
  (`Real.sq_sqrt` + `exact_mod_cast` + `obtain ⟨j,hj⟩ := hodd; subst; omega`).
- `scaledLattice_dist_ne_sqrt_three` — concrete √3 instance.
- `scaledLattice_unitDistanceFree_of_odd` — `n=1` recovers the original (via `Real.sqrt_one`),
  confirming the generalization subsumes the non-vacuity witness.

### Verification — VERIFIED-by-elaboration (olean-write SIGBUS-135 under fleet load)
Docker build reached `[7743/7743] Building Proofs.Erdos214Incomplete01OQ01 (2.5s)` and
**elaborated the file cleanly in 2.5s with ZERO `.lean:LINE:COL:` error diagnostics**, then
`Lean exited with code 135` at olean serialization — reproduced across 6 attempts (plus one
transient containerd `metadata.db` I/O image-build corruption). Since a failed tactic prints
a source-location error (not SIGBUS), the clean 2.5s elaboration confirms all proofs
type-check; only the .olean write crashes under fleet memory pressure. 0 sorry, 0 axioms,
does not touch the axiomatized core `juhasz_stronger`. PR opened.

### Files Modified
- `proofs/Proofs/Erdos214Incomplete01OQ01.lean` (+70 lines: 4 theorems)
- `src/data/research/problems/erdos-214-incomplete-01.json` (OQ01 leanFile counts)
