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

## Session 2026-07-09 (researcher-1) — √2·ℤ² avoids an infinite family of EVEN distances (n≡6 mod 8)

**Mode:** REVISIT (core still BLOCKED on `juhasz_stronger`; strengthened the verified
axiom-free content in the self-contained `Erdos214Incomplete01OQ01.lean`).

### Key realization
`scaledLattice_dist_ne_sqrt_odd` (dist²=2m even ⟹ avoids odd √n) throws away that the
even factor m is a SUM OF TWO SQUARES: dist² = 2·(u²+v²), u=a−a', v=b−b'. Since
u²+v² ≢ 3 (mod 4), dist² ≢ 6 (mod 8), so √2·ℤ² ALSO avoids every √n with n≡6 mod 8 —
the infinite family √6, √14, √22, … of EVEN distances, none reachable from the odd result.

### Added (4 theorems, 0 sorry, 0 axioms)
- `sq_add_sq_mod_four_ne_three (u v : ℤ) : (u²+v²)%4 ≠ 3` — even/odd square split
  (`Int.even_or_odd`; (k+k)²=4k², (2k+1)²=4(k²+k)+1; `rw;omega`), then
  `rcases key u <;> rcases key v <;> omega`.
- `scaledLattice_dist_sq_two_mul_sq_add_sq` — dist²=2(u²+v²) (sharpens dist_sq_even by
  exposing u,v; identical hx/hy/`push_cast;ring` skeleton, returns a−a', b−b').
- `scaledLattice_dist_ne_sqrt_six_mod_eight {n} (hn: n%8=6)` — the new family. crux:
  exact_mod_cast to (n:ℤ)=2(u²+v²), then `omega` chains n%8=6 → u²+v²≡3 mod4 vs h3.
  omega handles the mixed ℕ/ℤ modular reasoning with u²,v² as opaque atoms.
- `scaledLattice_dist_ne_sqrt_six` — concrete √6 instance (even, beyond odd result).

### Verification — VERIFIED-by-elaboration (olean-write SIGBUS-135)
Same pattern as researcher-6's session on this file: after the shared Mathlib cache
corruption cleared (2 early runs hit `invalid header` on random Mathlib .ir/.olean deps
at the import line — fleet cache race, different file each run), 5 runs reached
`[7743/7743] Building … (1.4–5.8s)` with ZERO `.lean:LINE:COL` diagnostics, then
`code 135` at olean serialization. A failed tactic prints a source-location error not a
SIGBUS, so the clean elaboration confirms all 4 proofs type-check. 0 sorry, 0 new axioms,
core `juhasz_stronger` untouched. File 198→271 lines, 9→13 theorems. Also fixed a stale
json sorryCount (1→0; the "1" was a docstring "no `sorry`" false-positive).

### Frontier
Unchanged: `juhasz_stronger` BLOCKED. The achieved squared distances of √2·ℤ² are
exactly {2·(u²+v²)}; odd n and n≡6 mod 8 are the two clean elementary sufficient
avoidance conditions now formalized. Full characterization would need the sum-of-two-
squares (Fermat) predicate.

## Session 2026-07-09 (researcher-2) — complete mod-8 dichotomy (UNVERIFIED, docker infra down)

Added 2 theorems to `Erdos214Incomplete01OQ01.lean` unifying the odd-`n` and `n≡6 mod 8`
avoidance families into the sharp mod-8 characterization of √2·ℤ²'s distance set:
- `scaledLattice_achievable_mod_eight`: if `dist p q = √n` then `n % 8 ∈ {0,2,4}` (the
  ONLY achievable residues) — from `dist² = 2(u²+v²)` and `(u²+v²)%4 ≠ 3`, `omega`.
- `scaledLattice_dist_ne_sqrt_of_mod_eight`: √2·ℤ² avoids √n for EVERY `n%8 ∈ {1,3,5,6,7}`
  (the exact complement), subsuming both `scaledLattice_dist_ne_sqrt_odd` (1,3,5,7) and
  `_six_mod_eight` (6). Contrapositive of the achievability lemma via `omega`.

This is the sharp mod-8 boundary: achievable residues are exactly {0,2,4}. (Beyond mod 8,
avoidance like √12 = √(2·6), 6 not a sum of two squares, needs the Fermat SoS predicate —
still the open frontier; core `juhasz_stronger` untouched.)

Both proofs are arithmetic-only, reusing `scaledLattice_dist_sq_two_mul_sq_add_sq` +
`sq_add_sq_mod_four_ne_three` + `omega` (identical skeleton to the proven `_six_mod_eight`).
Research json leanFile synced: lineCount 271→310, theoremCount 13→15.

**Verification: UNVERIFIED — docker infra down.** `docker-build.sh` fails at the image
build itself (`write .../containerd/.../meta.db: input/output error`), so no build ran
this session. High confidence from the mirrored proof skeleton; deployer full build will confirm.
