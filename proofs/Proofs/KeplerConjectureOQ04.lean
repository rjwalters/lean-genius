/-
  Kepler Conjecture OQ-04: Non-spherical packing in ℝ³

  **Open question** (parent gallery `kepler-conjecture-oq-04`).
  The parent Kepler-Hales theorem (`Proofs.KeplerConjecture`) axiomatizes
  the optimal packing density for **congruent spheres** in ℝ³ as
  `π / (3√2) ≈ 0.7405` (the FCC density). This file scaffolds the
  natural generalisation to **other convex bodies**, where the optimal
  density is generally NOT `π / (3√2)`:

  1. **Tetrahedral packing.** Chen–Engel–Glotzer (2010) constructed a
     dimer-based packing of regular tetrahedra achieving density
     `δ ≥ 4000/4671 ≈ 0.8564`, *strictly above* the FCC sphere density
     `π/(3√2) ≈ 0.7405`. This refutes any naive expectation that the
     FCC bound is shape-universal — the tetrahedron beats the sphere
     by ~16 percentage points.
  2. **Ellipsoid packing.** Donev–Stillinger–Chaikin–Torquato (2004)
     showed dense random packings of ellipsoids achieve `δ ≈ 0.7707`
     at aspect ratio `α ≈ √2`. Bezdek–Kuperberg (2007) proved the
     lattice-only ellipsoid density equals `π/(3√2)` exactly.
  3. **Ulam's conjecture (1972, open).** Every symmetric convex body
     `K ⊂ ℝ³` satisfies the optimal density bound `δ_K ≥ π/(3√2)`,
     with equality only for the unit ball. The unit ball would be the
     LEAST dense convex body to pack — a striking inversion of the
     Kepler optimality intuition.

  **S2 SCAFFOLD goal.** Introduce the tetrahedral dimer density as a
  named real-number constant, prove the basic positivity / less-than-one
  bounds (axiom-free, `norm_num`-discharged), and prepare the API
  surface for the S3 numerical inequality `tetrahedronDimerDensity >
  fccDensity` (refutes shape-universality of the sphere bound).

  The S3 inequality is a pure real-number computation:
    `4000 / 4671 > π / (3 * Real.sqrt 2)`
  ↔ `12000 * Real.sqrt 2 > 4671 * π`  (both sides positive)
  ⇐ `(12000)² · 2 > 4671² · π²`        (square — both sides positive)
  ↔ `288_000_000 > 21_818_241 · π²`
  ↔ `π² < 288_000_000 / 21_818_241 ≈ 13.2002`

  which is comfortably satisfied by `Real.pi_lt_315` (`π < 3.15`, so
  `π² < 9.9225 < 13.2002`). No new axioms needed.

  **Status of this file.**
  - 0 sorries, 0 axioms.
  - One definition (`tetrahedronDimerDensity`).
  - Three basic theorems: positivity, less-than-one, and the
    Chen–Engel–Glotzer literature anchor as a `decide`-checked
    rational inequality.
  - S3 deferred: the `tetrahedronDimerDensity > fccDensity` numerical
    inequality (target ~50 lines using `Real.pi_lt_315` and `Real.sq_sqrt`).
-/

import Mathlib
import Proofs.KeplerConjecture

namespace KeplerConjectureOQ04

open Real KeplerConjecture

/--
**Chen–Engel–Glotzer dimer packing density for regular tetrahedra in ℝ³**
(Chen, Engel, Glotzer, "Dense crystalline dimer packings of regular
tetrahedra", *Discrete & Computational Geometry* 44 (2010), 253–280).

This rational constant — `4000 / 4671 ≈ 0.8564` — is the density
achieved by the explicit dimer-based crystalline arrangement, and is
the best lower bound known for the regular-tetrahedron packing density
in ℝ³ as of the 2010 construction. (The exact optimal density for
tetrahedra remains an open problem.)

**Key observation** (Tactic S3, deferred): this value *strictly exceeds*
the FCC sphere density `π / (3 √ 2) ≈ 0.7405` (`fccDensity` in
`Proofs.KeplerConjecture`), refuting any naive expectation that the
Kepler upper bound is shape-universal.
-/
noncomputable def tetrahedronDimerDensity : ℝ := 4000 / 4671

/--
The Chen–Engel–Glotzer tetrahedron dimer density is positive.

This is the simplest positivity guarantee: the density is a strictly
positive rational, so its image in `ℝ` is positive.
-/
theorem tetrahedronDimerDensity_pos : 0 < tetrahedronDimerDensity := by
  unfold tetrahedronDimerDensity
  norm_num

/--
The Chen–Engel–Glotzer tetrahedron dimer density is strictly less
than one.

Like any meaningful packing density, the tetrahedron dimer density
lies in the open unit interval `(0, 1)`. This bound is rational and
discharged by `norm_num`.
-/
theorem tetrahedronDimerDensity_lt_one : tetrahedronDimerDensity < 1 := by
  unfold tetrahedronDimerDensity
  norm_num

/--
**Chen–Engel–Glotzer literature anchor (rational form).**

The exact dimer density `4000 / 4671` strictly exceeds the rational
under-approximation `0.8563` (to four decimal places). This anchors
the Chen–Engel–Glotzer 2010 literature claim of "approximately
85.6% density" as a Lean-checked numerical fact, independent of any
reference to `π` or `Real.sqrt 2`.

Numerically: `4000 / 4671 ≈ 0.856347676…`, comfortably above `0.8563`.
The S3 inequality `tetrahedronDimerDensity > fccDensity` will use this
bound as a structural pivot: `fccDensity = π/(3√2) ≈ 0.7405 < 0.8563`,
so `tetrahedronDimerDensity > 0.8563 > fccDensity`, modulo the
upper-bound side `fccDensity < 0.8563` (a separate numerical lemma).
-/
theorem tetrahedronDimerDensity_gt_8563 :
    (8563 : ℝ) / 10000 < tetrahedronDimerDensity := by
  unfold tetrahedronDimerDensity
  norm_num

end KeplerConjectureOQ04
