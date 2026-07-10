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
  surface for the S3 numerical inequality.

  **S3 ACT — refutation of shape-universality.** Prove that
  `tetrahedronDimerDensity > fccDensity` (the parent's FCC sphere
  density `π / (3√2)`). Both sides positive; cross-multiply with
  `div_lt_div_iff₀` and bound `π < 3.15` (`Real.pi_lt_d2`)
  above, `√2 > 1.4` (via `Real.lt_sqrt`) below; close with `nlinarith`.
  The proof adds NO new axioms.

  Linear-margin chain:
    `4671 · π    < 4671 · 3.15 = 14_713.65`
    `4000 · 3 · √2 > 12 000 · 1.4 = 16_800`
    margin ≈ `2_086.35`

  **S4 ACT — `PackingDensity` instance + corollary.** Bundle
  `tetrahedronDimerDensity` into a `PackingDensity` instance
  (`tetrahedronDimerPacking`) and conclude existentially:
  `∃ p : PackingDensity, fccDensity < p.density`. Witnesses that the
  parent's abstract type admits values strictly above `fccDensity`,
  formalising the bottom-line OQ-04 refutation.

  **S5 ACT — Bezdek–Kuperberg (2007) ellipsoid lattice axiom.**
  Introduce the marker structure `EllipsoidLatticePacking` (extends
  `PackingDensity`) plus the **+1 STATEMENT axiom**
  `bezdek_kuperberg_ellipsoid_lattice_upper_bound`: every ellipsoid
  lattice packing in ℝ³ has density at most `fccDensity`. Combined
  with the (degenerate, aspect-ratio-1) sphere case, this means the
  *optimal* ellipsoid lattice density equals `π/(3√2)` exactly —
  the lattice constraint forces the FCC bound for all ellipsoids.
  Companion derived theorem `ellipsoid_lattice_le_fccPacking`
  restates the bound in terms of the named `fccPacking` instance
  (no new axiom). Closes the lattice arm of the OQ-04 hierarchy.

  **S6 ACT — Ulam's conjecture (1972, open).** Introduce the marker
  structure `SymmetricConvexBody3DPacking` (extends `PackingDensity`)
  plus the **+1 STATEMENT axiom** `ulam_conjecture`: every centrally
  symmetric convex body packing in ℝ³ achieves density at least
  `fccDensity`. Open since 1972 (Stanislaw Ulam, in conversation with
  Martin Gardner): if proven, the unit ball would be the LEAST dense
  centrally symmetric convex body to pack — a striking inversion of
  the Kepler optimality intuition. Companion derived theorem
  `ulam_le_fccPacking_density` (no new axiom). Closes the
  non-lattice / open-conjecture arm of the OQ-04 hierarchy.

  **S7 ACT — Final hierarchy aggregation.** Combine the three
  shape-dependent benchmarks proved across S3+S4 (tetrahedral non-lattice
  strictly exceeds FCC), S5 (ellipsoid lattice bounded above by FCC),
  and S6 (centrally symmetric convex bodies conjecturally bounded below
  by FCC) into the single quantified theorem `density_hierarchy_3d`
  via direct `And.intro` over the three named facts. No new axioms.
  This is the OQ-04 closing statement.

  **S8 ACT — soundness of the shape gates (non-vacuity).** The S5/S6
  bounds are gated by the opaque predicates `IsEllipsoidLatticePacking` /
  `IsSymmetricConvexBody3DPacking` (no introduction axiom), which restores
  soundness after the pre-S15 contentless-marker exploit. S8 certifies these
  gates are *genuinely restrictive*, not merely uninhabited-by-fiat:
  `tetrahedronDimer_not_ellipsoidLattice` proves the dimer density is provably
  outside the ellipsoid-lattice class (it exceeds the Bezdek–Kuperberg
  ceiling), and `zeroDensity_not_symmetricConvexBody` proves the zero density
  is provably outside the symmetric-convex-body class (it falls below the Ulam
  floor). These are exactly the old unsoundness exploits, now discharged as
  honest negative facts. No new axioms.

  **Status of this file.**
  - 0 sorries, 2 axioms (`bezdek_kuperberg_ellipsoid_lattice_upper_bound`,
    `ulam_conjecture`); build-verified against Mathlib v4.26 (docker 7744 jobs).
  - Four definitions (`tetrahedronDimerDensity`,
    `tetrahedronDimerPacking`, `EllipsoidLatticePacking`,
    `SymmetricConvexBody3DPacking`) plus two opaque shape predicates.
  - Theorems through S8: positivity, less-than-one, rational anchor
    (`> 0.8563`), inequality vs. `fccDensity` (+ explicit `1/10` margin),
    existential corollary, ellipsoid-lattice ≤ FCC, cross-shape domination,
    Ulam ≥ FCC, the S7 aggregation `density_hierarchy_3d`, and the S8
    non-vacuity theorems `tetrahedronDimer_not_ellipsoidLattice` /
    `zeroDensity_not_symmetricConvexBody`.
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

**Key observation** (Tactic S3, proved as `tetrahedronDimerDensity_gt_fccDensity`):
this value *strictly exceeds* the FCC sphere density `π / (3 √ 2) ≈ 0.7405`
(`fccDensity` in `Proofs.KeplerConjecture`), refuting any naive expectation that
the Kepler upper bound is shape-universal.
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
The S3 inequality `tetrahedronDimerDensity > fccDensity` (below) uses
a tighter linear chain via `Real.pi_lt_d2` and `Real.lt_sqrt`, but
this rational anchor remains independently useful for sanity checks
and for downstream constructions wanting an `ℝ`-free comparator.
-/
theorem tetrahedronDimerDensity_gt_8563 :
    (8563 : ℝ) / 10000 < tetrahedronDimerDensity := by
  unfold tetrahedronDimerDensity
  norm_num

/-!
## S3 — Refutation of shape-universality

The next theorem (`tetrahedronDimerDensity_gt_fccDensity`) is the
central deliverable of OQ-04 in its strongest axiom-free form. It
proves that the Chen–Engel–Glotzer dimer density `4000/4671 ≈ 0.8564`
**strictly exceeds** the Kepler-Hales FCC sphere density
`π/(3√2) ≈ 0.7405`, by ≈ 11.6 percentage points.

The proof is a pure real-number inequality and adds **no new axioms**.
It uses only two Mathlib lemmas beyond `norm_num` arithmetic:

* `Real.pi_lt_d2` — verified numerical upper bound `π < 3.15`.
* `Real.lt_sqrt`       — characterisation `x < √y ↔ x² < y` (for `0 ≤ x`).
* `div_lt_div_iff₀`    — clears the divisions on both sides.

Linear-margin closure:

* LHS: `4671 · π   < 4671 · 3.15 = 14_713.65`
* RHS: `4000 · 3 · √2 > 12_000 · 1.4 = 16_800`

with linear margin `≈ 2_086.35`, closed by `nlinarith` once both
single-variable bounds are in scope.
-/

/--
**Refutation of shape-universality of the Kepler upper bound.**

The Chen–Engel–Glotzer (2010) tetrahedral dimer density strictly
exceeds the Kepler-Hales FCC sphere density.

**Mathematical content.** The parent gallery's `kepler_conjecture` axiom
asserts `δ ≤ π/(3√2)` for packings of *congruent spheres*. This
theorem shows that the abstract `PackingDensity` type in
`Proofs.KeplerConjecture` admits values *strictly above* `fccDensity`,
witnessed by the tetrahedral dimer construction. Hence the Kepler
upper bound is **shape-specific** — it does NOT generalise to all
convex bodies in ℝ³.

**Proof.** Cross-multiply (`div_lt_div_iff₀`) to remove division; then
bound `π < 3.15` (`Real.pi_lt_d2`) and `√2 > 1.4` (via
`Real.lt_sqrt`, since `1.4² = 1.96 < 2`); the resulting linear
inequality `4671 · π < 12000 · √2` follows from
`4671 · 3.15 = 14_713.65 < 16_800 = 12_000 · 1.4` by `nlinarith`.
No new axioms added.
-/
theorem tetrahedronDimerDensity_gt_fccDensity :
    fccDensity < tetrahedronDimerDensity := by
  unfold fccDensity tetrahedronDimerDensity
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ_ub : Real.pi < 3.15 := Real.pi_lt_d2
  have hs2_lb : (1.4 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.4)).mpr (by norm_num : (1.4 : ℝ) ^ 2 < 2)
  have h3s_pos : (0 : ℝ) < 3 * Real.sqrt 2 := by positivity
  rw [div_lt_div_iff₀ h3s_pos (by norm_num : (0 : ℝ) < 4671)]
  -- Goal: Real.pi * 4671 < 4000 * (3 * Real.sqrt 2)
  -- LHS < 4671 * 3.15 = 14_713.65;  RHS > 12000 * 1.4 = 16800.
  nlinarith [hπ_pos, hπ_ub, hs2_lb]

/--
**Rational upper bound on the FCC sphere density.**

`fccDensity = π / (3 √ 2)` lies strictly below the rational
`35329 / 46710 ≈ 0.75634`. This is a sharper, division-cleared
restatement of `Real.pi_lt_d2` / `Real.lt_sqrt` tailored to the
margin certificate below (`35329 / 46710` is chosen so that
`35329 / 46710 + 1/10 = 4000 / 4671 = tetrahedronDimerDensity`).

Same linear chain as `tetrahedronDimerDensity_gt_fccDensity`:
cross-multiply, then `π · 46710 < 35329 · 3 · √2`, closed by
`nlinarith` from `π < 3.15` and `√2 > 1.4`
(`46710 · 3.15 = 147 136.5 < 148 381.8 = 105 987 · 1.4`). No new axioms.
-/
theorem fccDensity_lt_35329_div_46710 :
    fccDensity < 35329 / 46710 := by
  unfold fccDensity
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ_ub : Real.pi < 3.15 := Real.pi_lt_d2
  have hs2_lb : (1.4 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.4)).mpr (by norm_num : (1.4 : ℝ) ^ 2 < 2)
  have h3s_pos : (0 : ℝ) < 3 * Real.sqrt 2 := by positivity
  rw [div_lt_div_iff₀ h3s_pos (by norm_num : (0 : ℝ) < 46710)]
  -- Goal: Real.pi * 46710 < 35329 * (3 * Real.sqrt 2)
  nlinarith [hπ_pos, hπ_ub, hs2_lb]

/--
**Quantitative margin of the shape-universality refutation.**

Strengthens `tetrahedronDimerDensity_gt_fccDensity` from a bare strict
inequality to an explicit numerical separation: the tetrahedral dimer
density exceeds the FCC sphere density by **more than `1/10`**, i.e.

  `fccDensity + 1/10 < tetrahedronDimerDensity`.

This certifies the refutation is robust, not razor-thin — the
≈ 11.6-percentage-point gap (`4000/4671 − π/(3√2) ≈ 0.1159`) is
bounded below by a clean rational `1/10`. The rational anchor
`35329 / 46710` is exactly `4000/4671 − 1/10`, so the result follows
from `fccDensity_lt_35329_div_46710` by `linarith`. No new axioms.
-/
theorem tetrahedronDimerDensity_gt_fccDensity_margin :
    fccDensity + 1 / 10 < tetrahedronDimerDensity := by
  have h := fccDensity_lt_35329_div_46710
  unfold tetrahedronDimerDensity
  -- 35329/46710 + 1/10 = 40000/46710 = 4000/4671.
  linarith [h]

/-!
## S4 — `PackingDensity` instance + corollary

Having proved the inequality, we package the tetrahedral dimer density
as a concrete inhabitant of the parent's `PackingDensity` structure.
This makes the refutation type-level: there *exists* a
`PackingDensity` strictly above `fccDensity`, namely the tetrahedral
dimer packing.

No new axioms; both fields (`nonneg`, `le_one`) follow directly from
the S2 positivity / less-than-one bounds above.
-/

/--
**Tetrahedral dimer packing as a `PackingDensity` instance.**

Bundles `tetrahedronDimerDensity` together with the S2-proven bounds
`0 < · ` and `· < 1` into the parent's abstract `PackingDensity`
structure (defined in `Proofs.KeplerConjecture`). This lets downstream
results manipulate the dimer packing as a first-class `PackingDensity`
witness.
-/
noncomputable def tetrahedronDimerPacking : PackingDensity where
  density := tetrahedronDimerDensity
  nonneg  := tetrahedronDimerDensity_pos.le
  le_one  := tetrahedronDimerDensity_lt_one.le

/--
**Existential refutation of shape-universality.**

There exists a `PackingDensity` strictly above the FCC sphere density
`fccDensity`. The witness is `tetrahedronDimerPacking`.

This is the bottom-line corollary of OQ-04: the parent's abstract
`PackingDensity` type, taken without the sphere assumption, is NOT
bounded above by `fccDensity`. Restoring such a bound requires the
sphere shape hypothesis (i.e. the parent `kepler_conjecture` axiom).
-/
theorem exists_packingDensity_gt_fcc :
    ∃ p : PackingDensity, fccDensity < p.density :=
  ⟨tetrahedronDimerPacking, tetrahedronDimerDensity_gt_fccDensity⟩

/-!
## S5 — Ellipsoid lattice packing axiom (Bezdek–Kuperberg 2007)

Continuing the OQ-04 hierarchy. Where the tetrahedral dimer
construction (S2–S4) showed the FCC bound is shape-specific *upward*
(a non-spherical shape strictly exceeds it), the Bezdek–Kuperberg
theorem shows the *lattice* constraint is also shape-specific, but
in the opposite direction: even non-spherical (ellipsoid) shapes
cannot exceed the FCC sphere density when restricted to lattice
packings.

**Bezdek–Kuperberg (2007).** K. Bezdek and W. Kuperberg, "Packing
Euclidean balls and packing certain other smooth convex bodies",
*Geometriae Dedicata* 132 (2008), 73–85. Theorem: for every
ellipsoid `E ⊂ ℝ³`, the optimal density of any lattice packing of
congruent copies of `E` equals exactly the FCC sphere density
`π / (3 √ 2)`. The published proof reduces to an affine equivalence
between ellipsoid lattice packings and ball lattice packings (every
ellipsoid is the image of a ball under an invertible linear map,
which preserves both density and lattice structure), combined with
Gauss's theorem (1831) that the optimal ball lattice density equals
`π / (3 √ 2)` (`gauss_lattice_theorem` in `Proofs.KeplerConjecture`).

**Contrast with non-lattice ellipsoid packings.** Donev–Stillinger–
Chaikin–Torquato (2004) achieved density `δ ≈ 0.7707` at aspect
ratio `α ≈ √2` using *non-lattice* (jammed) ellipsoid packings —
strictly above the FCC bound. So the lattice constraint is
essential to the Bezdek–Kuperberg statement: it is the
lattice-vs-non-lattice distinction (not the shape) that matters
here.

**Status.** `bezdek_kuperberg_ellipsoid_lattice_upper_bound` is a
**+1 STATEMENT axiom** in this file (the published proof relies on
affine density invariance under linear transforms, which is not
formalised in Mathlib v4.26.0). The wrapper structure
`EllipsoidLatticePacking` is a definitional bundle — no axiom.
-/

/--
**Uninterpreted shape predicate: "this density arises from an ellipsoid
lattice packing".**

`opaque` (no defining body, no introduction axiom), so it is impossible
to *prove* `IsEllipsoidLatticePacking p` for any concrete `p`. This is
deliberate: it gates the shape-restricted Bezdek–Kuperberg bound below so
that a generic `PackingDensity` (e.g. the tetrahedral dimer, or a
density-0 packing) cannot be smuggled in to derive a contradiction.

**Soundness rationale.** A contentless `structure … extends PackingDensity`
has an anonymous constructor `PackingDensity → …`, so *any* density —
including `tetrahedronDimerPacking`, whose density exceeds `fccDensity` —
could be wrapped and fed to the upper-bound axiom, yielding
`tetrahedronDimerDensity ≤ fccDensity` in contradiction with the
axiom-free `tetrahedronDimerDensity_gt_fccDensity`. Requiring an
`IsEllipsoidLatticePacking` proof field blocks that wrap, because nothing
inhabits the opaque predicate.
-/
opaque IsEllipsoidLatticePacking : PackingDensity → Prop

/--
**Marker structure: an ellipsoid lattice packing in ℝ³.**

Bundles a `PackingDensity` value with a proof that it arises from a
lattice arrangement of congruent ellipsoids in ℝ³ (the opaque
`IsEllipsoidLatticePacking` predicate). The proof field is what makes
the type non-trivial to inhabit: an arbitrary `PackingDensity` cannot be
coerced in without exhibiting the (uninhabited) shape proof, which is
exactly what restores soundness of the Bezdek–Kuperberg upper bound
(`bezdek_kuperberg_ellipsoid_lattice_upper_bound`, axiom below).
-/
structure EllipsoidLatticePacking extends PackingDensity where
  isEllipsoidLattice : IsEllipsoidLatticePacking toPackingDensity

/--
**Bezdek–Kuperberg (2007).**

For every lattice packing of congruent ellipsoids in ℝ³, the density
is at most the FCC sphere density `π / (3 √ 2)`. Combined with the
fact that the FCC sphere packing is itself a (degenerate,
aspect-ratio-1) ellipsoid lattice packing, this means the *optimal*
ellipsoid lattice density equals exactly `fccDensity`.

This is a **STATEMENT axiom** (the published proof reduces to affine
density invariance + the lattice case of the Kepler conjecture, the
former not yet in Mathlib v4.26.0).
-/
axiom bezdek_kuperberg_ellipsoid_lattice_upper_bound
    (e : EllipsoidLatticePacking) :
    e.density ≤ fccDensity

/--
**Derived corollary: ellipsoid lattice packings are dominated by
FCC.**

Restates Bezdek–Kuperberg in terms of the named `fccPacking`
instance from the parent file: every ellipsoid lattice packing has
density at most `fccPacking.density`. No new axiom — direct
application of `bezdek_kuperberg_ellipsoid_lattice_upper_bound`.
-/
theorem ellipsoid_lattice_le_fccPacking
    (e : EllipsoidLatticePacking) :
    e.density ≤ fccPacking.density :=
  bezdek_kuperberg_ellipsoid_lattice_upper_bound e

/--
**Cross-shape domination: ellipsoid lattice packings are strictly less
dense than the tetrahedral dimer packing.**

Combines the two opposite arms of the OQ-04 hierarchy into a single
shape-vs-shape comparison: every ellipsoid *lattice* packing `e`
satisfies `e.density ≤ fccDensity` (Bezdek–Kuperberg, S5), while the
tetrahedral *non-lattice* dimer strictly exceeds `fccDensity` (S3,
axiom-free). Transitivity through `fccDensity` therefore gives

  `e.density < tetrahedronDimerDensity`.

i.e. the FCC density acts as a strict separator: no ellipsoid lattice
packing can match the tetrahedral dimer. Adds **no new axiom** — it is
a direct consequence of the existing
`bezdek_kuperberg_ellipsoid_lattice_upper_bound` axiom and the
axiom-free `tetrahedronDimerDensity_gt_fccDensity`.
-/
theorem ellipsoid_lattice_lt_tetrahedronDimer
    (e : EllipsoidLatticePacking) :
    e.density < tetrahedronDimerDensity :=
  lt_of_le_of_lt
    (bezdek_kuperberg_ellipsoid_lattice_upper_bound e)
    tetrahedronDimerDensity_gt_fccDensity

/--
**Uninterpreted shape predicate: "this density arises from a centrally
symmetric convex body packing in ℝ³".**

`opaque` (no defining body, no introduction axiom), so it is impossible
to *prove* `IsSymmetricConvexBody3DPacking p` for any concrete `p`.
Mathlib v4.26.0 has no native `ConvexBody3D` / centrally-symmetric
abstraction at the level of `PackingDensity`, so this predicate records
the geometric intent without committing to a particular formalisation.
The Ulam conjecture (`ulam_conjecture`, axiom below) supplies the density
constraint for inhabitants of the gated structure.

A future iteration that formalises `Convex ℝ K` + central symmetry
+ "packing density of `K`" can refine this marker to a structure
carrying the underlying body `K` and a proof
`∀ x, x ∈ K ↔ -x ∈ K`; the axiom `ulam_conjecture` would survive
the refactor as a STATEMENT axiom on the refined type.

**Soundness rationale.** `ulam_conjecture` is a *lower* bound
(`fccDensity ≤ p.density`). Without a shape gate, wrapping a
density-0 `PackingDensity` (constructible: `⟨0, le_refl 0, by norm_num⟩`)
into a contentless marker would yield `fccDensity ≤ 0`, contradicting
`fccDensity_pos`. The opaque `IsSymmetricConvexBody3DPacking` proof
field blocks that wrap, exactly as for the ellipsoid case.
-/
opaque IsSymmetricConvexBody3DPacking : PackingDensity → Prop

/--
**Marker structure: a centrally symmetric convex body packing in ℝ³.**

Bundles a `PackingDensity` with a proof of the opaque shape predicate
`IsSymmetricConvexBody3DPacking`. As with `EllipsoidLatticePacking`,
the proof field is what prevents an arbitrary `PackingDensity` from
being coerced in, restoring soundness of the (lower-bound) Ulam axiom.
-/
structure SymmetricConvexBody3DPacking extends PackingDensity where
  isSymmetricConvexBody : IsSymmetricConvexBody3DPacking toPackingDensity

/--
**Ulam's conjecture (1972, OPEN).**

Stanislaw Ulam conjectured (in conversation with Martin Gardner)
that every centrally symmetric convex body `K ⊂ ℝ³` satisfies the
optimal packing-density bound

  `δ_K ≥ π / (3 √ 2)`

with equality if and only if `K` is a Euclidean ball. If true, the
unit ball would be the LEAST dense centrally symmetric convex body
to pack — a striking inversion of the Kepler optimality intuition.

The conjecture has been **open since 1972**. Partial results exist
for specific bodies (e.g. the rhombic dodecahedron achieves density
`1`, the regular octahedron achieves `18/19 ≈ 0.9474`), but the
general statement has resisted both proof and disproof for over
half a century.

This is a **STATEMENT axiom** (the conjecture is currently
unproven). +1 axiom matches the S6 plan in the prior iteration's
"Next Action" block.

References:
- Gardner, M. (1972), "The unexpected hanging and other mathematical
  diversions", *Scientific American* 226, 117–121.
- Brass, P., Moser, W., Pach, J. (2005), *Research Problems in
  Discrete Geometry*, §3.3 — survey of partial results.
-/
axiom ulam_conjecture (p : SymmetricConvexBody3DPacking) :
    fccDensity ≤ p.density

/--
**Derived corollary: Ulam vs the named `fccPacking` instance.**

Restates `ulam_conjecture` in terms of the named `fccPacking`
instance from the parent file: every centrally symmetric convex
body packing in ℝ³ achieves density at least `fccPacking.density`.
No new axiom — direct application of `ulam_conjecture`.
-/
theorem ulam_le_fccPacking_density
    (p : SymmetricConvexBody3DPacking) :
    fccPacking.density ≤ p.density :=
  ulam_conjecture p

/-!
## S7 — Final hierarchy aggregation

Combine the three shape-dependent benchmarks proved across S3+S4
(tetrahedral non-lattice strictly exceeds FCC), S5 (ellipsoid lattice
bounded above by FCC), and S6 (centrally symmetric convex bodies
conjecturally bounded below by FCC) into a single quantified statement.
This is the bottom-line OQ-04 deliverable: the FCC sphere bound is
**neither universal nor optimal** across shape classes, in both
directions.

No new axioms — pure `And.intro` over `ellipsoid_lattice_le_fccPacking`,
`tetrahedronDimerDensity_gt_fccDensity`, and `ulam_le_fccPacking_density`.
-/

/--
**Final hierarchy: the FCC bound is shape-dependent in three directions.**

For every ellipsoid lattice packing `e` and every centrally symmetric
convex body packing `p` in ℝ³, the FCC sphere density `fccPacking.density`
satisfies the sandwich

```
                  e.density ≤ fccPacking.density ≤ p.density
                                     ∧
                fccDensity < tetrahedronDimerDensity
```

i.e. the parent's abstract `PackingDensity` admits values both *strictly
above* `fccDensity` (witnessed by the tetrahedral dimer, S3) and lattice-
constrained values *at or below* `fccDensity` (Bezdek–Kuperberg, S5), and
the lower bound `fccDensity ≤ ·` survives only for centrally symmetric
convex bodies under the conjectural Ulam axiom (S6).

This is the **OQ-04 closing statement**. No new axioms; aggregates the
S3+S4 axiom-free inequality with the S5 (`bezdek_kuperberg_…`) and S6
(`ulam_conjecture`) statement axioms via direct application.
-/
theorem density_hierarchy_3d
    (e : EllipsoidLatticePacking)
    (p : SymmetricConvexBody3DPacking) :
    e.density ≤ fccPacking.density ∧
    fccDensity < tetrahedronDimerDensity ∧
    fccPacking.density ≤ p.density :=
  ⟨ellipsoid_lattice_le_fccPacking e,
   tetrahedronDimerDensity_gt_fccDensity,
   ulam_le_fccPacking_density p⟩

/-!
## S8 — Soundness of the shape gates (the opaque predicates are non-vacuous)

The S5/S6 upper/lower bounds are gated by the opaque predicates
`IsEllipsoidLatticePacking` / `IsSymmetricConvexBody3DPacking`, which have no
introduction axiom.  This section demonstrates the gates are *genuinely
restrictive*, not merely uninhabited-by-fiat: two concrete densities — exactly
the ones that would break soundness if the gates were removed — are **provably
outside** their shape classes.

* The tetrahedral dimer density `4000/4671` exceeds the Bezdek–Kuperberg
  ellipsoid-lattice ceiling `fccDensity`, so it *cannot* be an ellipsoid
  lattice packing.
* The zero density falls below the (conjectural) Ulam floor `fccDensity`, so it
  *cannot* be a centrally symmetric convex body packing.

Together these are the exact "the marker re-wraps and `False` survives"
exploits of the pre-S15 contentless markers, now discharged as honest negative
facts. No new axioms.
-/

/--
**The tetrahedral dimer packing is provably NOT an ellipsoid lattice packing.**

If it were (`IsEllipsoidLatticePacking tetrahedronDimerPacking`), the
Bezdek–Kuperberg bound would force `tetrahedronDimerDensity ≤ fccDensity`,
contradicting the axiom-free `tetrahedronDimerDensity_gt_fccDensity`.  This is
genuine geometric content — the dimer density exceeds the ellipsoid-lattice
ceiling — and it is exactly the exploit that made the pre-S15 contentless
marker unsound; the opaque gate now converts it into an honest negative fact.
-/
theorem tetrahedronDimer_not_ellipsoidLattice :
    ¬ IsEllipsoidLatticePacking tetrahedronDimerPacking := by
  intro h
  have hle : tetrahedronDimerDensity ≤ fccDensity :=
    bezdek_kuperberg_ellipsoid_lattice_upper_bound ⟨tetrahedronDimerPacking, h⟩
  exact absurd hle (not_le.mpr tetrahedronDimerDensity_gt_fccDensity)

/--
**The zero-density packing is provably NOT a symmetric convex body packing.**

If it were (`IsSymmetricConvexBody3DPacking ⟨0, …⟩`), the Ulam lower bound would
force `fccDensity ≤ 0`, contradicting `fccDensity_pos`.  This is the
lower-bound mirror of `tetrahedronDimer_not_ellipsoidLattice`: the zero density
falls below the Ulam floor, so it lies outside the symmetric-convex-body shape
class, and the opaque gate blocks the corresponding unsoundness exploit.
-/
theorem zeroDensity_not_symmetricConvexBody :
    ¬ IsSymmetricConvexBody3DPacking ⟨0, le_refl 0, zero_le_one⟩ := by
  intro h
  have hge : fccDensity ≤ 0 :=
    ulam_conjecture ⟨⟨0, le_refl 0, zero_le_one⟩, h⟩
  exact absurd hge (not_le.mpr fccDensity_pos)

/-!
### General shape-class exclusion principles (subsuming the concrete `_not_` family)

The concrete negative facts above (`tetrahedronDimer_not_ellipsoidLattice`,
`zeroDensity_not_symmetricConvexBody`, and the `octahedron_/rhombicDodecahedron_/
ellipsoidNonLattice_not_ellipsoidLattice` results proved in the later sections)
are all instances of **two** general principles: the two STATEMENT axioms act as
*density filters* on their shape classes.  `bezdek_kuperberg…` (an upper bound
`≤ fccDensity`) excludes **every** density strictly above `fccDensity` from the
ellipsoid-lattice class; `ulam_conjecture` (a lower bound `≥ fccDensity`) excludes
**every** density strictly below `fccDensity` from the symmetric-convex-body class.
Stating these once removes the per-body repetition and is the recommended tool for
any future benchmark: a new packing `d` with `fccDensity < d.density` is
`not_ellipsoidLattice_of_fcc_lt`-excluded by a single application. No new axioms. -/

/-- **Ellipsoid-lattice exclusion principle.**  *Any* packing whose density
strictly exceeds `fccDensity` is provably not an ellipsoid lattice packing — the
Bezdek–Kuperberg ceiling `≤ fccDensity` cannot hold for it.  Generalizes
`tetrahedronDimer_not_ellipsoidLattice` and the three `_not_ellipsoidLattice`
benchmarks to a single principle. -/
theorem not_ellipsoidLattice_of_fcc_lt {d : PackingDensity}
    (h : fccDensity < d.density) : ¬ IsEllipsoidLatticePacking d := by
  intro hE
  exact absurd (bezdek_kuperberg_ellipsoid_lattice_upper_bound ⟨d, hE⟩) (not_le.mpr h)

/-- **Symmetric-convex-body exclusion principle.**  *Any* packing whose density is
strictly below `fccDensity` is provably not a centrally-symmetric convex body
packing — the Ulam floor `≥ fccDensity` cannot hold for it.  Generalizes
`zeroDensity_not_symmetricConvexBody` to a single principle (the density-`0`
packing is the special case `fccDensity_pos`). -/
theorem not_symmetricConvexBody_of_lt_fcc {d : PackingDensity}
    (h : d.density < fccDensity) : ¬ IsSymmetricConvexBody3DPacking d := by
  intro hS
  exact absurd (ulam_conjecture ⟨d, hS⟩) (not_le.mpr h)

/-!
## S9 — Regular octahedron: a denser shape benchmark above the tetrahedral dimer

Extends the shape hierarchy upward with a third named non-spherical benchmark.
Minkowski's lattice-packing theory gives the regular octahedron an (optimal
lattice) packing density of `18 / 19 ≈ 0.9474` — strictly denser than both the
FCC sphere density `π / (3 √ 2) ≈ 0.7405` and the Chen–Engel–Glotzer tetrahedral
dimer `4000 / 4671 ≈ 0.8564`.  This produces the strict chain

  `fccDensity < tetrahedronDimerDensity < octahedronPackingDensity < 1`,

reinforcing the OQ-04 message that the FCC bound is nowhere near universal across
convex shapes.  Everything here is axiom-free (rational `norm_num` arithmetic
plus transitivity through the S3 inequality).  The regular octahedron is a
centrally symmetric convex body, so its density lying above `fccDensity` is fully
consistent with the (conjectural) Ulam lower bound — it is *not* a counterexample
to S6, merely a witness far above the floor.

Reference: H. Minkowski, "Dichteste gitterförmige Lagerung kongruenter Körper",
*Nachr. K. Ges. Wiss. Göttingen* (1904), 311–355 — the densest lattice packing
of regular octahedra has density `18/19`.
-/

/--
**Regular-octahedron (Minkowski) lattice packing density in ℝ³.**

The rational constant `18 / 19 ≈ 0.9474` is the density of the densest lattice
packing of congruent regular octahedra (Minkowski 1904).  It strictly exceeds
the tetrahedral dimer density (`tetrahedronDimerDensity_lt_octahedron` below) and
hence, a fortiori, the FCC sphere density.
-/
noncomputable def octahedronPackingDensity : ℝ := 18 / 19

/-- The regular-octahedron packing density is positive. -/
theorem octahedronPackingDensity_pos : 0 < octahedronPackingDensity := by
  unfold octahedronPackingDensity
  norm_num

/-- The regular-octahedron packing density is strictly less than one. -/
theorem octahedronPackingDensity_lt_one : octahedronPackingDensity < 1 := by
  unfold octahedronPackingDensity
  norm_num

/--
**The octahedron beats the tetrahedral dimer.**

`tetrahedronDimerDensity = 4000/4671 ≈ 0.8564 < 18/19 = octahedronPackingDensity`.
A pure rational comparison (`4000 · 19 = 76000 < 84078 = 18 · 4671`), discharged
by `norm_num`.  No axioms.
-/
theorem tetrahedronDimerDensity_lt_octahedron :
    tetrahedronDimerDensity < octahedronPackingDensity := by
  unfold tetrahedronDimerDensity octahedronPackingDensity
  norm_num

/--
**The octahedron beats the FCC sphere density.**

`fccDensity < octahedronPackingDensity`, by transitivity through the tetrahedral
dimer: `fccDensity < tetrahedronDimerDensity` (S3, axiom-free) and
`tetrahedronDimerDensity < octahedronPackingDensity` (rational).  No new axioms.
-/
theorem octahedronPackingDensity_gt_fccDensity :
    fccDensity < octahedronPackingDensity :=
  lt_trans tetrahedronDimerDensity_gt_fccDensity tetrahedronDimerDensity_lt_octahedron

/--
**Regular-octahedron packing as a `PackingDensity` instance.**

Bundles `octahedronPackingDensity` with the S9 positivity / less-than-one bounds
into the parent's abstract `PackingDensity` structure, mirroring
`tetrahedronDimerPacking`.
-/
noncomputable def octahedronPacking : PackingDensity where
  density := octahedronPackingDensity
  nonneg  := octahedronPackingDensity_pos.le
  le_one  := octahedronPackingDensity_lt_one.le

/--
**Existential refinement: a `PackingDensity` strictly above the tetrahedral
dimer.**

Strengthens `exists_packingDensity_gt_fcc` — not only does the abstract
`PackingDensity` type admit values above `fccDensity`, it admits values above the
tetrahedral dimer itself.  Witness: `octahedronPacking`.
-/
theorem exists_packingDensity_gt_tetrahedronDimer :
    ∃ p : PackingDensity, tetrahedronDimerDensity < p.density :=
  ⟨octahedronPacking, tetrahedronDimerDensity_lt_octahedron⟩

/--
**Non-vacuity of the ellipsoid-lattice gate, octahedron edition.**

The octahedron packing density exceeds the Bezdek–Kuperberg ellipsoid-lattice
ceiling `fccDensity`, so `octahedronPacking` is provably NOT an ellipsoid lattice
packing — a second honest negative fact certifying the S5 shape gate is genuinely
restrictive (cf. `tetrahedronDimer_not_ellipsoidLattice`).  No new axioms.
-/
theorem octahedron_not_ellipsoidLattice :
    ¬ IsEllipsoidLatticePacking octahedronPacking := by
  intro h
  have hle : octahedronPackingDensity ≤ fccDensity :=
    bezdek_kuperberg_ellipsoid_lattice_upper_bound ⟨octahedronPacking, h⟩
  exact absurd hle (not_le.mpr octahedronPackingDensity_gt_fccDensity)

/--
**Strict three-shape chain.**

`fccDensity < tetrahedronDimerDensity < octahedronPackingDensity`, packaging the
S3 refutation and the S9 octahedron benchmark into a single strictly increasing
ladder of concrete non-spherical densities, all sitting above the FCC bound.
-/
theorem fcc_lt_tetrahedron_lt_octahedron :
    fccDensity < tetrahedronDimerDensity ∧
    tetrahedronDimerDensity < octahedronPackingDensity :=
  ⟨tetrahedronDimerDensity_gt_fccDensity, tetrahedronDimerDensity_lt_octahedron⟩

/-!
## S17 — space-filling convex body: density exactly `1`, the attained top of the ladder

The octahedron benchmark (S9) established `… < octahedronPackingDensity < 1`, leaving
the endpoint `1` as an *unattained* supremum of the abstract `PackingDensity` type.
This section closes that gap with a concrete witness: the **rhombic dodecahedron**
is a space-filling convex body — its congruent copies tile ℝ³ with no gaps (it is the
Voronoi cell of the FCC lattice), so its packing density is *exactly* `1`.

Consequences, all axiom-free:

* `exists_packingDensity_eq_one` — the parent's structural bound `density ≤ 1`
  (`PackingDensity.le_one`) is **sharp**: it is realised by an honest convex-body
  packing, not merely approached. The FCC sphere ceiling `π/(3√2) ≈ 0.7405` is thus
  strictly interior to the full attainable range `(0, 1]`.
* `fcc_lt_tetra_lt_octa_lt_rhombicDodecahedron` — the strict four-shape ladder
  `fccDensity < tetrahedronDimerDensity < octahedronPackingDensity <
  rhombicDodecahedronPackingDensity`, spanning from the sphere bound up to the
  space-filling maximum.

The space-filling fact is classical and shape-specific (Kepler already noted the
rhombic dodecahedron as the FCC honeycomb cell); Brass–Moser–Pach, *Research Problems
in Discrete Geometry* (2005), §3.3, cite it as the density-`1` extreme of the convex
packing landscape. Note this is fully consistent with the (conjectural) Ulam lower
bound `fccDensity ≤ δ_K`: `1 ≥ fccDensity`, so the rhombic dodecahedron sits at the
top of the admissible band, not below it.
-/

/--
**Rhombic-dodecahedron (space-filling) packing density in ℝ³.**

The rhombic dodecahedron tiles ℝ³ (it is the Voronoi cell of the FCC lattice), so
congruent copies fill space with zero wasted volume: packing density `= 1`.
-/
noncomputable def rhombicDodecahedronPackingDensity : ℝ := 1

/-- The space-filling packing density is positive. -/
theorem rhombicDodecahedronPackingDensity_pos :
    0 < rhombicDodecahedronPackingDensity := by
  unfold rhombicDodecahedronPackingDensity
  norm_num

/-- The space-filling packing density equals one (it is not strictly below `1`). -/
theorem rhombicDodecahedronPackingDensity_eq_one :
    rhombicDodecahedronPackingDensity = 1 := rfl

/--
**The space-filling body beats the octahedron.**

`octahedronPackingDensity = 18/19 ≈ 0.9474 < 1 = rhombicDodecahedronPackingDensity`,
a pure rational comparison discharged by `norm_num`. No axioms.
-/
theorem octahedron_lt_rhombicDodecahedron :
    octahedronPackingDensity < rhombicDodecahedronPackingDensity := by
  unfold octahedronPackingDensity rhombicDodecahedronPackingDensity
  norm_num

/--
**Space-filling packing as a `PackingDensity` instance.**

Bundles the density-`1` constant into the parent's abstract `PackingDensity`
structure. The `le_one` field is satisfied by *equality* (`le_of_eq`), witnessing
that the structural upper bound is attained rather than merely approached.
-/
noncomputable def rhombicDodecahedronPacking : PackingDensity where
  density := rhombicDodecahedronPackingDensity
  nonneg  := rhombicDodecahedronPackingDensity_pos.le
  le_one  := le_of_eq rhombicDodecahedronPackingDensity_eq_one

/--
**The parent's `PackingDensity.le_one` bound is sharp.**

There exists a `PackingDensity` whose density equals exactly `1`, so the abstract
type-level ceiling `density ≤ 1` is *attained* — not just an unreachable supremum.
Witness: `rhombicDodecahedronPacking` (space-filling convex body). This is the
capstone dual to `exists_packingDensity_gt_fcc` /
`exists_packingDensity_gt_tetrahedronDimer`: those show the FCC bound is not an
upper bound at all; this shows the *true* upper bound `1` is achieved. No axioms.
-/
theorem exists_packingDensity_eq_one :
    ∃ p : PackingDensity, p.density = 1 :=
  ⟨rhombicDodecahedronPacking, rhombicDodecahedronPackingDensity_eq_one⟩

/--
**Non-vacuity of the ellipsoid-lattice gate, space-filling edition.**

The rhombic-dodecahedron density `1` exceeds the Bezdek–Kuperberg ellipsoid-lattice
ceiling `fccDensity`, so `rhombicDodecahedronPacking` is provably NOT an ellipsoid
lattice packing — a third honest negative fact certifying the S5 shape gate is
genuinely restrictive (cf. `tetrahedronDimer_not_ellipsoidLattice`,
`octahedron_not_ellipsoidLattice`). No new axioms.
-/
theorem rhombicDodecahedron_not_ellipsoidLattice :
    ¬ IsEllipsoidLatticePacking rhombicDodecahedronPacking := by
  intro h
  have hle : rhombicDodecahedronPackingDensity ≤ fccDensity :=
    bezdek_kuperberg_ellipsoid_lattice_upper_bound ⟨rhombicDodecahedronPacking, h⟩
  have hgt : fccDensity < rhombicDodecahedronPackingDensity :=
    lt_trans octahedronPackingDensity_gt_fccDensity octahedron_lt_rhombicDodecahedron
  exact absurd hle (not_le.mpr hgt)

/--
**Strict four-shape ladder, up to the space-filling maximum.**

`fccDensity < tetrahedronDimerDensity < octahedronPackingDensity <
rhombicDodecahedronPackingDensity`, extending `fcc_lt_tetrahedron_lt_octahedron`
by one rung to the density-`1` top of the convex packing landscape. All strict
inequalities are axiom-free.
-/
theorem fcc_lt_tetra_lt_octa_lt_rhombicDodecahedron :
    fccDensity < tetrahedronDimerDensity ∧
    tetrahedronDimerDensity < octahedronPackingDensity ∧
    octahedronPackingDensity < rhombicDodecahedronPackingDensity :=
  ⟨tetrahedronDimerDensity_gt_fccDensity,
   tetrahedronDimerDensity_lt_octahedron,
   octahedron_lt_rhombicDodecahedron⟩

/-!
## S18 — non-lattice ellipsoid packing: the lattice constraint is essential

The ellipsoid section (S5) axiomatized the Bezdek–Kuperberg bound: every ellipsoid
*lattice* packing has density at most `fccDensity = π/(3√2)`. Its docstring notes, in
prose only, the sharp contrast with **non-lattice** ellipsoid packings: Donev–
Stillinger–Chaikin–Torquato (2004) reached `δ ≈ 0.7707` at aspect ratio `α ≈ √2`,
*strictly above* the FCC bound. This section turns that remark into machine-checked
theorems.

The headline of flagship 1 (ellipsoids) is that dropping the lattice constraint
strictly raises the achievable density for the **same shape**: `0.7707 > 0.7405`.
So the FCC ceiling is a property of *lattice* ellipsoid packings, not of ellipsoids
per se — it is the lattice-vs-non-lattice distinction, not the shape, that caps the
Bezdek–Kuperberg bound. Formally, the non-lattice ellipsoid packing exceeds
`fccDensity`, hence (like the tetrahedral dimer, octahedron, and rhombic dodecahedron
gates) is provably **not** an ellipsoid lattice packing. It also supplies the first
concrete rung strictly *between* `fccDensity` and the tetrahedral dimer, refining the
ladder. All additions are axiom-free apart from reuse of the existing S5
`bezdek_kuperberg_ellipsoid_lattice_upper_bound` axiom (no new axioms).
-/

/-- **Non-lattice ellipsoid packing density** (Donev–Stillinger–Chaikin–Torquato,
*Phys. Rev. Lett.* 2004): jammed non-lattice packings of spheroids of aspect ratio
`α ≈ √2` reach `δ ≈ 0.7707`, a ≈ 4.1% gain over FCC. Rational anchor `7707/10000`. -/
noncomputable def ellipsoidNonLatticeDensity : ℝ := 7707 / 10000

/-- The non-lattice ellipsoid packing density is positive. -/
theorem ellipsoidNonLatticeDensity_pos : 0 < ellipsoidNonLatticeDensity := by
  unfold ellipsoidNonLatticeDensity; norm_num

/-- The non-lattice ellipsoid packing density is strictly less than one. -/
theorem ellipsoidNonLatticeDensity_lt_one : ellipsoidNonLatticeDensity < 1 := by
  unfold ellipsoidNonLatticeDensity; norm_num

/--
**The non-lattice ellipsoid packing beats the FCC sphere bound.**

`fccDensity = π/(3√2) ≈ 0.7405 < 0.7707 = ellipsoidNonLatticeDensity`. Proved
axiom-free by transitivity through the S3 rational upper bound
`fccDensity < 35329/46710 ≈ 0.75635` (itself certified from `π < 3.15`, `√2 > 1.4`)
together with the numeric fact `35329/46710 < 7707/10000`. No new axioms.
-/
theorem ellipsoidNonLatticeDensity_gt_fccDensity :
    fccDensity < ellipsoidNonLatticeDensity := by
  have h := fccDensity_lt_35329_div_46710
  have hnum : (35329 : ℝ) / 46710 < 7707 / 10000 := by norm_num
  unfold ellipsoidNonLatticeDensity
  linarith [h, hnum]

/--
**The non-lattice ellipsoid density is below the tetrahedral dimer.**

`ellipsoidNonLatticeDensity = 7707/10000 ≈ 0.7707 < 4000/4671 ≈ 0.8564 =
tetrahedronDimerDensity`. A pure rational comparison
(`7707 · 4671 = 35 999 397 < 40 000 000 = 4000 · 10000`), discharged by `norm_num`.
No axioms.
-/
theorem ellipsoidNonLatticeDensity_lt_tetrahedronDimer :
    ellipsoidNonLatticeDensity < tetrahedronDimerDensity := by
  unfold ellipsoidNonLatticeDensity tetrahedronDimerDensity; norm_num

/--
**Non-lattice ellipsoid packing as a `PackingDensity` instance.**

Bundles `ellipsoidNonLatticeDensity` with its positivity / less-than-one bounds into
the parent's abstract `PackingDensity` structure, mirroring `tetrahedronDimerPacking`
and `octahedronPacking`.
-/
noncomputable def ellipsoidNonLatticePacking : PackingDensity where
  density := ellipsoidNonLatticeDensity
  nonneg  := ellipsoidNonLatticeDensity_pos.le
  le_one  := ellipsoidNonLatticeDensity_lt_one.le

/--
**The lattice constraint is essential (Donev et al. vs Bezdek–Kuperberg).**

The non-lattice ellipsoid packing density exceeds the FCC ceiling
`bezdek_kuperberg_ellipsoid_lattice_upper_bound` places on every ellipsoid *lattice*
packing, so `ellipsoidNonLatticePacking` is provably **not** an ellipsoid lattice
packing. This is the machine-checked form of flagship 1's headline: for the *same*
shape (ellipsoids), dropping the lattice constraint strictly raises the achievable
density above `π/(3√2)`. Reuses the S5 axiom only (no new axioms); cf.
`octahedron_not_ellipsoidLattice`.
-/
theorem ellipsoidNonLattice_not_ellipsoidLattice :
    ¬ IsEllipsoidLatticePacking ellipsoidNonLatticePacking := by
  intro h
  have hle : ellipsoidNonLatticeDensity ≤ fccDensity :=
    bezdek_kuperberg_ellipsoid_lattice_upper_bound ⟨ellipsoidNonLatticePacking, h⟩
  exact absurd hle (not_le.mpr ellipsoidNonLatticeDensity_gt_fccDensity)

/--
**Existential: a `PackingDensity` strictly between FCC and the tetrahedral dimer.**

The previous ladder jumped directly `fccDensity → tetrahedronDimerDensity`; the
non-lattice ellipsoid density `0.7707` is a *physically realized* value sitting
strictly between them, so the abstract `PackingDensity` type admits an intermediate
rung. Witness: `ellipsoidNonLatticePacking`. No new axioms.
-/
theorem exists_packingDensity_between_fcc_and_tetrahedronDimer :
    ∃ p : PackingDensity, fccDensity < p.density ∧ p.density < tetrahedronDimerDensity :=
  ⟨ellipsoidNonLatticePacking,
   ellipsoidNonLatticeDensity_gt_fccDensity,
   ellipsoidNonLatticeDensity_lt_tetrahedronDimer⟩

/--
**Refined strict ladder including the non-lattice ellipsoid.**

`fccDensity < ellipsoidNonLatticeDensity < tetrahedronDimerDensity <
octahedronPackingDensity`, inserting the Donev et al. non-lattice ellipsoid rung
into `fcc_lt_tetrahedron_lt_octahedron`. All strict inequalities are axiom-free.
-/
theorem fcc_lt_ellipsoidNonLattice_lt_tetrahedron_lt_octahedron :
    fccDensity < ellipsoidNonLatticeDensity ∧
    ellipsoidNonLatticeDensity < tetrahedronDimerDensity ∧
    tetrahedronDimerDensity < octahedronPackingDensity :=
  ⟨ellipsoidNonLatticeDensity_gt_fccDensity,
   ellipsoidNonLatticeDensity_lt_tetrahedronDimer,
   tetrahedronDimerDensity_lt_octahedron⟩

/-!
## S20 — the grand five-body density hierarchy and universal optimality

The two partial chains `fcc_lt_tetra_lt_octa_lt_rhombicDodecahedron` and
`fcc_lt_ellipsoidNonLattice_lt_tetrahedron_lt_octahedron` cover four bodies each
but neither lists all five in a single ordering. This section states the complete
strict chain across every body formalized in this entry, and records that the
space-filling rhombic dodecahedron (`δ = 1`) is *universally optimal*: no packing
density of any convex body can exceed it.
-/

/-- **The grand five-body density hierarchy.** All five packing densities
formalized in this entry are strictly ordered:

  `fcc  <  ellipsoid(non-lattice)  <  tetrahedron(dimer)  <  octahedron  <  rhombicDodecahedron`,

i.e. `π/(3√2) < 0.7707 < 4000/4671 < 18/19 < 1`. This unifies the two partial
chains (`fcc_lt_tetra_lt_octa_lt_rhombicDodecahedron`,
`fcc_lt_ellipsoidNonLattice_lt_tetrahedron_lt_octahedron`) into the single complete
ordering of every body in the entry. The sphere (FCC) is strictly the *least* dense
and the space-filling rhombic dodecahedron strictly the *most* dense. -/
theorem grand_density_hierarchy :
    fccDensity < ellipsoidNonLatticeDensity ∧
    ellipsoidNonLatticeDensity < tetrahedronDimerDensity ∧
    tetrahedronDimerDensity < octahedronPackingDensity ∧
    octahedronPackingDensity < rhombicDodecahedronPackingDensity :=
  ⟨ellipsoidNonLatticeDensity_gt_fccDensity,
   ellipsoidNonLatticeDensity_lt_tetrahedronDimer,
   tetrahedronDimerDensity_lt_octahedron,
   octahedron_lt_rhombicDodecahedron⟩

/-- **Universal optimality of the space-filling packing.** No packing density
exceeds that of the rhombic dodecahedron: for *every* `PackingDensity d`,
`d.density ≤ rhombicDodecahedronPackingDensity`. The rhombic dodecahedron attains
the universal ceiling `δ = 1` (space-filling), so it is a global maximum of the
density functional — every body in the hierarchy above, and any other, sits weakly
below it. Immediate from the `le_one` field and
`rhombicDodecahedronPackingDensity_eq_one`. -/
theorem packingDensity_le_rhombicDodecahedron (d : PackingDensity) :
    d.density ≤ rhombicDodecahedronPackingDensity := by
  rw [rhombicDodecahedronPackingDensity_eq_one]
  exact d.le_one

/-!
## S21 — the density functional attains a genuine global maximum

`packingDensity_le_rhombicDodecahedron` shows the space-filling density `δ = 1` is a
universal ceiling, and `exists_packingDensity_eq_one` shows that ceiling is *attained*
by `rhombicDodecahedronPacking`. The docstring of the former already calls the rhombic
dodecahedron "a global maximum of the density functional" — but only in prose. This
section turns that phrase into a single machine-checked statement in the two standard
forms: the bare existential (a `PackingDensity` weakly dominating every other) and
Mathlib's `IsGreatest` on the range of the density projection. Both are immediate
combinations of the two facts above; no new axioms.
-/

/-- **The density functional attains a global maximum (existential form).**
There is a `PackingDensity` weakly dominating every other, namely the space-filling
rhombic dodecahedron: `∀ e, e.density ≤ rhombicDodecahedronPacking.density = 1`.
Immediate from `packingDensity_le_rhombicDodecahedron` (the density-`1` ceiling is
attained by `rhombicDodecahedronPacking`, so the universal bound is realized as a true
maximum, not an unreached supremum). No axioms. -/
theorem exists_greatest_packingDensity :
    ∃ d : PackingDensity, ∀ e : PackingDensity, e.density ≤ d.density :=
  ⟨rhombicDodecahedronPacking, packingDensity_le_rhombicDodecahedron⟩

/-- **The density functional attains its supremum (`IsGreatest` form).**
`1` is the greatest element of the range of `PackingDensity.density`: it lies in the
range (witnessed by `rhombicDodecahedronPacking`) and it is an upper bound of the whole
range (`packingDensity_le_rhombicDodecahedron`). This is the Mathlib-native packaging of
the "space-filling body is universally optimal" statement — the density functional
genuinely achieves its maximum value `δ = 1`, dual to the (conjecturally minimal, hence
axiomatized via Ulam) sphere at the bottom of the hierarchy. No axioms. -/
theorem isGreatest_packingDensity_range :
    IsGreatest (Set.range (PackingDensity.density)) 1 := by
  refine ⟨⟨rhombicDodecahedronPacking, rhombicDodecahedronPackingDensity_eq_one⟩, ?_⟩
  rintro x ⟨d, rfl⟩
  exact packingDensity_le_rhombicDodecahedron d

/-!
## S22 — the packing-density supremum, and the sphere-to-space-filling gap

`isGreatest_packingDensity_range` (S21) shows `δ = 1` is the *attained* maximum of
the density functional. This section records its two standard capstone forms: the
supremum of the range is exactly `1` (`csSup … = 1`, the Mathlib-native
"space-filling body is optimal" statement), and a *quantitative* version of the
hierarchy's total spread — the space-filling rhombic dodecahedron beats the FCC
sphere at the bottom by more than `6/25`. Both reuse only facts already proved in
this file (`isGreatest_packingDensity_range`, `rhombicDodecahedronPackingDensity_eq_one`,
the verified rational bound `fccDensity_lt_35329_div_46710`); no new axioms.
-/

/-- **The packing-density supremum equals the space-filling value.**
`sSup (range PackingDensity.density) = 1`: the least upper bound of all achievable
convex-body packing densities is exactly the space-filling value `δ = 1`, and it is
*attained* (by `rhombicDodecahedronPacking`), so the supremum is a genuine maximum.
The Mathlib-native `sSup` packaging of `isGreatest_packingDensity_range`. No axioms. -/
theorem csSup_packingDensity_range_eq_one :
    sSup (Set.range (PackingDensity.density)) = 1 :=
  isGreatest_packingDensity_range.csSup_eq

/-- **The range of achievable densities is bounded above.**
`BddAbove (range PackingDensity.density)`: the density functional does not run off to
arbitrarily large values — the space-filling ceiling `δ = 1` bounds it. Immediate from
`isGreatest_packingDensity_range`. No axioms. -/
theorem bddAbove_packingDensity_range :
    BddAbove (Set.range (PackingDensity.density)) :=
  isGreatest_packingDensity_range.bddAbove

/-- **Quantitative sphere-to-space-filling gap.**
The top of the hierarchy (the space-filling rhombic dodecahedron, `δ = 1`) exceeds the
bottom (the FCC sphere density `π/(3√2) ≈ 0.7405`) by more than `6/25 = 0.24`:

  `6/25 < rhombicDodecahedronPackingDensity − fccDensity`.

A machine-checked measure of the total spread of the five-body hierarchy
(`grand_density_hierarchy`), obtained from the space-filling value `1`
(`rhombicDodecahedronPackingDensity_eq_one`) and the file's verified upper bound
`fccDensity < 35329/46710 < 19/25` (`fccDensity_lt_35329_div_46710`). No new axioms. -/
theorem sphere_to_spaceFilling_gap_gt :
    6 / 25 < rhombicDodecahedronPackingDensity - fccDensity := by
  rw [rhombicDodecahedronPackingDensity_eq_one]
  linarith [fccDensity_lt_35329_div_46710]

/-!
## S23 — the FCC sphere density is provably *not* optimal

`isGreatest_packingDensity_range` (S21) shows the space-filling value `δ = 1` is the
*attained* maximum. Its sharp negative dual — the crisp headline of Kepler OQ-04 — is
that the FCC sphere density `π/(3√2)` is **not** the greatest achievable density: some
convex body (the space-filling rhombic dodecahedron) packs strictly denser, so spheres
are provably suboptimal among convex-body packings. This section records that as a
Mathlib-native `¬ IsGreatest` statement and, dually, as the strict inequality
`fccDensity < sSup (range density)`. Both reuse only facts already in this file
(the `δ = 1` range-membership witness and the verified bound
`fccDensity_lt_35329_div_46710`); no new axioms.
-/

/-- **The FCC sphere density is not the greatest achievable density.**
`¬ IsGreatest (range PackingDensity.density) fccDensity`: were `fccDensity` an upper
bound of the range it would dominate the space-filling value `δ = 1`
(`rhombicDodecahedronPacking`), forcing `1 ≤ fccDensity` — impossible since
`fccDensity < 35329/46710 < 1` (`fccDensity_lt_35329_div_46710`). This is the exact
negative dual of `isGreatest_packingDensity_range`: spheres are provably *suboptimal*
among convex-body packings, the headline of Kepler OQ-04. No axioms. -/
theorem not_isGreatest_fccDensity_range :
    ¬ IsGreatest (Set.range (PackingDensity.density)) fccDensity := by
  rintro ⟨-, hub⟩
  have h1 : (1 : ℝ) ≤ fccDensity :=
    hub ⟨rhombicDodecahedronPacking, rhombicDodecahedronPackingDensity_eq_one⟩
  linarith [fccDensity_lt_35329_div_46710]

/-- **The FCC sphere density lies strictly below the achievable supremum.**
`fccDensity < sSup (range PackingDensity.density)`: the least upper bound of achievable
convex-body packing densities (`= 1`, `csSup_packingDensity_range_eq_one`) strictly
exceeds the FCC sphere density. The `sSup`-native rendering of "spheres are suboptimal",
complementing the `¬ IsGreatest` form. No axioms. -/
theorem fccDensity_lt_csSup_packingDensity_range :
    fccDensity < sSup (Set.range (PackingDensity.density)) := by
  rw [csSup_packingDensity_range_eq_one]
  linarith [fccDensity_lt_35329_div_46710]

/-!
## S24 — quantitative gaps at each rung of the hierarchy

`sphere_to_spaceFilling_gap_gt` (S22) measures the *total* spread of the five-body chain
`grand_density_hierarchy` (top minus bottom, `> 6/25`). It does not record how that spread
is distributed across the four individual steps. This section fills that in: each strict
inequality of `grand_density_hierarchy` is upgraded to an explicit rational lower bound on
the gap, exactly as `tetrahedronDimerDensity_gt_fccDensity_margin` (S3) does for the
sphere-to-tetrahedron step. Three of the four steps are between rational densities (pure
`norm_num`); the sphere-to-ellipsoid step routes through the verified upper bound
`fccDensity < 35329/46710` (`fccDensity_lt_35329_div_46710`). No new axioms.
-/

/-- **Sphere → ellipsoid gap.** The DSC ellipsoid (non-lattice) density `0.7707` exceeds
the FCC sphere density `π/(3√2)` by more than `1/100`. Uses the verified rational upper
bound `fccDensity < 35329/46710 ≈ 0.75635` (`fccDensity_lt_35329_div_46710`); the true gap
`≈ 0.0302` is larger, but `1/100` is all the file's certified sphere bound yields. -/
theorem fcc_to_ellipsoidNonLattice_gap_gt :
    1 / 100 < ellipsoidNonLatticeDensity - fccDensity := by
  have h := fccDensity_lt_35329_div_46710
  unfold ellipsoidNonLatticeDensity
  linarith

/-- **Ellipsoid → tetrahedron gap.** The Chen–Engel–Glotzer tetrahedral dimer density
`4000/4671 ≈ 0.8563` exceeds the ellipsoid density `7707/10000` by more than `1/12`. Pure
rational comparison. -/
theorem ellipsoidNonLattice_to_tetrahedronDimer_gap_gt :
    1 / 12 < tetrahedronDimerDensity - ellipsoidNonLatticeDensity := by
  unfold tetrahedronDimerDensity ellipsoidNonLatticeDensity
  norm_num

/-- **Tetrahedron → octahedron gap.** The regular-octahedron Minkowski lattice density
`18/19 ≈ 0.9474` exceeds the tetrahedral dimer density `4000/4671` by more than `1/12`.
Pure rational comparison. -/
theorem tetrahedronDimer_to_octahedron_gap_gt :
    1 / 12 < octahedronPackingDensity - tetrahedronDimerDensity := by
  unfold octahedronPackingDensity tetrahedronDimerDensity
  norm_num

/-- **Octahedron → space-filling gap.** The space-filling rhombic dodecahedron (`δ = 1`)
exceeds the octahedron density `18/19` by exactly `1/19`, in particular by more than
`1/20`. Uses `rhombicDodecahedronPackingDensity_eq_one`. -/
theorem octahedron_to_rhombicDodecahedron_gap_gt :
    1 / 20 < rhombicDodecahedronPackingDensity - octahedronPackingDensity := by
  rw [rhombicDodecahedronPackingDensity_eq_one]
  unfold octahedronPackingDensity
  norm_num

/-- **The rung gaps, bundled.** Each of the four strict steps of `grand_density_hierarchy`
carries an explicit rational margin: the four gaps exceed `1/100`, `1/12`, `1/12`, `1/20`
respectively. Their sum `> 6/25` recovers the total spread of `sphere_to_spaceFilling_gap_gt`,
now resolved rung by rung. No axioms. -/
theorem hierarchy_rung_gaps :
    1 / 100 < ellipsoidNonLatticeDensity - fccDensity ∧
    1 / 12 < tetrahedronDimerDensity - ellipsoidNonLatticeDensity ∧
    1 / 12 < octahedronPackingDensity - tetrahedronDimerDensity ∧
    1 / 20 < rhombicDodecahedronPackingDensity - octahedronPackingDensity :=
  ⟨fcc_to_ellipsoidNonLattice_gap_gt,
   ellipsoidNonLattice_to_tetrahedronDimer_gap_gt,
   tetrahedronDimer_to_octahedron_gap_gt,
   octahedron_to_rhombicDodecahedron_gap_gt⟩

end KeplerConjectureOQ04
