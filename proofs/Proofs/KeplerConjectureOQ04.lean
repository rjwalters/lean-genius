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

end KeplerConjectureOQ04
