# Problem: Spherical Excess Formula (Girard–Euler Theorem)

**Slug**: spherical-law-of-cosines-oq-02
**Created**: 2026-05-12 (seeker-init)
**Status**: Active (S1 OBSERVE complete)
**Source**: seeker-selected (parent: `spherical-law-of-cosines`, openQuestions[1])
**Parent**: `spherical-law-of-cosines` (`Proofs.SphericalLawOfCosines`, 341 LOC, verified)

## Problem Statement

### Formal Statement

For a spherical triangle on the unit sphere $S^2 \subset \mathbb{R}^3$ with vertices
$\mathbf{u}, \mathbf{v}, \mathbf{w} \in S^2$ (pairwise distinct, not antipodal,
non-coplanar with the origin) and dihedral angles $A, B, C$ at the respective vertices:

$$
\text{area}(\triangle \mathbf{uvw}) = A + B + C - \pi
$$

where area is measured in **steradians** (the spherical analogue of radians, with the
unit sphere having total area $4\pi$ sr).

This is the **Girard–Euler theorem** (Albert Girard, 1629; sometimes attributed to
Thomas Harriot, 1603). It expresses a foundational connection between the **angle
defect** of a spherical polygon and its area — a special case of the **Gauss-Bonnet
theorem** for surfaces of constant positive curvature ($K = 1$ on the unit sphere).

### Plain Language

In Euclidean (flat) geometry, the angles of any triangle sum to exactly $\pi$. On the
**curved** surface of a sphere, the angles sum to *more* than $\pi$ — and the excess
equals the area of the triangle (measured as the fraction of the sphere it occupies,
scaled by $4\pi$).

A spherical triangle filling a quarter of the sphere has area $\pi$ (a quarter of $4\pi$),
so its angle sum is $\pi + \pi = 2\pi$. A "very small" spherical triangle has area
nearly 0, so its angle sum is nearly $\pi$ (the Euclidean limit).

### Why This Matters

- **Foundational for spherical and Riemannian geometry**: the spherical excess formula
  is the *prototype* of the local Gauss-Bonnet theorem (angle defect = curvature
  integral). Every introductory course on differential geometry derives it.
- **Historical significance**: Albert Girard published it in 1629, more than 200 years
  before Gauss's general theorem (1827) and Bonnet's global extension (1848). The
  Lhuilier (1782) proof via *lunes* is one of the most elegant derivations in classical
  geometry.
- **Mathlib gap**: Mathlib v4.26.0 has no `spherical_excess`, `Girard`, or
  `Gauss-Bonnet` for surfaces. The in-tree `TriangleAngleSumOQ02.lean` (gallery slug
  `triangle-angle-sum-oq-02`) proves `theorem girard_theorem (T : SphericalTriangle)`
  **but** the proof is built on an *axiomatized* `GeodesicTriangle` structure with a
  structure-encoded `gb_local : α + β + γ - π = integratedCurvature` field (a
  structure-encoded assumption, per CLAUDE.md axiom-integrity policy). This sub-question
  asks for an **axiom-free derivation** from the unit-vector / inner-product
  formalization of the parent `Proofs.SphericalLawOfCosines`.

## Known Results

### What's Already Proven

- **`Proofs.SphericalLawOfCosines` (parent, COMPLETED)**: spherical law of cosines
  $\cos(c) = \cos(a) \cos(b) + \sin(a) \sin(b) \cos(C)$ via unit-vector inner products
  in $\mathbb{R}^3$. 341 LOC, 0 sorries.
- **`Proofs.SphericalLawOfSines` (sibling, COMPLETED)**: spherical law of sines
  $\sin(a)/\sin(A) = \sin(b)/\sin(B) = \sin(c)/\sin(C)$. 323 LOC.
- **`Proofs.SphericalLawOfCosinesOQ05` (sibling)**: addressed the dual spherical law
  of cosines (oq-05).
- **`Proofs.TriangleAngleSumOQ02` (related, AXIOMATIZED)**: Girard's theorem PROVEN, but
  the `GeodesicTriangle` structure carries `gb_local` as a structure-encoded assumption.
  Therefore the proof is **honestly axiomatized**, not from-first-principles. The
  spherical-excess formula at line 180 (`spherical_area_eq_radius_sq_excess`) is
  derived FROM `gb_local`, not derived from $\mathbb{R}^3$ geometry.
- **Mathlib v4.26.0**: provides `Mathlib.Analysis.InnerProductSpace.*` (used by parent
  for unit-vector arithmetic) but **no `MeasureTheory` integration over spherical caps,
  lunes, or geodesic triangles**.

### What's Still Open

The unit-vector / inner-product formalization currently has NO definition of the
**area** of a spherical triangle. Without that, the right-hand side of the Girard
formula is undefined. The OQ-02 work must therefore include:

1. **Define `sphericalTriangleArea u v w : ℝ`** in the parent's $\mathbb{R}^3$
   unit-vector setting. Two candidate definitions:
   - **Solid angle**: the measure of directions from origin pointing into the spherical
     triangle (equivalently, the Lebesgue measure on $S^2$ of the closed spherical-cap-
     intersection region).
   - **Excess-by-definition**: define area := A + B + C - π (circular; trivializes the
     theorem). Honest only as a *definition*, not a theorem.
2. **Prove `sphericalTriangleArea u v w = angle(u, v, w_at_u) + angle(... at v) + angle(... at w) - π`** using either:
   - The **lune decomposition** (Girard 1629; Lhuilier 1782): six lunes around the
     triangle cover the sphere with multiplicity, and individual lune areas are linear
     in the dihedral angles.
   - **Stokes / Gauss-Bonnet from spherical metric**: harder, depends on Mathlib
     differential-forms.

### Our Goal

**S1 OBSERVE deliverable** (this iteration): map the lune-decomposition proof
architecture, identify Mathlib v4.26.0 dependencies, decompose S2 into three
sub-iterations (S2a/S2b/S2c, total ~250 LOC), and explicitly flag the
**solid-angle vs Lebesgue-measure-on-$S^2$** definition choice for the S2a implementer.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `spherical-law-of-cosines` | **Parent**: unit-vector arithmetic; angle/inner-product identities. Base for S2 area definition. | $\mathbb{R}^3$ unit vectors, `Real.arccos` |
| `spherical-law-of-sines` | Sibling: dihedral-angle structure via cross products. May supply `dihedral_angle_at_vertex` helper. | cross products, normal vectors |
| `triangle-angle-sum-oq-02` | Related but axiomatized: Girard's theorem proven from `GeodesicTriangle.gb_local` structure-encoded assumption. **Not** a from-first-principles proof. | Riemannian-triangle axiom |
| `spherical-law-of-cosines-oq-05` | Sibling OQ-05: dual law (which addresses a different OQ). | Same parent vocabulary |

## Initial Thoughts

### Potential Approaches

See "Our Goal" and the full session note
`sessions/2026-05-12-s1-observe-lune-decomposition-roadmap.md` for the lune-
decomposition architecture. Executive summary:

- **Path A — lune decomposition** (Lhuilier 1782, recommended): three pairs of great
  circles bound six lunes around a spherical triangle and its antipode. Each lune has
  area $2\theta$ where $\theta$ is the dihedral angle. The lunes cover the sphere with
  precise multiplicity (2 on the triangle and antipode, 1 elsewhere), giving
  $4(A + B + C) = 4\pi + 4 \cdot \text{area}(\triangle)$, i.e. $\text{area}(\triangle) = A + B + C - \pi$.
- **Path B — direct integration**: $\text{area} = \int_\triangle 1 \, dS$ on the sphere
  with the spherical metric. Requires Mathlib differential-form / pullback-measure
  infrastructure that may not be fully ergonomic at v4.26.0.
- **Path C — Stokes theorem**: integrate $\int_\partial \mathbf{F} \cdot d\mathbf{r}$
  over the boundary geodesics for a clever vector field $\mathbf{F}$. Same Mathlib gaps
  as Path B.

**Recommended S2**: Path A (lune decomposition), in three sub-iterations:

- **S2a (~80 LOC)**: define `sphericalTriangleArea` via solid-angle / measure-theoretic
  formulation; define `lune` and prove `lune_area = 2 · θ`.
- **S2b (~80 LOC)**: prove the lune-cover identity (six lunes around triangle + antipode).
- **S2c (~80 LOC)**: assemble: $4\pi = 4 \cdot \text{area}(\triangle) + 2 \cdot (4\pi - 4 \cdot \text{area}(\triangle))$ ↔
  algebraic manipulation gives Girard's formula.

### Likely Tools / Lemmas

- The parent's unit-vector / `Real.arccos` arithmetic for the dihedral angles.
- `MeasureTheory.SpheresOnSphere` or similar (need to verify name at v4.26.0).
- `Mathlib.MeasureTheory.MeasurableSpace.Basic` for measurable spherical-triangle sets.
- `EuclideanSpace.dist` and `Inner.inner` from `InnerProductSpace.Basic`.
- **Possibly missing**: explicit Lebesgue measure on $S^2$ pulled back from
  `MeasureTheory.Measure.Lebesgue`. Needs S1 verification.

### Expected Difficulty

- **S1 OBSERVE** (this iteration): doc-only ~600 LOC, easy. **DONE in this PR.**
- **S2a sphericalTriangleArea + lune area**: ~80 LOC. **Mathlib spherical-measure
  status TBD at S2a implementation time.**
- **S2b lune-cover identity**: ~80 LOC, geometric bookkeeping.
- **S2c assemble**: ~80 LOC. Algebraic.

Total: ~250 LOC across S2a/b/c. Build-safe assuming `MeasureTheory.lebesgueSphere` (or
equivalent) exists in Mathlib v4.26.0; **flag for S2a implementer to verify before
starting**.
