# Knowledge Base: spherical-law-of-cosines-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent slug `spherical-law-of-cosines` (`Proofs.SphericalLawOfCosines`, 341 LOC,
verified) proves $\cos(c) = \cos(a) \cos(b) + \sin(a) \sin(b) \cos(C)$ for spherical
triangles using unit vectors $\mathbf{u}, \mathbf{v}, \mathbf{w}$ in $\mathbb{R}^3$ and
inner products. The OQ-02 sub-question asks to extend this to the **Girard-Euler
spherical-excess formula**:

$$\text{area}(\triangle \mathbf{uvw}) = A + B + C - \pi$$

where $A, B, C$ are the dihedral angles at the vertices and area is in steradians.

This is the **prototype Gauss-Bonnet** (constant-positive-curvature special case).

---

## Insights (S1 OBSERVE)

### Insight 1 — The in-tree axiomatized Girard is not first-principles

`Proofs.TriangleAngleSumOQ02.lean` defines

```lean
structure GeodesicTriangle where
  α β γ area integratedCurvature : ℝ
  ...
  gb_local : α + β + γ - π = integratedCurvature
```

and proves Girard's theorem ($\text{area}(T) = R^2 \cdot \text{excess}(T)$) at line 180
**by direct use of `gb_local`**. The `gb_local` field is a **structure-encoded
assumption** per CLAUDE.md axiom-integrity policy — it is not derived from anything;
it just *asserts* the Gauss-Bonnet identity. So this Girard theorem is honestly
axiomatized.

The OQ-02 sub-question asks for an **axiom-free** proof from the unit-vector
formalization of the parent. This is **distinct** from the in-tree axiomatized
version — both can coexist in the gallery (different proofs of the same theorem).

### Insight 2 — Lhuilier lune-decomposition is the classical first-principles proof

Albert Girard (1629) and later Simon Lhuilier (1782) gave the following argument:

1. **Lune lemma**: a *lune* is the region of the unit sphere bounded by two great-circle
   arcs meeting at antipodal points. Lunes are parametrized by the dihedral angle $\theta$
   between the two great circles. By rotational symmetry, the area of a lune is linear
   in $\theta$; at $\theta = \pi$ (full half-sphere), the lune fills half the sphere,
   so $\text{area}(\text{lune}_\theta) = 2\theta$ steradians.

2. **Six-lune cover**: a spherical triangle $T = \triangle \mathbf{uvw}$ with dihedral
   angles $A, B, C$ at its vertices generates **six lunes** as follows. Each pair of
   sides extends to two complete great circles; the wedge between them (containing $T$)
   forms a lune at the dihedral angle at the third vertex. The three lunes are
   $L_A$ (containing $T$, at dihedral angle $A$, antipodal to the lune containing $-T$),
   $L_B$, $L_C$. The three lunes through $-T$ are $L_A', L_B', L_C'$. **Note**: each
   $L_X$ and $L_X'$ are antipodal lunes (they share their dihedral angle $X$ but are
   antipodal regions of the sphere).

3. **Multiplicity count**: the six lunes $L_A, L_A', L_B, L_B', L_C, L_C'$ tile the
   sphere with the following multiplicity:

   - $T$ is in $L_A \cap L_B \cap L_C$ (multiplicity 3).
   - $-T$ is in $L_A' \cap L_B' \cap L_C'$ (multiplicity 3).
   - Everything else is in exactly one of the six lunes (multiplicity 1).

   So the sum of lune areas counts the sphere area with this weighting:
   $$\sum_{X \in \{A,B,C\}} (\text{area}(L_X) + \text{area}(L_X')) = 1 \cdot (4\pi - 2 \cdot \text{area}(T)) + 3 \cdot 2 \cdot \text{area}(T) = 4\pi + 4 \cdot \text{area}(T).$$

   Using $\text{area}(L_X) = 2X$:
   $$4(A + B + C) = 4\pi + 4 \cdot \text{area}(T)$$
   $$\text{area}(T) = A + B + C - \pi$$ ✓

### Insight 3 — Mathlib spherical-measure status uncertain at v4.26.0

A grep at v4.26.0 for `Sphere.*Measure|sphere.*measure|S²|surface measure|isotropy` in
`Mathlib/MeasureTheory/` is inconclusive. There are spherical-cap definitions in
`Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean` but **not** a canonical
$S^2$ surface measure with `volume(Sphere ℝ³) = 4π` baked in.

**Workaround (recommended)**: define `solidAngle` as a **3-D Lebesgue cone measure**,
not a 2-D surface measure. For a spherical region $R \subseteq S^2$, define

$$\text{Cone}(R) := \{ t \cdot p : t \in [0, 1], p \in R \} \subseteq \mathbb{R}^3$$

(the closed cone from origin to $R$ within the unit ball). The solid angle of $R$ is
$\Omega(R) := 3 \cdot \text{vol}(\text{Cone}(R))$ (the factor 3 calibrates so that
$\Omega(S^2) = 3 \cdot \frac{4\pi}{3} = 4\pi$). This formulation uses **only 3-D
Lebesgue measure** (`MeasureTheory.volume` on `ℝ³`), which is fully ergonomic at
v4.26.0.

### Insight 4 — Lune as a cone-cap is computable in 3-D

A lune at dihedral angle $\theta$ around the $\mathbf{z}$-axis (great circles through
$\pm \hat{z}$ at angular separation $\theta$) is

$$L_\theta := \{ p \in S^2 : 0 \leq \arg(p_x + i p_y) \leq \theta \}$$

(viewing $\mathbb{R}^3$ as $\mathbb{C} \times \mathbb{R}$). Its cone

$$\text{Cone}(L_\theta) := \{ t \cdot p : t \in [0, 1], p \in L_\theta \}$$

is a "pie wedge" of the unit ball — angular fraction $\theta / (2\pi)$ of the ball.
Volume:

$$\text{vol}(\text{Cone}(L_\theta)) = \frac{\theta}{2\pi} \cdot \frac{4\pi}{3} = \frac{2\theta}{3}$$

so $\Omega(L_\theta) = 3 \cdot \frac{2\theta}{3} = 2\theta$ ✓. This matches the
classical lune-area formula.

### Insight 5 — Spherical triangle as a cone-cap from $\mathbb{R}^3$

For unit vectors $\mathbf{u}, \mathbf{v}, \mathbf{w} \in S^2$ (in counterclockwise
order), the spherical triangle they bound is the set of points $p \in S^2$ such that
$p$ is in the cone spanned by $\mathbf{u}, \mathbf{v}, \mathbf{w}$. Its cone is

$$\text{Cone}(T) := \{ \alpha \mathbf{u} + \beta \mathbf{v} + \gamma \mathbf{w} : \alpha, \beta, \gamma \geq 0, \|p\| \leq 1 \}$$

This is a tetrahedral cone (with vertex at origin) intersected with the unit ball.

The solid angle $\Omega(T) = 3 \cdot \text{vol}(\text{Cone}(T))$. The lune-decomposition
argument then becomes a fact about *the volumes of cones in $\mathbb{R}^3$*: the six
lune-cones cover the unit ball with multiplicity 3 on $\text{Cone}(T) \cup \text{Cone}(-T)$
and multiplicity 1 elsewhere. Verifying this is a 3-D solid-geometry computation, not
a 2-D spherical-geometry computation.

### Insight 6 — Dihedral angle at a vertex is `Real.arccos` of unit-normal inner product

For a vertex $\mathbf{u}$ of a spherical triangle $\triangle \mathbf{uvw}$, the dihedral
angle at $\mathbf{u}$ is the angle between the half-planes containing edges
$\overline{\mathbf{uv}}$ and $\overline{\mathbf{uw}}$ (as planar regions through the
origin). The normal to the half-plane $\overline{\mathbf{uv}}$ is
$\mathbf{u} \times \mathbf{v}$ (a vector perpendicular to both); the dihedral angle at
$\mathbf{u}$ is the angle between $\mathbf{u} \times \mathbf{v}$ and
$\mathbf{u} \times \mathbf{w}$:

$$A_{\mathbf{u}} = \arccos\left( \frac{\langle \mathbf{u} \times \mathbf{v}, \mathbf{u} \times \mathbf{w} \rangle}{\|\mathbf{u} \times \mathbf{v}\| \cdot \|\mathbf{u} \times \mathbf{w}\|} \right)$$

The parent file `SphericalLawOfCosines.lean` does not define this directly, but the
sibling `SphericalLawOfSines.lean` uses cross products in its argument — **good place
to look for a `dihedral_angle_at_vertex` helper to reuse**.

### Insight 7 — Honest scope: assume non-degeneracy

For the lune-decomposition to work, the spherical triangle must be non-degenerate:

- Three vertices are pairwise distinct.
- No two are antipodal.
- The three vectors are linearly independent (so the triangle has positive area).

These can be captured as hypotheses on the `sphericalTriangleArea` definition. The
parent `SphericalLawOfCosines` already imposes similar non-degeneracy hypotheses on
its theorem — the S2 implementation should match this pattern.

---

## Dead Ends

### Dead End 1 — Use `Proofs.TriangleAngleSumOQ02.girard_theorem` directly

The in-tree axiomatized version assumes `gb_local : α + β + γ - π = integratedCurvature`
as a structure field. Importing and citing this would make the new OQ-02 result
*equally axiomatized* as the original — failing the from-first-principles goal of this
sub-question. The new OQ-02 proof must **not** import `TriangleAngleSumOQ02`.

### Dead End 2 — Pull spherical-area measure from `Mathlib/MeasureTheory/Measure/Hausdorff`

Mathlib v4.26.0's Hausdorff measure on $S^2$ (computed as the 2-D Hausdorff measure of
the unit sphere in $\mathbb{R}^3$) MAY equal the standard surface area up to a
normalization factor, but the ergonomic API for "integrate over a region of $S^2$" is
not well-developed. Workaround: insight 3 (cone-Lebesgue) sidesteps the issue entirely.

### Dead End 3 — Define $\text{area}(\triangle) := A + B + C - \pi$ by fiat

Tempting (and would make the theorem trivial), but **circular**: the goal is to *prove*
the formula, not to define it as the formula. The S2 implementation must define area
independently (e.g., as `solidAngle` via cone-Lebesgue, insight 3) and then prove the
identity.

---

## References

- **Parent slug**: `spherical-law-of-cosines` (`Proofs.SphericalLawOfCosines`, 341 LOC,
  verified). Unit-vector / inner-product formulation.
- **Related (axiomatized) slug**: `triangle-angle-sum-oq-02`
  (`Proofs.TriangleAngleSumOQ02`, with `GeodesicTriangle.gb_local` structure field).
- **Sibling**: `spherical-law-of-cosines-oq-05` (dual spherical law of cosines,
  COMPLETED).
- **Mathlib v4.26.0 modules**:
  - `Mathlib.Analysis.InnerProductSpace.Basic` (inner products, used by parent).
  - `Mathlib.Analysis.InnerProductSpace.EuclideanDist` (Euclidean space utilities).
  - `Mathlib.MeasureTheory.Measure.Lebesgue` (3-D Lebesgue for cone-Lebesgue area).
  - `Mathlib.MeasureTheory.MeasurableSpace.Basic` (measurable cones).
- **Survey session note**: `sessions/2026-05-12-s1-observe-lune-decomposition-roadmap.md`
  (created by S1 OBSERVE, this PR).
- **External references**:
  - Girard (1629). *Invention nouvelle en l'algèbre*, contains the first published
    statement of the spherical-excess formula.
  - Lhuilier (1782). *De relatione mutua capacitatis et terminorum figurarum*, gave
    the lune-decomposition proof.
  - Coxeter, *Introduction to Geometry*, §6.9 (modern presentation of Lhuilier's proof).
  - Todhunter, *Spherical Trigonometry* (1886), §107 (the lune-cover identity).
