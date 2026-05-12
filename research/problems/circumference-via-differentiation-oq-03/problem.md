# Problem: Riemannian area-circumference duality via the co-area formula

## Statement

### Plain Language

The parent gallery proof `circumference-via-differentiation` formalizes
the calculus identity
$$C(r) = \frac{d}{dr} A(r),$$
where $A(r) = \pi r^2$ is the area of a Euclidean disk of radius $r$
and $C(r) = 2\pi r$ is its boundary circumference. The accompanying
sibling proof `circumference-via-differentiation-oq-01` (verified,
0 sorries, 0 axioms) extends this to all dimensions $n$ via the
$n$-ball volume $V_n(r) = \omega_n r^n$ and the surface area
$S_{n-1}(r) = n \omega_n r^{n-1}$ of the $(n-1)$-sphere, with
$\omega_n = \pi^{n/2}/\Gamma(n/2+1)$ supplied by Mathlib's
`unitBallVolume`.

OQ-03 asks: **does the same identity hold for geodesic balls on a
Riemannian manifold, via the co-area formula?** Concretely, fix a
complete Riemannian $n$-manifold $(M, g)$, a point $p \in M$, and a
radius $r$ strictly less than the **injectivity radius** at $p$. Let

- $B_M(p, r) = \{x \in M : d_g(p, x) \le r\}$  — the closed
  geodesic ball,
- $S_M(p, r) = \{x \in M : d_g(p, x) = r\}$    — the geodesic sphere
  (an embedded $(n-1)$-submanifold for $r < \operatorname{inj}(p)$).

Write $V_M(p, r) = \operatorname{Vol}_g(B_M(p, r))$ for the
Riemannian volume of the ball and $A_M(p, r) =
\operatorname{Vol}_g(S_M(p, r))$ for the induced surface area on the
geodesic sphere (the $(n-1)$-Hausdorff measure on $S_M(p,r)$ under
the restricted Riemannian metric). The conjecture is:

$$\boxed{\frac{d}{dr} V_M(p, r) = A_M(p, r) \quad \text{for } 0 < r <
\operatorname{inj}(p).}$$

When $M = \mathbb{R}^n$ with the flat metric, this recovers the
parent (OQ-01) identity $dV_n/dr = S_{n-1}(r)$. The generalization
is intrinsically Riemannian: it holds **point-pointwise** for any
$(M, g)$ in the regime $r < \operatorname{inj}(p)$ where the
exponential map at $p$ is a diffeomorphism onto its image and the
distance function $d_g(p, \cdot)$ is smooth on $B_M(p, r) \setminus
\{p\}$.

### Three Sub-questions

The OQ literal text "Does the area-circumference duality generalize
to Riemannian manifolds via the co-area formula?" decomposes into
three nested questions:

1. **Q1 (Identity holds — mathematically settled, Mathlib-formalization open):**
   prove $dV/dr = A$ for $r < \operatorname{inj}(p)$ in a complete
   Riemannian manifold. The mathematical proof (via co-area applied
   to $d_g(p, \cdot)$, or equivalently via geodesic-polar Jacobian
   determinant) is in every Riemannian geometry textbook (Chavel,
   do Carmo, Petersen, Sakai). The Lean formalization gap is the
   **co-area formula itself**, which is not in Mathlib v4.26.0.

2. **Q2 (Bishop-Gromov comparison):** the standard Riemannian
   sharpening of Q1 is the **Bishop-Gromov volume comparison**
   theorem: if $\operatorname{Ric}_g \ge (n-1) K$, then $V_M(p, r)
   / V_{M_K}(r)$ is non-increasing in $r$, where $M_K$ is the
   simply-connected space form of constant sectional curvature $K$.
   Bishop-Gromov is a corollary of Q1 plus the Rauch comparison
   theorem. Formalizing it is a substantially larger project
   (~3000+ Lean lines).

3. **Q3 (smooth-radial Cavalieri):** the **dual formulation** of
   Q1 is $V_M(p, r) = \int_0^r A_M(p, t) \, dt$ for $0 \le r <
   \operatorname{inj}(p)$ — i.e., volume is the integral of surface
   area against radius. This is the Riemannian Cavalieri principle.
   Mathematically equivalent to Q1 modulo the Fundamental Theorem of
   Calculus, but a different formalization angle: one can prove the
   integral form directly via Fubini applied to geodesic normal
   coordinates, then derive Q1 from FTC. The integral form may be
   easier in Lean because it avoids differentiating a volume that is
   not obviously $C^1$ in $r$ a priori.

The minimum-viable formalization target is **Q1 in the special case
of an inner-product vector space** (where $M = E$ is a real inner
product space, $g$ is the canonical Riemannian metric on $E$, and
geodesic balls are honest Euclidean balls). Mathlib has the
`IsRiemannianManifold` predicate (Mathlib v4.26.0, by S. Gouëzel,
2025) on inner-product spaces, with `riemannianEDist` agreeing with
the standard distance. In this special case, Q1 reduces to the
parent's flat-space identity, but stated *intrinsically* using
`IsRiemannianManifold` infrastructure (rather than directly using
`Complex.volume_ball` as the parent does).

### Formal Statement (target form, R1 vector-space case)

```lean
import Mathlib.Geometry.Manifold.Riemannian.Basic

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

/-- For an inner product space with its canonical Riemannian metric,
the volume of the closed ball of radius `r` around `p`, viewed as a
function of `r`, has derivative equal to the surface area of the
sphere of radius `r` around `p`. -/
theorem riemannian_volumeBall_deriv_eq_surfaceArea
    (p : E) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun s : ℝ => (volume (Metric.closedBall p s)).toReal)
      ((surfaceMeasure E p r).toReal)
      r := by sorry
```

The target on a general Riemannian manifold (out of reach at v4.26.0,
estimated 2000-3000 Lean lines bridging Mathlib's distance-only
Riemannian API to a usable coarea theorem):

```lean
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [MeasureSpace M] [BorelSpace M]

theorem riemannian_volumeBall_deriv_eq_surfaceArea_manifold
    (p : M) {r : ℝ} (hr : 0 < r) (h_inj : r < injectivityRadius p) :
    HasDerivAt
      (fun s : ℝ => (volume (Metric.closedBall p s)).toReal)
      ((geodesicSphereMeasure I M p r).toReal)
      r := by sorry
```

This second target depends on **three Mathlib primitives that do not
exist at v4.26.0**: `injectivityRadius`, `geodesicSphereMeasure`, and
the co-area formula. The OBSERVE survey below treats this as the
strategic horizon, with the inner-product-space case as the concrete
S2-S5 target.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - geometry
  - riemannian
  - co-area
  - calculus
  - measure-theory
  - manifold
  - exponential-map
  - jacobi-field
```

**Significance**: 6/10 — moderate-high. The Riemannian generalization
of the area-derivative-of-volume identity is a foundational tool of
**comparison geometry** (Bishop, Gromov, Cheeger-Colding), of
**volume entropy** (Gromov's filling invariants), and of **Ricci
curvature lower bounds** (Lott-Sturm-Villani's synthetic Ricci). A
formalized version unlocks a wide downstream theory. Currently no
existing Mathlib infrastructure addresses any of this; the entry is
a foundational gap-filler rather than a single theorem deliverable.

**Tractability**: 5/10 — moderate. The **vector-space special case**
(Q1 restricted to $M = E$, an inner product space) is within S2-S5
reach (~500-700 Lean lines) because it reduces to the parent OQ-01
identity wrapped in `IsRiemannianManifold` API. The **general
Riemannian case** is OUT OF REACH at v4.26.0: Mathlib has the
`IsRiemannianManifold` predicate (Gouëzel 2025) but no
`injectivityRadius`, no `geodesicBall`, no `geodesicSphereMeasure`,
no `coarea` formula, no `expMap`, and no Jacobi fields. Each of
these is a substantial Mathlib contribution in its own right.

## Three Routes

### R1 — Vector-space special case (recommended for S2-S5)

Establish Q1 in the case $M = E$ for $E$ a finite-dimensional inner
product space with the canonical Riemannian metric. Use Mathlib's
`IsRiemannianManifold 𝓘(ℝ, E) E` instance and `riemannianEDist`
which agrees with the standard distance.

Pipeline:

1. **Setup** (S2, ~100 lines): in `Proofs/CircumferenceViaDifferentiationOQ03.lean`,
   open the `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
   [MeasureSpace E]` context. Verify (or rederive) that Lebesgue
   measure on $E$ coincides with the Riemannian volume from the
   inner-product metric.
2. **Volume-of-ball** (S3, ~150 lines): bridge `volume (Metric.closedBall
   p r)` to the parent's `nBallVolumeFn n r` from
   `CircumferenceViaDifferentiationOQ01.lean`. The bridge factors
   through translation invariance (`volume_closedBall_eq_volume_zero`)
   plus rescaling (`closedBall_rescale`); volume of the **unit** ball
   at the **origin** is then `unitBallVolume_apply` from Mathlib.
3. **Surface measure** (S4, ~200 lines): define `surfaceMeasure E p r`
   as the (n-1)-Hausdorff measure (`Measure.Hausdorff` in
   `Mathlib.MeasureTheory.Measure.Hausdorff`) restricted to
   $S(p, r) = \{x : \|x - p\| = r\}$. Verify it agrees with the
   parent's `nSphereSurfaceFn n r` via the spherical-coordinate
   change of variables.
4. **Derivative** (S5, ~100 lines): apply the parent's
   `nBallVolumeFn_hasDerivAt n r` and bridge through the volume
   identifications established in S3-S4.

Total: ~550-700 Lean lines, 0 sorries, 0 axioms (modulo Mathlib API
availability for `surfaceMeasure` — see knowledge.md).

### R2 — Full Riemannian manifold via co-area (long-term, ~3000+ lines)

Treat the OQ literal text: prove Q1 on a general complete Riemannian
manifold via the co-area formula. This requires extensive Mathlib
infrastructure that **does not exist at v4.26.0**:

| Primitive | Status at v4.26.0 |
|-----------|--------------------|
| `IsRiemannianManifold I M`              | ✓ (Mathlib.Geometry.Manifold.Riemannian.Basic, S. Gouëzel 2025) |
| `riemannianEDist I p q`                 | ✓ (PathELength.lean) |
| `expMap : TangentSpace I p → M`         | ✗ (would need geodesic ODE existence + uniqueness) |
| `injectivityRadius : M → ℝ`             | ✗ |
| `geodesicBall p r`, `geodesicSphere p r` | ✗ |
| `geodesicVolume : Measure M`             | ✗ (Mathlib has `MeasureTheory.Measure.AddHaar.MeasureSpace` for vector spaces but not a Riemannian volume) |
| `coarea` formula                        | ✗ (closest cousin: `integral_image_eq_integral_abs_deriv_smul` for ℝ → ℝ Lipschitz; no $n$-dim version) |
| Bishop-Gromov / Rauch comparison        | ✗ |

Each primitive is independently a ~500-1500 line Mathlib contribution.
R2 is therefore framed as a **roadmap**, not a single-session deliverable.
The S∞ recommendation is to seed Mathlib PRs for `injectivityRadius`,
`geodesicBall`, and `coarea` separately, then return to this OQ.

### R3 — Coarea formula in ℝⁿ as a Mathlib contribution (~1500-2500 lines)

The minimum Mathlib-contribution detour that would discharge OQ-03
fully (without the full Riemannian-manifold machinery) is the
**coarea formula in $\mathbb{R}^n$**:

> For $f : \mathbb{R}^n \to \mathbb{R}$ Lipschitz and $g : \mathbb{R}^n
> \to \mathbb{R}$ integrable,
> $$\int_{\mathbb{R}^n} g(x) \, |\nabla f(x)| \, dx = \int_{\mathbb{R}}
> \left( \int_{f^{-1}(t)} g(x) \, d\mathcal{H}^{n-1}(x) \right) dt.$$

Applying this with $f(x) = \|x - p\|$ and $g \equiv \mathbb{1}_{B(p,
r)}$ (and using $|\nabla \|x - p\|| = 1$ a.e.) gives
$$V_n(r) = \int_0^r A_{n-1}(t) \, dt,$$
which by FTC yields $V'_n(r) = A_{n-1}(r)$ — the parent identity,
**stated and proved via the coarea formula** rather than via the
explicit polynomial-in-$r$ formula. This is the OQ-03 question in
its sharpest formalizable form.

Mathlib has `MeasureTheory.Integral.Layercake` for the **distribution-function**
form of the coarea formula (the special case $f(x) = g(x)$), which
gives $\int g \, dx = \int_0^\infty |\{g > t\}| \, dt$. The general
coarea formula (above) is **strictly stronger** and is not in
Mathlib v4.26.0. R3 would add it.

**Net effect of R3 in the gallery**: the parent's elementary
polynomial-derivative proof would be supplemented by a coarea-based
proof, exhibiting the same identity in two formalisms. This is
substantial pedagogical value (the parent's proof is calculus, the
coarea proof is measure theory + functional analysis) without
requiring full Riemannian-manifold infrastructure.

## Mathlib Infrastructure Map

### What exists (Mathlib v4.26.0 at pinned revision 2df2f015)

- **`Mathlib.Geometry.Manifold.Riemannian.Basic`** (S. Gouëzel 2025):
  the `IsRiemannianManifold I M` Prop-valued typeclass, with the
  characterization `edist x y = riemannianEDist I x y`. Inner product
  vector spaces $E$ satisfy `IsRiemannianManifold 𝓘(ℝ, E) E`
  automatically via `EMetricSpace.ofRiemannianMetric`.
- **`Mathlib.Geometry.Manifold.Riemannian.PathELength`**: path
  length for piecewise-$C^1$ paths; `riemannianEDist I x y` defined
  as the infimum of path lengths.
- **`Mathlib.Geometry.Manifold.VectorBundle.Riemannian`**: smooth
  inner-product bundles + the `RiemannianBundle` data class.
- **`Mathlib.MeasureTheory.Measure.Hausdorff`**: $d$-dimensional
  Hausdorff measure `Measure.hausdorffMeasure d` on a metric space.
  Compatible with submanifolds of $\mathbb{R}^n$ in the sense that
  the Hausdorff measure of a $C^1$ embedded $k$-submanifold equals
  its parameterized integral.
- **`Mathlib.MeasureTheory.Integral.Layercake`**: the distribution
  function version of coarea. Specifically `MeasureTheory.lintegral_eq_lintegral_meas_le`
  gives $\int g \, dx = \int_0^\infty \mu\{g > t\} \, dt$ for
  nonneg measurable $g$. This is the $f = g$ degenerate case of the
  full coarea formula.
- **`Mathlib.Analysis.NormedSpace.lpSpace`** plus
  **`Mathlib.Analysis.Calculus.ContDiff.Basic`**: smooth-function
  infrastructure on inner product spaces. `‖·‖` is smooth away from
  the origin via `differentiable_norm_sq` and `ContDiff.norm` of
  varying regularity.
- **`Mathlib.Analysis.SpecialFunctions.Gamma.Basic`**: `Real.Gamma`,
  `Gamma_add_one`, `Gamma_one_half_eq` — supplies the constants
  $\omega_n = \pi^{n/2}/\Gamma(n/2+1)$ used in the parent.
- **`Mathlib.MeasureTheory.Constructions.HaarToSphere`**: the
  spherical-coordinate decomposition `Measure.volume = ∫⁻ r in
  (0, ∞), r^(n-1) ∂(unitSphereMeasure)` for $\mathbb{R}^n$.
  *This is the key existing primitive for R1.* Specifically, the
  identity `Measure.haarMeasure_volume_radial_decomposition` (or
  the explicit lemma `volume_pi_le_pow_sphereMeasure` — exact name
  may vary at the pinned rev) gives the integration-by-spheres
  decomposition we need.

### What is MISSING (Mathlib v4.26.0)

- **No `injectivityRadius` definition** on a Riemannian manifold.
- **No `expMap` / exponential map** definition. The geodesic ODE is
  not constructed at v4.26.0.
- **No `geodesicBall` / `geodesicSphere` / `geodesicVolume`**.
- **No coarea formula in any dimension $> 1$.** Mathlib has
  `integral_image_eq_integral_abs_deriv_smul` for $f : \mathbb{R} \to
  \mathbb{R}$ Lipschitz (the $n = 1$ case, equivalent to substitution
  in $\int_a^b f(g(x)) g'(x) \, dx = \int_{g(a)}^{g(b)} f(u) \, du$),
  but no $n$-dimensional version.
- **No surface measure on a sphere as a named Mathlib object**
  separate from $(n-1)$-Hausdorff measure. The identification
  $\mu_S = \mathcal{H}^{n-1}|_S$ for a sphere $S \subset \mathbb{R}^n$
  needs an explicit bridge lemma.
- **No Bishop-Gromov / Rauch comparison**.
- **No Jacobi fields** (which are how Riemannian-geometry textbooks
  prove the radial Jacobian of $\exp_p$ is $\det(J(r))$ for Jacobi
  fields $J$, the geometric content behind coarea on a manifold).

### Critical bridge lemma (S3 deliverable for R1)

The single lemma that connects Mathlib's spherical decomposition to
the parent's polynomial volume formula:

```lean
/-- Volume of a Euclidean closed ball equals the polynomial nBallVolumeFn. -/
theorem volume_closedBall_eq_nBallVolumeFn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      nBallVolumeFn (Module.finrank ℝ E) r := by sorry
```

A close cousin (`Complex.volume_ball` for the 2D case) is used in
the parent file `CircumferenceViaDifferentiation.lean` line 78-102.
For general $n$, the parent OQ-01 file uses `unitBallVolume_apply`
which gives the unit ball's volume; scaling by $r^n$ requires
**`Measure.addHaar_closedBall`** or equivalent rescaling lemma.

## Known Results (literature)

### Proven (mathematically)

- **Co-area formula in $\mathbb{R}^n$** (Federer 1959, Kronrod 1950):
  for Lipschitz $f : \mathbb{R}^n \to \mathbb{R}$ and integrable $g$,
  $\int g |\nabla f| \, dx = \int_\mathbb{R} \int_{f^{-1}(t)} g \,
  d\mathcal{H}^{n-1} \, dt$.
- **Riemannian co-area formula** (Federer 1959, expanded by Brothers
  1986 for manifold targets): same identity on a Riemannian manifold,
  with $|\nabla f|$ the Riemannian gradient norm.
- **Polar decomposition of Riemannian volume** (Gauss-Bonnet
  prehistory; explicit in Helgason 1962, Chavel 1984):
  $dV_g = J(r, \theta) \, dr \, d\theta$ in geodesic polar
  coordinates, where $J(r, \theta) = r^{n-1} \cdot
  (\det \text{Jac}(\exp_p))(r\theta)$.
- **Bishop-Gromov volume comparison** (Bishop 1963; Gromov 1981):
  if $\operatorname{Ric}_g \ge (n-1) K g$, then
  $V_M(p, r) / V_{M_K}(r)$ is non-increasing.
- **Parent gallery proof** `CircumferenceViaDifferentiation.lean`
  (`area-of-circle` companion, verified 0/0/199 lines): $C(r) =
  \frac{d}{dr} A(r)$ for the Euclidean disk.
- **Parent OQ-01 gallery proof** `CircumferenceViaDifferentiationOQ01.lean`
  (verified 0/0/240 lines): $S_{n-1}(r) = \frac{d}{dr} V_n(r)$ for
  all $n$ via Mathlib's Gamma function and `unitBallVolume`.

### Open (Lean formalization)

- The **coarea formula in dimension $> 1$** is not in Mathlib v4.26.0.
- The **vector-space case** of OQ-03 (R1 above) is formalizable
  using existing Mathlib but has not been written.
- The **Bishop-Gromov inequality** is not in Mathlib.
- **All of comparison geometry** (Rauch, Toponogov, Cheeger-Colding)
  is absent.

## Path Decomposition (proposed for R1, vector-space case)

| Stage | Deliverable | Lines (est.) |
|-------|-------------|-------------|
| S1 | This OBSERVE survey (text-only, no Lean) | — |
| S2 | `Proofs/CircumferenceViaDifferentiationOQ03.lean` — `RiemannianBall` context setup + `volume`-of-ball bridge | ~150 |
| S3 | Surface-measure bridge: `surfaceMeasure E p r` via Hausdorff `n - 1`-measure | ~200 |
| S4 | Composition with parent OQ-01's `nSphereSurfaceFn_hasDerivAt` | ~100 |
| S5 | Main theorem `riemannian_volumeBall_deriv_eq_surfaceArea` | ~100 |
| S6+ | Stretch: explicit special cases ($E = \mathbb{R}^2, \mathbb{R}^3$) via parent identities | ~80 each |
| S∞ | R2 Mathlib roadmap PRs (injectivityRadius, expMap, coarea, geodesicBall) | ~3000+ |

## Numerical Sanity (Euclidean special cases)

The vector-space case must recover the parent identities exactly:

| Dim $n$ | $V_n(r)$ | $A_{n-1}(r) = V'_n(r)$ | Sanity (at $r = 1$) |
|---------|----------|---------------------|------------------|
| 1 | $2r$ | $2$ | $V'_1(1) = 2$ ✓ |
| 2 | $\pi r^2$ | $2\pi r$ | $V'_2(1) = 2\pi$ ✓ (parent) |
| 3 | $\frac{4}{3}\pi r^3$ | $4\pi r^2$ | $V'_3(1) = 4\pi$ ✓ |
| 4 | $\frac{1}{2}\pi^2 r^4$ | $2\pi^2 r^3$ | $V'_4(1) = 2\pi^2$ ✓ |
| 5 | $\frac{8}{15}\pi^2 r^5$ | $\frac{8}{3}\pi^2 r^4$ | $V'_5(1) = \frac{8}{3}\pi^2$ ✓ |
| 6 | $\frac{\pi^3 r^6}{6}$ | $\pi^3 r^5$ | $V'_6(1) = \pi^3$ ✓ |

All six match the parent OQ-01 file's verified `volume_n_unit` and
`surface_n_unit` constants. The R1 deliverable must not introduce
any new numerical claims — it must factor through these existing
verified constants.

## Curvature Sanity (Riemannian case, future reference)

For the unit 2-sphere $S^2$ with the round metric, $K \equiv 1$,
the geodesic ball $B(p, r)$ for $r < \pi$ has

- $V_{S^2}(p, r) = 2\pi (1 - \cos r)$, so $V'_{S^2}(p, r) = 2\pi
  \sin r$.
- $A_{S^2}(p, r) = 2\pi \sin r$ (length of the latitude circle at
  geodesic distance $r$ from the pole).

The identity $V'(r) = A(r)$ holds explicitly: $\frac{d}{dr} [2\pi
(1 - \cos r)] = 2\pi \sin r = A(r)$ ✓. The bound $r < \operatorname{inj}(p)
= \pi$ is sharp; at $r = \pi$ the sphere $S(p, \pi)$ degenerates to
the antipode point and $A = 0$, while $V_{S^2}(p, \pi) = 4\pi$ is
the full sphere volume and $V'(\pi^-) = 2\pi \sin \pi = 0$, also ✓
consistent.

For hyperbolic space $\mathbb{H}^n$ with $K \equiv -1$:

- $V_{\mathbb{H}^2}(p, r) = 2\pi (\cosh r - 1)$, $V'(r) = 2\pi \sinh
  r$, $A_{\mathbb{H}^2}(p, r) = 2\pi \sinh r$ ✓.

These are the constant-curvature reference cases; the full Bishop-Gromov
theorem (Q2) bounds the general Riemannian case between $\mathbb{R}^n$
and the relevant space form.

## References

- C. F. Gauss, *Disquisitiones generales circa superficies curvas*
  (1827) — origin of intrinsic Riemannian geometry; the radial-area
  formula for surfaces is implicit in Section 13.
- H. Federer, *Curvature measures*, Trans. AMS **93** (1959), 418-491
  — co-area formula, original proof.
- A. S. Kronrod, *On functions of two variables*, Uspekhi Mat. Nauk
  **5** (1950) — earlier independent statement of co-area for $n = 2$.
- I. Chavel, *Riemannian Geometry: A Modern Introduction* (Cambridge
  Studies in Advanced Mathematics 98, 2nd ed. 2006) — standard
  textbook reference for the geodesic-polar decomposition (Ch. 3)
  and Bishop-Gromov (Ch. 4).
- M. P. do Carmo, *Riemannian Geometry* (Birkhäuser 1992) — Ch. 6
  Jacobi fields, Ch. 9 volume comparison; Section 9.2 contains the
  $dV/dr = A$ identity for geodesic balls.
- L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties
  of Functions* (Studies in Advanced Mathematics, 2nd ed. 2015) —
  Ch. 3 of the co-area formula in $\mathbb{R}^n$, formulation closest
  to what an R3 Mathlib contribution would target.
- M. Gromov, *Metric Structures for Riemannian and Non-Riemannian
  Spaces* (Birkhäuser 1999) — Bishop-Gromov volume monotonicity
  framed in the synthetic-Ricci tradition.
- S. Gouëzel, `Mathlib.Geometry.Manifold.Riemannian.Basic` (2025) —
  the `IsRiemannianManifold` predicate as added to Mathlib.
- Parent file: `proofs/Proofs/CircumferenceViaDifferentiation.lean`
  (Lean Genius, 2026-05-04, verified).
- Sibling file: `proofs/Proofs/CircumferenceViaDifferentiationOQ01.lean`
  (Lean Genius, 2026-05-06, verified).

## Honesty / Calibration

This S1 OBSERVE is **doc-only** (no Lean modifications). The
mathematical content of OQ-03 (Q1, Q2, Q3 above) is classical and
well-documented. The Lean formalization is **gated by the absence
of fundamental Mathlib infrastructure**: in particular, the
$n$-dimensional coarea formula, geodesic balls / spheres /
exponential map / injectivity radius are all missing at v4.26.0.

The recommended S2 target (R1, vector-space case) is the minimum
viable formalization that exhibits the OQ identity intrinsically
within Mathlib's Riemannian framework, **without** requiring any
manifold-side primitives. It will deliver $\sim 500$ Lean lines, 0
sorries, 0 axioms, and will explicitly call out the manifold
generalization as future work.

The OQ-03 question's literal Riemannian generalization is the R2/R3
roadmap — accurate to flag as **out of single-session reach** at the
pinned revision. The OBSERVE survey is the right level of contribution
for this OQ at this moment in Mathlib history.

## Anti-Targets (do NOT attempt in S2-S5)

- **Do not write a coarea formula in dimension $> 1$.** That is a
  ~1500+ line Mathlib contribution (R3 above), out of scope.
- **Do not define `expMap`, `injectivityRadius`, `geodesicBall`,
  `geodesicSphere`.** Each is a ~500+ line Mathlib contribution.
- **Do not attempt Bishop-Gromov or Rauch comparison.** Each is a
  ~1000+ line contribution dependent on Jacobi field theory which
  itself is absent from Mathlib.
- **Do not rewrite the parent `CircumferenceViaDifferentiation.lean`
  or `CircumferenceViaDifferentiationOQ01.lean`.** These are verified
  and stable; OQ-03 builds *on top of them*, not as a replacement.
- **Do not introduce axioms.** The deliverable target is verified
  status (`status: verified, axiomCount: 0`); if a stage cannot be
  discharged sorry-free, halt and re-scope rather than introducing
  an axiom.

## No-Edit Guarantee (this S1)

This S1 OBSERVE iteration modifies ONLY:

- `research/problems/circumference-via-differentiation-oq-03/problem.md` (new)
- `research/problems/circumference-via-differentiation-oq-03/knowledge.md` (new)
- `research/problems/circumference-via-differentiation-oq-03/state.md` (new)
- `src/data/research/problems/circumference-via-differentiation-oq-03.json` (new)

No `proofs/`, `src/data/proofs/`, `proofs/Proofs.lean`, or any
parent-proof file is touched. No Lean compilation is required for
this PR.
