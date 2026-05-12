# Knowledge: circumference-via-differentiation-oq-03 — Riemannian dV/dr = A via co-area

## S1 OBSERVE (researcher-9, 2026-05-12)

### Session Summary

OBSERVE iteration on the third open question of the parent gallery
proof `circumference-via-differentiation`. The OQ literally asks
"Does the area-circumference duality generalize to Riemannian
manifolds via the co-area formula?" — i.e., whether $\frac{d}{dr}
V_M(p, r) = A_M(p, r)$ holds for the volume $V$ and surface area $A$
of geodesic balls/spheres in a Riemannian manifold, in the regime $r
< \operatorname{inj}(p)$.

Mathematically the answer is YES (Federer 1959, Chavel 1984), but
Mathlib at v4.26.0 lacks the foundational primitives required to
state, let alone prove, the manifold-side identity. The OBSERVE
session decomposes the OQ into Q1/Q2/Q3 sub-questions, audits
Mathlib for the relevant infrastructure, and recommends a vector-space
restriction (R1) as the S2-S5 deliverable while keeping the full
Riemannian generalization (R2/R3) on the long-term roadmap.

The slug was seeker-selected via batch PR #18337 (seeker/batch-20260512T205304,
opened 2026-05-12T22:37:30Z, ~2h prior to S1 claim) with 0 prior
research PRs / branches; this is the first researcher iteration.

S1 establishes:

1. **The Riemannian identity is mathematically classical and
   well-documented** (Chavel Riemannian Geometry §3.4; do Carmo §9.2;
   Sakai §I.10). The proof flows from the co-area formula applied to
   $d_g(p, \cdot)$ using $|\nabla d_g(p, \cdot)|_g = 1$ a.e.; or
   equivalently from the geodesic-polar Jacobian determinant
   decomposition $dV_g = J(r, \theta) \, dr \, d\theta$.

2. **Mathlib v4.26.0 has the `IsRiemannianManifold` predicate** (S.
   Gouëzel, 2025) — `Mathlib.Geometry.Manifold.Riemannian.Basic` —
   but lacks the manifold-side primitives needed to state the
   identity: no `expMap`, no `injectivityRadius`, no `geodesicBall`
   / `geodesicSphere`, no Riemannian volume measure, no co-area
   formula in dimension $> 1$.

3. **Three discharge routes** (R1 vector-space special case — the
   only one tractable in S2-S5, ~500-700 lines; R2 full Riemannian
   manifold via co-area — ~3000+ lines, gated by Mathlib gaps; R3
   coarea formula in $\mathbb{R}^n$ as a standalone Mathlib
   contribution — ~1500-2500 lines).

4. **R1 (recommended S2-S5)**: prove the Q1 identity for $M = E$
   inner-product space using `IsRiemannianManifold 𝓘(ℝ, E) E`. The
   proof bridges Mathlib's `Metric.closedBall` volume to the parent
   OQ-01's `nBallVolumeFn` and Hausdorff $(n-1)$-measure on the
   sphere to the parent OQ-01's `nSphereSurfaceFn`. Two critical
   bridge lemmas required:

   - `volume_closedBall_eq_nBallVolumeFn` (S3): Lebesgue volume of a
     closed ball equals the parent's polynomial-in-$r$ formula.
   - `hausdorffMeasure_sphere_eq_nSphereSurfaceFn` (S4): $(n-1)$-Hausdorff
     measure of a sphere equals the parent's polynomial-in-$r$
     surface formula.

5. **Numerical sanity**: the $V'_n(r) = A_{n-1}(r)$ identity is
   verified at $n \in \{1, 2, 3, 4, 5, 6\}$ via the parent OQ-01
   formulas, and at $K \in \{+1, -1\}$ via the curvature-1 sphere
   $S^2$ ($V = 2\pi(1 - \cos r)$, $V' = 2\pi \sin r = A$) and the
   curvature-$-1$ hyperbolic plane $\mathbb{H}^2$ ($V = 2\pi(\cosh
   r - 1)$, $V' = 2\pi \sinh r = A$).

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

### Mathematical Background

#### Co-Area Formula (Federer 1959)

Let $f : \mathbb{R}^n \to \mathbb{R}$ be Lipschitz and $g :
\mathbb{R}^n \to \mathbb{R}$ measurable with $g \cdot |\nabla f|$
integrable. Then

$$\int_{\mathbb{R}^n} g(x) |\nabla f(x)| \, dx = \int_{-\infty}^{\infty}
\left( \int_{f^{-1}(t)} g(x) \, d\mathcal{H}^{n-1}(x) \right) dt.$$

The integrand $g \cdot |\nabla f|$ on the left is on $\mathbb{R}^n$
under Lebesgue measure; the right-hand integral is over $\mathbb{R}$
with the inner integral over the level set $f^{-1}(t)$ under $(n-1)$-Hausdorff
measure $\mathcal{H}^{n-1}$.

**Specialization to $f(x) = \|x - p\|$ and $g \equiv \mathbb{1}_{B(p, r)}$**.
The Euclidean norm is 1-Lipschitz with $|\nabla \|x\|| = 1$ for $x
\neq 0$ (and is non-differentiable only at $x = 0$, which is a
Lebesgue-null set so doesn't affect the integral). The level set
$\{\|x - p\| = t\}$ is the sphere $S(p, t)$. The indicator
$\mathbb{1}_{B(p,r)}(x) = 1$ iff $\|x - p\| \le r$, so the LHS is
$V_n(r)$ and the RHS becomes $\int_0^r \mathcal{H}^{n-1}(S(p, t))
\, dt = \int_0^r A_{n-1}(t) \, dt$. Concluding:

$$V_n(r) = \int_0^r A_{n-1}(t) \, dt, \quad \text{whence } V'_n(r) = A_{n-1}(r) \text{ by FTC}.$$

#### Riemannian Co-Area Formula

Let $(M, g)$ be a Riemannian $n$-manifold, $f : M \to \mathbb{R}$
Lipschitz, $\phi : M \to \mathbb{R}$ integrable. Then

$$\int_M \phi |\nabla_g f| \, dV_g = \int_{-\infty}^{\infty}
\left( \int_{f^{-1}(t)} \phi \, d\mathcal{H}^{n-1}_g \right) dt,$$

with $|\nabla_g f|$ the Riemannian gradient norm and $\mathcal{H}^{n-1}_g$
the $(n-1)$-Hausdorff measure under the metric $d_g$.

**Specialization to $f(x) = d_g(p, x)$ and $\phi \equiv \mathbb{1}_{B_M(p, r)}$**.
On the regime $r < \operatorname{inj}(p)$, the distance function
$d_g(p, \cdot)$ is smooth on $M \setminus \{p\}$ and satisfies
$|\nabla_g d_g(p, \cdot)|_g = 1$ pointwise. The level set $\{x :
d_g(p, x) = t\}$ for $t < \operatorname{inj}(p)$ is the geodesic
sphere $S_M(p, t)$, an embedded $(n-1)$-submanifold. The Hausdorff
$\mathcal{H}^{n-1}_g$ measure restricted to $S_M(p, t)$ equals the
induced Riemannian surface volume $A_M(p, t)$. Concluding:

$$V_M(p, r) = \int_0^r A_M(p, t) \, dt, \quad V'_M(p, r) = A_M(p, r).$$

#### Geodesic-Polar Coordinate Alternative

The same identity is derivable without invoking co-area, via the
**geodesic-polar Jacobian**. Set up: in the regime $r <
\operatorname{inj}(p)$, the exponential map $\exp_p : T_pM \to M$
is a diffeomorphism onto $B_M(p, r)$. Pulling back the Riemannian
volume $dV_g$ via $\exp_p$ to $T_pM \cong \mathbb{R}^n$ gives

$$\exp_p^*(dV_g) = J(r, \theta) \, dr \, d\theta_{S^{n-1}},$$

where $(r, \theta)$ are polar coordinates on $T_pM$, $d\theta_{S^{n-1}}$
is the standard volume form on the unit sphere in $T_pM$, and
$J(r, \theta) = r^{n-1} \cdot |\det \text{Jac}(\exp_p)(r\theta)|$ is
the **geodesic-radial Jacobian**. The factor $r^{n-1}$ is the
Euclidean spherical Jacobian; the $|\det \text{Jac}(\exp_p)|$ factor
captures the metric distortion, which is described by **Jacobi
fields** $J(t)$ along the radial geodesic $t \mapsto \exp_p(t\theta)$.

By Fubini in $(r, \theta)$:

$$V_M(p, r) = \int_0^r \int_{S^{n-1}} J(s, \theta) \, d\theta \, ds.$$

Defining $A_M(p, s) = \int_{S^{n-1}} J(s, \theta) \, d\theta$ as the
surface area at radius $s$, we get $V_M(p, r) = \int_0^r A_M(p, s)
\, ds$, hence $V'_M(p, r) = A_M(p, r)$ by FTC.

Both derivations are equivalent; the co-area derivation is more
analytic (uses $|\nabla d|$ as the relevant Jacobian factor), the
geodesic-polar derivation is more geometric (uses the explicit
parametrization $\exp_p$).

#### The Constant-Curvature Reference Cases

| Curvature $K$ | Manifold | $V(p, r)$ | $A(p, r) = V'(p, r)$ |
|----|----|----|----|
| $0$ | $\mathbb{R}^2$ | $\pi r^2$ | $2\pi r$ |
| $+1$ | Unit sphere $S^2$ | $2\pi (1 - \cos r)$, $r < \pi$ | $2\pi \sin r$ |
| $-1$ | Hyperbolic plane $\mathbb{H}^2$ | $2\pi (\cosh r - 1)$ | $2\pi \sinh r$ |
| $0$ | $\mathbb{R}^3$ | $\frac{4}{3}\pi r^3$ | $4\pi r^2$ |
| $+1$ | $S^3$ | $\pi(2r - \sin 2r)$, $r < \pi$ | $4\pi \sin^2 r$ |
| $-1$ | $\mathbb{H}^3$ | $\pi(\sinh 2r - 2r)$ | $4\pi \sinh^2 r$ |

Direct check at $n = 2$: $\frac{d}{dr}[2\pi(1 - \cos r)] = 2\pi
\sin r$ ✓; $\frac{d}{dr}[2\pi(\cosh r - 1)] = 2\pi \sinh r$ ✓. These
exact formulas are the **space form volume formulas**
$V_K(r) = \int_0^r A_K(s) \, ds$ with $A_K(s) = (n-1) \omega_{n-1}
\cdot s_K(s)^{n-1}$ where $s_K(s) = \sin(\sqrt{K} s)/\sqrt{K}$ for
$K > 0$, $s$ for $K = 0$, $\sinh(\sqrt{|K|} s)/\sqrt{|K|}$ for
$K < 0$. These are the cases against which Bishop-Gromov compares
the general Riemannian volume.

### Mathlib API Surface (v4.26.0 at rev 2df2f015)

#### Available

| Component | Module | Status |
|-----------|--------|--------|
| `IsRiemannianManifold I M` | `Mathlib.Geometry.Manifold.Riemannian.Basic` | ✓ (S. Gouëzel 2025) |
| `riemannianEDist I x y` | `…Riemannian.PathELength` | ✓ |
| `EMetricSpace.ofRiemannianMetric` | `…Riemannian.Basic` | ✓ |
| Canonical Riemannian metric on `[InnerProductSpace ℝ E]` | `…Riemannian.Basic` | ✓ |
| `Measure.hausdorffMeasure d` | `Mathlib.MeasureTheory.Measure.Hausdorff` | ✓ |
| `Measure.haarMeasure_volume_radial_decomposition` (or equivalent) | `Mathlib.MeasureTheory.Constructions.HaarToSphere` | ✓ |
| `volume (Metric.closedBall p r)` on $\mathbb{R}^n$ | `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` plus `EuclideanSpace.volume_closedBall` family | ✓ |
| `Complex.volume_ball`, `Complex.volume_closedBall` | `Mathlib.Analysis.SpecialFunctions.Complex.Circle` (parent file uses this) | ✓ (2D special case) |
| `unitBallVolume`, `unitBallVolume_apply` | `Mathlib.Analysis.SpecialFunctions.Volume.Basic` (parent OQ-01 file uses this) | ✓ |
| `Measure.addHaar_closedBall` (rescaling) | `Mathlib.MeasureTheory.Measure.Haar.NormedSpace` | ✓ |
| `Measure.addHaar_smul` (Haar measure under scaling) | as above | ✓ |
| `lintegral_eq_lintegral_meas_le` (distribution-function form) | `Mathlib.MeasureTheory.Integral.Layercake` | ✓ (degenerate coarea) |
| `integral_image_eq_integral_abs_deriv_smul` (substitution, 1D) | `Mathlib.MeasureTheory.Function.LpSeminorm.Trim` | ✓ (degenerate coarea, $n = 1$) |

#### Missing (would need Mathlib contributions)

| Component | Estimated effort | Notes |
|-----------|------------------|-------|
| `injectivityRadius (p : M)` | ~500 lines | Requires geodesic ODE flow; classical definition is the supremum of $r$ such that $\exp_p$ is a diffeomorphism on $B_{T_pM}(0, r)$ |
| `expMap : TangentSpace I p → M` | ~1000 lines | Requires Picard-Lindelöf on the geodesic ODE $\nabla_{\dot\gamma} \dot\gamma = 0$; uniqueness needs Riemannian connection theory |
| `geodesicBall p r`, `geodesicSphere p r` | ~200 lines (given expMap) | Image of `expMap` restricted to the Euclidean ball |
| `RiemannianMeasure : Measure M` | ~800 lines | Volume element $\sqrt{\det g}$ in local coordinates; existence of a global measure requires partition-of-unity arguments |
| Coarea formula on $\mathbb{R}^n$ (general $n$) | ~1500 lines | Federer's classical proof requires the area formula plus density arguments |
| Coarea formula on a Riemannian manifold | ~3000 lines | Bootstrap on the $\mathbb{R}^n$ version plus partition-of-unity and the Riemannian gradient identification |
| Jacobi fields, Rauch comparison | ~2000 lines | Requires curvature tensor, second-variation formula |
| Bishop-Gromov inequality | ~1500 lines (given the above) | Comparison + volume monotonicity |

#### Key Bridges for R1 (S2-S5 deliverables)

For the vector-space special case (R1), the deliverable rests on
two non-trivial bridges:

**Bridge 1 (S3, ~150 lines)**: Lebesgue volume of a closed ball in
$E$ equals the parent OQ-01 polynomial formula $\omega_n r^n$.

```lean
theorem volume_closedBall_eq_nBallVolumeFn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  -- Translation invariance: volume (closedBall p r) = volume (closedBall 0 r)
  rw [Measure.addHaar_closedBall_eq_addHaar_closedBall_zero]
  -- Rescaling: volume (closedBall 0 r) = r^n · volume (closedBall 0 1)
  rw [Measure.addHaar_closedBall_smul_radius]
  -- volume (closedBall 0 1) = unitBallVolume = ω_n
  rw [parent_unitBallVolume_eq]
  -- ω_n · r^n = nBallVolumeFn n r
  rfl
```

The four ingredients (`addHaar_closedBall_eq_addHaar_closedBall_zero`,
`addHaar_closedBall_smul_radius`, `parent_unitBallVolume_eq`, the
final `rfl`) are all expected to be available or easy to derive. The
exact Mathlib lemma names may need adjustment based on the v4.26.0
API (e.g., `Measure.addHaar_smul_self` vs.
`Measure.addHaar_closedBall_smul_radius`); S2 verification pass.

**Bridge 2 (S4, ~200 lines)**: $(n-1)$-Hausdorff measure of the
sphere of radius $r$ in $E$ equals the parent OQ-01 polynomial
formula $S_{n-1}(r) = n \omega_n r^{n-1}$.

```lean
theorem hausdorffMeasure_sphere_eq_nSphereSurfaceFn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (p : E) (r : ℝ) (hr : 0 ≤ r) :
    (Measure.hausdorffMeasure (Module.finrank ℝ E - 1)
      (Metric.sphere p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn
        (Module.finrank ℝ E) r := by
  sorry  -- needs spherical-coordinate decomposition
```

This is the more delicate bridge. The standard derivation uses the
spherical-coordinate decomposition `Measure.volume = ∫⁻ r in (0,
∞), r^(n-1) ∂(unitSphereMeasure)` plus the identification of
`unitSphereMeasure` with $(n-1)$-Hausdorff measure on the unit
sphere. Mathlib's `HaarToSphere` provides one half of this; the
Hausdorff identification may require an explicit lemma not yet in
v4.26.0.

**Risk**: if Mathlib's spherical decomposition lemma at v4.26.0 is
stated with a non-Hausdorff sphere measure (e.g., the parametric
measure under a chart), Bridge 2 may need an additional ~100 lines
to establish the Hausdorff identification. S2 verification pass
required.

### Lean Skeleton Sketch for S2

```lean
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Proofs.CircumferenceViaDifferentiationOQ01

/-!
# Riemannian area-circumference duality (vector-space case)

This file establishes the area-circumference duality
`dV/dr = A` for closed balls in an inner-product vector space,
viewed as a Riemannian manifold via Mathlib's `IsRiemannianManifold`
predicate. Parent OQ-03 of `circumference-via-differentiation`.
-/

namespace CircumferenceViaDifferentiationOQ03

open MeasureTheory Measure Metric Real

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The Riemannian volume function on an inner product space, viewed
as `r ↦ volume (closedBall p r)` for a fixed center `p`. -/
noncomputable def riemannianVolumeBall (p : E) (r : ℝ) : ℝ :=
  (volume (Metric.closedBall p r)).toReal

/-- The Riemannian surface area function on an inner product space,
viewed as `r ↦ μ_{n-1}(sphere p r)` for a fixed center `p`. -/
noncomputable def riemannianSurfaceArea (p : E) (r : ℝ) : ℝ :=
  (Measure.hausdorffMeasure
    (Module.finrank ℝ E - 1)
    (Metric.sphere p r)).toReal

-- Bridge 1: volume agrees with parent OQ-01 polynomial.
theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    riemannianVolumeBall p r =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  sorry

-- Bridge 2: surface area agrees with parent OQ-01 polynomial.
theorem riemannianSurfaceArea_eq_nSphereSurfaceFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    riemannianSurfaceArea p r =
      CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn
        (Module.finrank ℝ E) r := by
  sorry

-- Main theorem: dV/dr = A for r > 0.
theorem riemannianVolumeBall_hasDerivAt_riemannianSurfaceArea
    (p : E) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (riemannianVolumeBall p) (riemannianSurfaceArea p r) r := by
  -- Bridge 1 + parent OQ-01 derivative + Bridge 2
  sorry

end CircumferenceViaDifferentiationOQ03
```

This is the **S2 ACT deliverable in skeleton form**: file structure
with three theorem stubs `sorry`-tagged, no proof attempts. S2's
concrete task is to (i) verify the import + variable boilerplate
compiles, (ii) discharge the structural elaboration of the
definitions (so they typecheck), (iii) leave the three proofs as
`sorry`. S3 handles Bridge 1; S4 handles Bridge 2; S5 composes them
into the main theorem.

### Parallel-Work Check

At time of S1 OBSERVE claim (researcher-9, 2026-05-12 ~22:50 UTC):

- `gh pr list --search "circumference-via-differentiation-oq-03"`:
  1 open PR (seeker batch init #18337, no content).
- `gh pr list --merged --search "…oq-03"`: 0 recent merges.
- `git branch -r | grep circumference`: only OQ-01 audit/research
  branches; no OQ-03 work in flight.
- `.lean/state/candidate-pool.json` candidate `id:
  circumference-via-differentiation-oq-03`: `status: available`,
  knowledge_score = 0 (EMPTY = pristine).

Pristine slug; no race risk.

### Anti-Targets (re-stated from problem.md)

- Do not write a coarea formula in dim $> 1$.
- Do not define `expMap`, `injectivityRadius`, `geodesicBall`,
  `geodesicSphere`, `RiemannianMeasure`.
- Do not attempt Bishop-Gromov, Rauch, or any comparison theorem.
- Do not modify parent or sibling proofs.
- Do not introduce axioms.

### Honesty Note

OQ-03 is fundamentally a **Riemannian-geometry-on-manifold**
question, and Mathlib's Riemannian infrastructure is too thin at
v4.26.0 to support the literal generalization. The R1 vector-space
restriction is an **honest partial answer**: it exhibits the
identity intrinsically within Mathlib's Riemannian framework, but
explicitly does NOT close the manifold version. The gallery entry
for OQ-03 should reflect this: title "Riemannian area-derivative-of-volume,
inner-product-space case" rather than the unrestricted "via co-area
formula." A README / overview section should call out the manifold
version as `formalized: false` with a roadmap pointer.

### Aristotle non-applicability

The R1 vector-space pipeline is NOT a routine Aristotle target. The
two key bridges (volume + Hausdorff-measure rescaling) both require
custom measure-theoretic arguments specific to the inner-product
geometry; Aristotle's strengths lie in routine algebraic / order /
arithmetic discharging, not in measure-theoretic identifications.
Plan all of S2-S5 as manual researcher iterations.

### Risk Register

1. **Bridge 2 (S4) may be harder than 200 lines** if Mathlib's
   spherical decomposition uses a non-Hausdorff sphere measure at
   v4.26.0. Mitigation: spend the first 30 min of S4 doing API audit
   on `HaarToSphere.lean`; if the measure is not Hausdorff, draft an
   intermediate bridge lemma identifying the parametric measure with
   $\mathcal{H}^{n-1}$ on the sphere.
2. **`Measure.addHaar_closedBall_smul_radius` may not exist** by
   that exact name. Mitigation: S2 audit; fall back to manual proof
   via `Measure.smul_closedBall` plus push-forward under scaling
   homeomorphism.
3. **`Complex.volume_ball` is 2D-specific**; the parent uses it,
   but R1 wants the general-$n$ identification. The parent OQ-01
   file's `volume_n_unit` (which gives `volume (Metric.closedBall 0
   1) = ω_n` for general $n$) may need to be exposed or generalized.
   Mitigation: S2 verifies that the parent OQ-01 file already
   exposes the generalized volume identification; if not, add a
   one-line lemma re-exporting it.
4. **`MeasureSpace E` typeclass requirement** may not auto-resolve
   for arbitrary inner product spaces — Mathlib often requires
   `FiniteDimensional ℝ E` plus explicit `[MeasureSpace E]
   [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]`
   instances. Mitigation: pin variables explicitly; document the
   typeclass shape in S2.

### Next Action (for S2 researcher)

Create `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`
with:

1. Header docstring matching the parent OQ-01 style.
2. The three imports listed above.
3. The `riemannianVolumeBall` and `riemannianSurfaceArea` definitions.
4. The three theorem stubs with `sorry` proofs.
5. Add an entry in `proofs/Proofs.lean`.
6. Add `src/data/proofs/circumference-via-differentiation-oq-03/{meta.json,
   index.ts, annotations.json}` with status `formalized` (since
   sorries remain) — NOT `verified` or `axiomatized`.
7. Update `src/data/research/problems/circumference-via-differentiation-oq-03.json`:
   phase `OBSERVE → ACT`, iteration `1 → 2`, S2 summary.

Build verification: `./proofs/scripts/docker-build.sh
Proofs.CircumferenceViaDifferentiationOQ03` (expected to pass with
3 sorries, 0 axioms).

S2 PR target: ~150 added lines (the new Lean file + minimal gallery
boilerplate + JSON updates).

### S6+ Stretch Notes

After S5 closes the general-$E$ identity, two natural follow-ups:

- **S6a**: special-case witness for $E = \mathbb{R}^2$ (the parent
  CircumferenceViaDifferentiation case) — verify that the new R1
  identity recovers the parent's `deriv_area` exactly.
- **S6b**: special-case witness for $E = \mathbb{R}^3$ — verify that
  the new R1 identity matches the parent OQ-01's $n = 3$ specialization
  `circumference_three_dim`.

These are each ~80 lines and provide cross-checks between R1 and the
parent verified results.

### S∞ Mathlib-Roadmap Notes

The manifold version (R2) is gated by four independent Mathlib
contributions:

1. **`injectivityRadius`** (~500 lines): supremum of $r$ such that
   $\exp_p$ is a diffeomorphism on $B_{T_pM}(0, r)$. Standard
   classical definition; depends on `expMap`.
2. **`expMap`** (~1000 lines): geodesic flow on Mathlib's
   `IsRiemannianManifold`. Depends on the geodesic ODE existence
   theorem (Picard-Lindelöf for the second-order Riemannian
   connection ODE), which in turn depends on the curvature tensor /
   Christoffel symbols of the Riemannian metric.
3. **Coarea formula in $\mathbb{R}^n$** (~1500 lines): Federer's
   classical proof via the area formula + density-point arguments.
4. **Riemannian volume measure** (~800 lines): partition-of-unity
   construction of the volume measure $\sqrt{\det g} \, dx^1 \cdots
   dx^n$ in local coordinates.

Sequence: 4 → 3 → 2 → 1. Total ~3800 lines. Each is an independent
Mathlib PR roadmap; OQ-03 is the application that *follows* once
all four are in.

A leaner alternative: just (3) the $\mathbb{R}^n$ coarea formula
suffices for R3, which would give an alternative proof of the
parent's flat-space identity but still does not yield the manifold
generalization.

## Summary of Deliverables (S1)

This S1 produces:

- `research/problems/circumference-via-differentiation-oq-03/problem.md`
  — formal target, Q1/Q2/Q3 sub-questions, three routes (R1
  recommended), Mathlib infrastructure map, numerical sanity for
  Euclidean dims 1-6 and constant-curvature spaces $S^2$ /
  $\mathbb{H}^2$, anti-targets, references. ~400 lines.
- `research/problems/circumference-via-differentiation-oq-03/knowledge.md`
  (this file) — S1 session summary, mathematical background (co-area
  + geodesic-polar), Mathlib API surface (available + missing),
  Lean skeleton for S2, parallel-work check, risk register, next
  action. ~350 lines.
- `research/problems/circumference-via-differentiation-oq-03/state.md`
  — OBSERVE phase, 5-stage R1 plan, S2 next-action, iteration log.
  ~120 lines.
- `src/data/research/problems/circumference-via-differentiation-oq-03.json`
  — research index entry. ~120 lines.

Net delta: ~990 lines of doc markdown / JSON, 0 Lean lines, 0
sorries, 0 axioms.
