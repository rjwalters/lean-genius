/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): the spherical model as a `MetricSpace`

This companion file to `Proofs.FeuerbachsTheoremOQ04` carries out the top item on the OQ-04
frontier list: **bundling `(Sⁿ, sdist)` as an actual Mathlib `MetricSpace` instance**.

## Why this matters for Feuerbach

The merged file already proves the four metric-space axioms for `sdist` on model points
(`sdist_isMetric`: it vanishes on the diagonal, separates points, is symmetric, and satisfies
the spherical triangle inequality).  What was still missing was the *packaging*: carving the
sphere out as a subtype and feeding those four facts to `MetricSpace.mk` so that the spherical
model becomes a genuine metric space in the sense Mathlib's whole metric library understands.
Once that is done, everything Mathlib knows about metric spaces — balls, closures,
completeness questions, `Metric.diam`, isometries — is available for the spherical Feuerbach
configuration for free.

## The construction

`SpherePoint E` is the subtype `{P : E // OnSphere P}` of unit vectors.  Its distance is
`sdist` of the underlying vectors; the four `MetricSpace` obligations are exactly the four
conjuncts of `sdist_isMetric` (with `eq_of_dist_eq_zero` needing one `Subtype.ext` to lift
`P.1 = Q.1` back to `P = Q`).  The auxiliary `edist`/uniformity/bornology fields take Mathlib's
standard defaults, so the metric topology is the honest one induced by `sdist`.

Everything is built on the *merged* metric API of `Proofs.FeuerbachsTheoremOQ04`
(`OnSphere`, `sdist`, `sdist_self`, `sdist_comm`, `sdist_triangle`, `sdist_eq_zero_iff`,
`sdist_le_pi`, `sdist_eq_angle`); this file adds no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `SpherePoint` — the sphere subtype `{P : E // OnSphere P}`.
* `SpherePoint.instMetricSpace` — the bundled `MetricSpace (SpherePoint E)` instance, with
  `dist P Q = sdist P.1 Q.1`.
* `SpherePoint.dist_def` — the defining unfold `dist P Q = sdist P.1 Q.1`.
* `SpherePoint.dist_le_pi` — every spherical distance is at most `π`: the model has diameter
  `≤ π`, the metric shadow of "antipodal points are the farthest apart".
* `SpherePoint.dist_eq_angle` — the spherical metric *is* Mathlib's unoriented vector angle
  `InnerProductGeometry.angle` on the underlying unit vectors, tying the bundled instance back
  to Mathlib's developed angle theory.
* `SpherePoint.nonneg`, `SpherePoint.dist_comm'` — the `dist` restatements of `sdist_nonneg`
  and `sdist_comm`, convenient once one is working inside the metric-space instance.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The spherical model as a subtype.**  `SpherePoint E` is the type of unit vectors of `E`
— the model points of the spherical geometry.  Bundling the sphere as a subtype is exactly
what turns the four metric axioms of `sdist_isMetric` into a `MetricSpace` instance. -/
def SpherePoint (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type _ :=
  {P : E // OnSphere P}

namespace SpherePoint

/-- **The spherical model is a genuine metric space.**  With distance `sdist` between the
underlying unit vectors, `SpherePoint E` satisfies all four `MetricSpace` obligations,
supplied verbatim by the merged spherical-metric API: `sdist_self` (vanishing on the
diagonal), `sdist_comm` (symmetry), `sdist_triangle` (the spherical triangle inequality) and
`sdist_eq_zero_iff` (point separation, lifted through `Subtype.ext`).  The `edist`/uniformity/
bornology data take Mathlib's standard `dist`-induced defaults, so this is the honest spherical
topology. -/
noncomputable instance instMetricSpace : MetricSpace (SpherePoint E) where
  dist P Q := sdist P.1 Q.1
  dist_self P := sdist_self P.1 P.2
  dist_comm P Q := sdist_comm P.1 Q.1
  dist_triangle P Q R := sdist_triangle P.2 Q.2 R.2
  eq_of_dist_eq_zero {P Q} h := Subtype.ext ((sdist_eq_zero_iff P.2 Q.2).mp h)

/-- **The spherical metric unfolds to `sdist`.**  By definition of the instance the distance
between two model points is the spherical distance of their underlying unit vectors. -/
@[simp] theorem dist_def (P Q : SpherePoint E) : dist P Q = sdist P.1 Q.1 := rfl

/-- **Spherical distances are nonnegative** (the `dist` restatement of `sdist_nonneg`). -/
theorem nonneg (P Q : SpherePoint E) : 0 ≤ dist P Q := sdist_nonneg P.1 Q.1

/-- **The spherical metric is symmetric** (the `dist` restatement of `sdist_comm`; also a
consequence of `MetricSpace.dist_comm`, recorded here in `sdist` terms). -/
theorem dist_comm' (P Q : SpherePoint E) : dist P Q = dist Q P := sdist_comm P.1 Q.1

/-- **The spherical model has diameter at most `π`.**  Every spherical distance is `≤ π`
(`sdist_le_pi`): antipodal points, at distance exactly `π`, are the farthest apart.  This is
the metric-space shadow of the fact that a spherical circle of angular radius `π` is a single
point (the antipode of its centre). -/
theorem dist_le_pi (P Q : SpherePoint E) : dist P Q ≤ Real.pi := sdist_le_pi P.1 Q.1

/-- **The spherical metric is Mathlib's unoriented vector angle.**  On the underlying unit
vectors, `dist P Q = InnerProductGeometry.angle P.1 Q.1`.  This identifies the bundled
spherical `MetricSpace` with the arccos-of-inner-product angle, so Mathlib's angle theory
transfers directly to the spherical model — the same bridge (`sdist_eq_angle`) that supplied
the triangle inequality now connects the *whole* metric to Mathlib's `InnerProductGeometry`. -/
theorem dist_eq_angle (P Q : SpherePoint E) :
    dist P Q = InnerProductGeometry.angle P.1 Q.1 :=
  sdist_eq_angle P.2 Q.2

end SpherePoint

end FeuerbachsTheoremOQ04
