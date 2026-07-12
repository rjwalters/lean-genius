/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): the spherical model has diameter π

Companion to `Proofs.FeuerbachsTheoremOQ04Metric`, which packaged the spherical model
`SphereModel E` (unit vectors of `E`) as a bundled `MetricSpace` with `dist = sdist` and
recorded the pointwise bound `dist P Q ≤ π` (`SphereModel.dist_le_pi`).

That bound is *sharp*: `dist P (−P) = π` for the antipode of any model point
(`FeuerbachsTheoremOQ04.sdist_antipode`).  This file promotes the pointwise bound into the
two metric-space statements it was aiming at, now expressed through Mathlib's `Bornology` /
`Metric.diam` API on the bundled instance:

* `SphereModel.antipode` — the antipodal involution `P ↦ −P` as a self-map of the model.
* `SphereModel.dist_antipode` — `dist P (antipode P) = π`: the antipode realises the bound.
* `SphereModel.isBounded_univ` — the whole spherical model is metrically bounded
  (`Bornology.IsBounded Set.univ`), so it plugs into Mathlib's boundedness API.
* `SphereModel.diam_le_pi` — `Metric.diam Set.univ ≤ π`.
* `SphereModel.diam_univ_eq_pi` — for a nonempty model the diameter is *exactly* `π`
  (the upper bound is attained at any antipodal pair), so the spherical model is a
  bounded metric space of diameter `π`.

Everything is `0`-axiom / `0`-sorry (`propext`/`Classical.choice`/`Quot.sound` only) on top
of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04Metric

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace SphereModel

/-- The **antipodal involution** of the spherical model: `P ↦ −P`, again a model point
(`onSphere_neg`).  A point and its antipode are the diametrically opposite pair. -/
def antipode (P : SphereModel E) : SphereModel E := ⟨-P.1, onSphere_neg P.2⟩

/-- **The antipode realises the diameter bound.**  `dist P (antipode P) = π`: a model point
and its antipode sit at the maximal spherical distance, so the bound `dist ≤ π`
(`dist_le_pi`) is attained.  Directly `sdist_antipode`. -/
@[simp] theorem dist_antipode (P : SphereModel E) : dist P (antipode P) = Real.pi := by
  rw [dist_eq]; exact sdist_antipode P.2

/-- **The spherical model is bounded.**  Every distance is at most `π`, so `Set.univ` is a
`Bornology.IsBounded` set — the spherical model is a bounded metric space, usable with
Mathlib's entire boundedness API. -/
theorem isBounded_univ : Bornology.IsBounded (Set.univ : Set (SphereModel E)) :=
  Metric.isBounded_iff.mpr ⟨Real.pi, fun x _ y _ => dist_le_pi x y⟩

/-- **Diameter upper bound.**  `Metric.diam Set.univ ≤ π` for the spherical model. -/
theorem diam_le_pi : Metric.diam (Set.univ : Set (SphereModel E)) ≤ Real.pi :=
  Metric.diam_le_of_forall_dist_le Real.pi_nonneg (fun x _ y _ => dist_le_pi x y)

/-- **The spherical model has diameter exactly `π`.**  For a nonempty model the upper bound
`Metric.diam ≤ π` is attained — any point and its antipode are `π` apart — so the diameter of
the whole spherical model equals `π`.  This is the metric-space form of the sharpness of
`dist_le_pi`: the spherical model is a bounded metric space of diameter `π`, with the maximum
realised at antipodal pairs. -/
theorem diam_univ_eq_pi [Nonempty (SphereModel E)] :
    Metric.diam (Set.univ : Set (SphereModel E)) = Real.pi := by
  refine le_antisymm diam_le_pi ?_
  obtain ⟨P⟩ := (inferInstance : Nonempty (SphereModel E))
  calc Real.pi = dist P (antipode P) := (dist_antipode P).symm
    _ ≤ Metric.diam (Set.univ : Set (SphereModel E)) :=
        Metric.dist_le_diam_of_mem isBounded_univ (Set.mem_univ P) (Set.mem_univ _)

end SphereModel

end FeuerbachsTheoremOQ04
