import Proofs.FeuerbachsTheoremOQ04

/-
# The spherical model as a bundled `MetricSpace`  (Feuerbach OQ-04, continued)

`FeuerbachsTheoremOQ04.lean` proves `sdist_isMetric`: the spherical distance
`sdist P Q = arccos ⟪P, Q⟫` satisfies all four metric-space axioms on model points
(unit vectors).  Its docstring notes that "packaging this as a bundled `MetricSpace`
instance would only additionally require carving the sphere out as a subtype".

This file does exactly that.  It defines the spherical model `SphereModel E` as the
subtype of unit vectors and registers a genuine `MetricSpace (SphereModel E)`
instance whose `dist` is `sdist`, drawing each field from the corresponding lemma of
`FeuerbachsTheoremOQ04` (`sdist_self`, `sdist_comm`, `sdist_triangle`,
`sdist_eq_zero_iff`).  This turns the four-axiom conjunction into an actual typeclass
instance, so the spherical model can be used with Mathlib's entire metric-space API
(balls, `Metric.sphere`, continuity, `Bornology`, uniformity, …) rather than only the
bare `sdist` lemmas.

Two immediate consequences are recorded: the distance formula `dist P Q =
arccos ⟪P, Q⟫` (definitional, `rfl`) and the diameter bound `dist P Q ≤ π` (the
spherical model has diameter `π`, attained at antipodal points).

Axiom-free (`propext`/`Classical.choice`/`Quot.sound` only): no `native_decide`, no
`sorry`, no `axiom`.
-/

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **spherical model**: the subtype of unit vectors of `E` (`OnSphere P : ‖P‖ = 1`).
This is the carrier on which `sdist` is a genuine metric. -/
def SphereModel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type _ :=
  {P : E // OnSphere P}

namespace SphereModel

instance : CoeOut (SphereModel E) E := ⟨Subtype.val⟩

/-- **The spherical model is a metric space** with `dist = sdist`.  Each axiom is
supplied by the corresponding `sdist_*` lemma of `FeuerbachsTheoremOQ04`; the
`edist`/uniformity/bornology fields take their canonical defaults derived from `dist`. -/
noncomputable instance instMetricSpace : MetricSpace (SphereModel E) where
  dist P Q := sdist P.1 Q.1
  dist_self P := sdist_self P.1 P.2
  dist_comm P Q := sdist_comm P.1 Q.1
  dist_triangle P Q R := sdist_triangle P.2 Q.2 R.2
  eq_of_dist_eq_zero {P Q} h := Subtype.ext ((sdist_eq_zero_iff P.2 Q.2).mp h)

/-- The metric-space `dist` on the spherical model is definitionally `sdist`. -/
@[simp] theorem dist_eq (P Q : SphereModel E) : dist P Q = sdist P.1 Q.1 := rfl

/-- Unfolded distance formula: `dist P Q = arccos ⟪P, Q⟫`. -/
theorem dist_eq_arccos (P Q : SphereModel E) :
    dist P Q = Real.arccos ⟪(P : E), (Q : E)⟫ := rfl

/-- **Diameter bound.**  Every spherical distance is at most `π`; the spherical model
has diameter `π` (attained at antipodal points).  Immediate from `arccos ≤ π`. -/
theorem dist_le_pi (P Q : SphereModel E) : dist P Q ≤ Real.pi := by
  rw [dist_eq_arccos]
  exact Real.arccos_le_pi _

end SphereModel

end FeuerbachsTheoremOQ04
