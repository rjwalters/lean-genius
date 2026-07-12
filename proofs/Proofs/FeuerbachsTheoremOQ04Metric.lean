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

Immediate consequences are recorded: the distance formula `dist P Q =
arccos ⟪P, Q⟫` (definitional, `rfl`) and the diameter bound `dist P Q ≤ π` (the
spherical model has diameter `π`, attained at antipodal points).

The bundled instance is then used to lift the raw-vector antipodal identities of
`FeuerbachsTheoremOQ04` to a genuine self-map `antipode : SphereModel E → SphereModel E`
(`P ↦ -P`, well-defined by `onSphere_neg`): it is an involution (`antipode_antipode`),
realises the diameter (`dist_antipode : dist P (antipode P) = π`), is the *unique* point at
distance `π` (`dist_eq_pi_iff`, the far-end dual of `eq_of_dist_eq_zero`), is an isometry
of the model (`dist_antipode_antipode`), and reflects distances to their supplement
(`dist_antipode_right : dist P (antipode Q) = π − dist P Q`).

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

/-! ### The antipodal map as a bundled self-map of the metric space

`FeuerbachsTheoremOQ04` proves the antipodal identities at the level of raw unit vectors
(`onSphere_neg`, `sdist_antipode`, `sdist_eq_pi_iff`, `sdist_neg_neg`, `sdist_neg_right`).
Since `SphereModel E` is closed under `x ↦ -x` (`onSphere_neg`), these package into a
genuine self-map `antipode : SphereModel E → SphereModel E` and its metric properties
inside the bundled `MetricSpace`. -/

/-- The **antipodal map** on the spherical model, `P ↦ -P`.  Well-defined because the
sphere is closed under negation (`onSphere_neg`). -/
def antipode (P : SphereModel E) : SphereModel E := ⟨-(P : E), onSphere_neg P.2⟩

@[simp] theorem antipode_coe (P : SphereModel E) : (antipode P : E) = -(P : E) := rfl

/-- **The antipodal map is an involution:** `antipode (antipode P) = P`, from `- -P = P`. -/
@[simp] theorem antipode_antipode (P : SphereModel E) : antipode (antipode P) = P :=
  Subtype.ext (neg_neg (P : E))

/-- **A point is at distance `π` from its own antipode:** `dist P (antipode P) = π`.  The
antipode realises the diameter `π` of `dist_le_pi`.  Bundled form of `sdist_antipode`. -/
theorem dist_antipode (P : SphereModel E) : dist P (antipode P) = Real.pi := by
  rw [dist_eq]; exact sdist_antipode P.2

/-- **The antipode is the unique point at distance `π`:** `dist P Q = π ↔ Q = antipode P`.
Bundled form of `sdist_eq_pi_iff`; the metric-space counterpart of the near-end
separation `dist P Q = 0 ↔ P = Q` (`eq_of_dist_eq_zero`). -/
theorem dist_eq_pi_iff (P Q : SphereModel E) : dist P Q = Real.pi ↔ Q = antipode P := by
  rw [dist_eq, sdist_eq_pi_iff P.2 Q.2]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; subst h; rfl

/-- **The antipodal map is an isometry of the spherical model:**
`dist (antipode P) (antipode Q) = dist P Q`.  Bundled form of `sdist_neg_neg` — the central
symmetry `x ↦ -x` preserves spherical distance. -/
@[simp] theorem dist_antipode_antipode (P Q : SphereModel E) :
    dist (antipode P) (antipode Q) = dist P Q := by
  rw [dist_eq, dist_eq]; exact sdist_neg_neg (P : E) (Q : E)

/-- **Reflecting one point through the centre sends the distance to its supplement:**
`dist P (antipode Q) = π − dist P Q`.  Bundled form of `sdist_neg_right`; with `Q = P` it
recovers `dist_antipode`. -/
theorem dist_antipode_right (P Q : SphereModel E) :
    dist P (antipode Q) = Real.pi - dist P Q := by
  rw [dist_eq, dist_eq]; exact sdist_neg_right (P : E) (Q : E)

end SphereModel

end FeuerbachsTheoremOQ04
