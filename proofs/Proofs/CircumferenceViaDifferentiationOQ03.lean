/-
  OQ-03: Riemannian dV/dr = A — vector-space partial answer (n = 2, 3)
  (circumference-via-differentiation-oq-03)

  Open Question 3 asks whether the identity dV/dr = A (volume's derivative
  equals surface area) generalizes from Euclidean space to Riemannian
  manifolds via the co-area formula. The literal Riemannian-manifold
  version is gated by four Mathlib gaps (no `injectivityRadius`, `expMap`,
  geodesicBall/Sphere/Volume family, no n-dim coarea); see `research/
  problems/circumference-via-differentiation-oq-03/problem.md`.

  This file delivers the **R1 vector-space partial answer** at concrete
  Euclidean dimensions n = 2 and n = 3, recovering the parent theorem
  (n = 2: circle circumference) and the n = 3 case (surface area of the
  2-sphere) from Mathlib's `EuclideanSpace` ball-volume primitives.

  The four theorems:
    * `riemannianVolumeBall_fin_two`  — bridge: `vol (closedBall p r) = π r²`
    * `riemannianVolumeBall_fin_three` — bridge: `vol (closedBall p r) = (4π/3) r³`
    * `riemannianVolumeBall_hasDerivWithinAt_fin_two` — main: dV/dr = 2π r
    * `riemannianVolumeBall_hasDerivWithinAt_fin_three` — main: dV/dr = 4π r²

  Status: 0 sorries, 0 axioms.

  Limitations (per `state.md` §Calibration): R1 vector-space restriction
  only; arbitrary `n` and abstract `InnerProductSpace` polymorphism are
  out of scope, as is the full Riemannian-manifold target (R2). See
  parent OQ-01 (`Proofs/CircumferenceViaDifferentiationOQ01.lean`) for
  the polynomial general-n form on the n-ball volume polynomial side.

  Mathlib bearers (pinned rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67):
    * `EuclideanSpace.volume_closedBall_fin_two`  — VolumeOfBalls.lean
    * `EuclideanSpace.volume_closedBall_fin_three` — VolumeOfBalls.lean
    * `HasDerivWithinAt.congr` — Deriv/Basic.lean (f₁ x = f x orientation)
    * `hasDerivAt_pow` — Deriv/Pow.lean
    * `ENNReal.toReal_mul`, `ENNReal.toReal_pow`, `ENNReal.toReal_ofReal`
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

open Real MeasureTheory ENNReal Metric

namespace CircumferenceViaDifferentiationOQ03

/-- Bridge 1, n = 2: closed-ball area in the Euclidean plane is `π r²`. -/
theorem riemannianVolumeBall_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = π * r ^ 2 := by
  rw [EuclideanSpace.volume_closedBall_fin_two p r,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal pi_nonneg]
  ring

/-- Bridge 1, n = 3: closed-ball volume in Euclidean 3-space is `(4π/3) r³`. -/
theorem riemannianVolumeBall_fin_three
    (p : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal = (4 * π / 3) * r ^ 3 := by
  rw [EuclideanSpace.volume_closedBall_fin_three p r,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π * 4 / 3)]
  ring

/-- Main S5, n = 2: dV/dr = 2π r, the circumference of the circle of radius r. -/
theorem riemannianVolumeBall_hasDerivWithinAt_fin_two
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (2 * π * r) (Set.Ici 0) r := by
  have h_poly : HasDerivAt (fun s : ℝ => π * s ^ 2) (2 * π * r) r := by
    have h := (hasDerivAt_pow 2 r).const_mul π
    convert h using 1
    ring
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact riemannianVolumeBall_fin_two p s hs
  · exact riemannianVolumeBall_fin_two p r hr

/-- Main S5, n = 3: dV/dr = 4π r², the surface area of the 2-sphere of radius r. -/
theorem riemannianVolumeBall_hasDerivWithinAt_fin_three
    (p : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (4 * π * r ^ 2) (Set.Ici 0) r := by
  have h_poly : HasDerivAt (fun s : ℝ => (4 * π / 3) * s ^ 3) (4 * π * r ^ 2) r := by
    have h := (hasDerivAt_pow 3 r).const_mul (4 * π / 3)
    convert h using 1
    ring
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact riemannianVolumeBall_fin_three p s hs
  · exact riemannianVolumeBall_fin_three p r hr

end CircumferenceViaDifferentiationOQ03
