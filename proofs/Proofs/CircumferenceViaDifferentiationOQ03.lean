/-
  OQ-03: Riemannian dV/dr = A — vector-space partial answer (n = 2, 3)
  plus abstract polymorphic Bridge 1 (Workaround A)
  (circumference-via-differentiation-oq-03)

  Open Question 3 asks whether the identity dV/dr = A (volume's derivative
  equals surface area) generalizes from Euclidean space to Riemannian
  manifolds via the co-area formula. The literal Riemannian-manifold
  version is gated by four Mathlib gaps (no `injectivityRadius`, `expMap`,
  geodesicBall/Sphere/Volume family, no n-dim coarea); see `research/
  problems/circumference-via-differentiation-oq-03/problem.md`.

  This file delivers:

  (R1.a) the **R1 vector-space partial answer** at concrete Euclidean
  dimensions n = 2 and n = 3, recovering the parent theorem (n = 2:
  circle circumference) and the n = 3 case (surface area of the 2-sphere)
  from Mathlib's `EuclideanSpace` ball-volume primitives; and

  (R1.b) the **polymorphic Bridge 1** (S3 ACT, Workaround A) over an
  abstract `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]` with the
  canonical `MeasureSpace E`, identifying `vol(closedBall p r).toReal`
  with the OQ-01 polynomial `nBallVolumeFn (finrank ℝ E) r`.

  The theorems:
    * `riemannianVolumeBall_fin_two`  — bridge: `vol (closedBall p r) = π r²`
    * `riemannianVolumeBall_fin_three` — bridge: `vol (closedBall p r) = (4π/3) r³`
    * `riemannianVolumeBall_hasDerivWithinAt_fin_two` — main: dV/dr = 2π r
    * `riemannianVolumeBall_hasDerivWithinAt_fin_three` — main: dV/dr = 4π r²
    * `riemannianVolumeBall_eq_nBallVolumeFn` — Bridge 1 (polymorphic)

  Status: 0 sorries, 0 axioms.

  Limitations (per `state.md` §Calibration): R1 vector-space restriction
  only; full Riemannian-manifold target (R2) and standalone n-dim
  coarea (R3) remain Mathlib-roadmap gaps. The S3 ACT polymorphic Bridge 1
  takes the polymorphic step over abstract `[InnerProductSpace ℝ E]`,
  recovering the OQ-01 polynomial `nBallVolumeFn` as the volume formula.

  Mathlib bearers (pinned rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67):
    * `EuclideanSpace.volume_closedBall_fin_two`  — VolumeOfBalls.lean
    * `EuclideanSpace.volume_closedBall_fin_three` — VolumeOfBalls.lean
    * `InnerProductSpace.volume_closedBall` — VolumeOfBalls.lean:372
      (re-verified at pinned SHA on 2026-05-31; no drift from S3 PREP)
    * `HasDerivWithinAt.congr` — Deriv/Basic.lean (f₁ x = f x orientation)
    * `hasDerivAt_pow` — Deriv/Pow.lean
    * `ENNReal.toReal_mul`, `ENNReal.toReal_pow`, `ENNReal.toReal_ofReal`
    * `Real.sqrt_eq_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Proofs.CircumferenceViaDifferentiationOQ01

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

/-- **Bridge 1 (abstract polymorphic, Workaround A)**: in any
finite-dimensional real inner-product space `E` (with the canonical
`MeasureSpace` / `BorelSpace` instances), the closed-ball volume agrees
with the parent OQ-01 polynomial `nBallVolumeFn` at the dimension
`finrank ℝ E`.

Combined with `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt`,
this proves the polymorphic main identity `dV/dr = A` at every
`finrank ℝ E ≥ 1` (S4 ACT target).

The `[Nontrivial E]` hypothesis (equivalent to `0 < finrank ℝ E`) is the
natural typing: at `finrank = 0` the manifold is a point and both
`V ≡ 0` and `A ≡ 0`.

See `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-14-s3-prep-workaround-a-bridge1-mathlib-availability-erratum.md`
§3 for the proof-chain derivation. -/
theorem riemannianVolumeBall_eq_nBallVolumeFn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]
    (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  rw [InnerProductSpace.volume_closedBall p r, ENNReal.toReal_mul]
  rw [show ((ENNReal.ofReal r) ^ Module.finrank ℝ E).toReal =
        r ^ Module.finrank ℝ E from ?_]
  swap
  · rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  have h_quot_nn : 0 ≤
      Real.sqrt π ^ Module.finrank ℝ E /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
    apply div_nonneg
    · exact pow_nonneg (Real.sqrt_nonneg π) _
    · exact (Real.Gamma_pos_of_pos (by positivity)).le
  rw [ENNReal.toReal_ofReal h_quot_nn]
  set n := Module.finrank ℝ E with hn_def
  unfold CircumferenceViaDifferentiationOQ01.nBallVolumeFn
         CircumferenceViaDifferentiationOQ01.unitBallVolume
  have h_sqrt_pow : Real.sqrt π ^ n = π ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow,
        ← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) n,
        ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  rw [h_sqrt_pow]
  ring

end CircumferenceViaDifferentiationOQ03
