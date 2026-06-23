/-
  OQ-02: The n-Ball Volume Model Is the Euclidean Lebesgue Measure
  (circumference-via-differentiation-oq-02)

  The sibling entry OQ-01 proves the volume–surface duality

    d/dr (ω_n · rⁿ) = n · ω_n · r^(n-1) = S_{n-1}(r)

  for the *polynomial model* `nBallVolumeFn n r = unitBallVolume n * rⁿ`, where
  `unitBallVolume n = π^(n/2)/Γ(n/2+1)` is defined purely through the Gamma
  function. What OQ-01 leaves open for general n is whether that abstract
  constant ω_n really is the *Lebesgue measure* of a ball: OQ-01 only connects
  the n = 2 case to the parent's `areaFn` (itself built on `Complex.volume_ball`).

  This file closes that gap for ALL dimensions, answering the parent's open
  question "can the n-dimensional analog be formalized using Mathlib's geometric
  measure theory?":

    1.  `nBallVolume_eq_measure` — the polynomial model equals the genuine
        Lebesgue measure of a Euclidean n-ball:
            (volume (ball 0 r)).toReal = unitBallVolume n · rⁿ      (n ≥ 1, r ≥ 0),
        via Mathlib's `EuclideanSpace.volume_ball`. This grounds OQ-01's
        Gamma-defined ω_n as a true volume.

    2.  `measure_ball_hasDerivAt_surface` — consequently the radial derivative of
        the *actual* Lebesgue measure of the ball equals the surface area:
            d/dr [ (volume (ball 0 r)).toReal ] = S_{n-1}(r)        (n ≥ 1, r > 0).
        Here the duality is a statement about genuine geometric volume, not the
        algebraic model. (Restricted to r > 0 because for r < 0 the ball is empty
        while the polynomial ω_n rⁿ is not.)

  Reuses OQ-01's definitions (`unitBallVolume`, `nBallVolumeFn`, `nSphereSurfaceFn`).
  Status: 0 sorries, 0 axioms.
-/

import Mathlib
import Proofs.CircumferenceViaDifferentiation
import Proofs.CircumferenceViaDifferentiationOQ01

open MeasureTheory Metric Real
open CircumferenceViaDifferentiationOQ01

namespace CircumferenceViaDifferentiationOQ02

/-! ## Reconciling the two forms of the unit-ball constant

OQ-01 writes `ω_n = π^(n/2)/Γ(n/2+1)` (a real power of π), whereas Mathlib's
`EuclideanSpace.volume_ball` produces `√π ^ n / Γ(n/2+1)` (a natural power of √π).
These agree because `π^(n/2) = (√π)ⁿ`. -/

/-- `π^(n/2) = (√π)ⁿ`: the real power and the natural power of √π coincide. -/
theorem pi_rpow_half_eq_sqrt_pow (n : ℕ) : π ^ ((n : ℝ) / 2) = Real.sqrt π ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul Real.pi_nonneg]
  congr 1
  ring

/-! ## The measure bridge -/

/-- **Grounding OQ-01's volume in measure theory.** For `n ≥ 1` and `r ≥ 0`, the
polynomial model `nBallVolumeFn n r = ω_n · rⁿ` equals the genuine Lebesgue
measure of the Euclidean n-ball of radius `r`. This is the specialization of
Mathlib's `EuclideanSpace.volume_ball` that justifies calling `unitBallVolume n`
a *volume* in every dimension. -/
theorem nBallVolume_eq_measure {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal = nBallVolumeFn n r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hC : (0 : ℝ) ≤ Real.sqrt π ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by positivity
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.toReal_mul,
      ← ENNReal.ofReal_pow hr,
      ENNReal.toReal_ofReal (pow_nonneg hr n),
      ENNReal.toReal_ofReal hC]
  unfold nBallVolumeFn unitBallVolume
  rw [pi_rpow_half_eq_sqrt_pow]
  ring

/-- In particular, `unitBallVolume n` is the Lebesgue measure of the *unit* ball. -/
theorem unitBallVolume_eq_measure {n : ℕ} (hn : 1 ≤ n) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal = unitBallVolume n := by
  rw [nBallVolume_eq_measure hn 1 zero_le_one]
  unfold nBallVolumeFn
  simp

/-! ## Duality on the genuine Lebesgue measure -/

/-- **Volume–surface duality for the true measure.** For `n ≥ 1` and `r > 0`, the
radial derivative of the *actual Lebesgue measure* of the Euclidean n-ball equals
the `(n-1)`-sphere surface area `S_{n-1}(r) = n · ω_n · r^(n-1)`.

This upgrades OQ-01's model-level duality to a statement about genuine geometric
volume. The measure agrees with the polynomial model on the neighbourhood
`{ρ : 0 < ρ}` of `r`, so `HasDerivAt.congr_of_eventuallyEq` transports OQ-01's
derivative `nBallVolumeFn_hasDerivAt`. -/
theorem measure_ball_hasDerivAt_surface {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun ρ => (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ)).toReal)
      (nSphereSurfaceFn n r) r := by
  have hEq : (fun ρ => (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ)).toReal)
      =ᶠ[nhds r] nBallVolumeFn n := by
    filter_upwards [Ioi_mem_nhds hr] with ρ hρ
    exact nBallVolume_eq_measure hn ρ (le_of_lt hρ)
  exact (nBallVolumeFn_hasDerivAt n r).congr_of_eventuallyEq hEq

/-- The `deriv` form of the measure-level duality (for `r > 0`). -/
theorem deriv_measure_ball {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    deriv (fun ρ => (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ)).toReal) r
      = nSphereSurfaceFn n r :=
  (measure_ball_hasDerivAt_surface hn hr).deriv

/-! ## Concrete dimensions -/

/-- **n = 2.** The Lebesgue measure of a disk of radius `r` is `π r²`. -/
theorem measure_disk_eq (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)).toReal = π * r ^ 2 := by
  rw [nBallVolume_eq_measure (by norm_num) r hr]
  unfold nBallVolumeFn
  rw [unitBallVolume_two]

/-- **n = 2.** Differentiating the genuine disk area gives the circumference `2π r`
(for `r > 0`) — the parent theorem, now on the Lebesgue measure itself. -/
theorem deriv_measure_disk (r : ℝ) (hr : 0 < r) :
    deriv (fun ρ => (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)).toReal) r
      = 2 * π * r := by
  rw [deriv_measure_ball (by norm_num) hr]
  unfold nSphereSurfaceFn
  rw [nSphereSurfaceConst_two]
  norm_num

/-- **n = 3.** The Lebesgue measure of a ball of radius `r` is `(4π/3) r³`. -/
theorem measure_ball_three_eq (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)).toReal = 4 * π / 3 * r ^ 3 := by
  rw [nBallVolume_eq_measure (by norm_num) r hr]
  unfold nBallVolumeFn
  rw [unitBallVolume_three]

/-- **n = 3.** Differentiating the genuine ball volume gives the sphere surface
area `4π r²` (for `r > 0`) — the spatial case of the duality on the true measure. -/
theorem deriv_measure_ball_three (r : ℝ) (hr : 0 < r) :
    deriv (fun ρ => (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) ρ)).toReal) r
      = 4 * π * r ^ 2 := by
  rw [deriv_measure_ball (by norm_num) hr]
  unfold nSphereSurfaceFn
  rw [nSphereSurfaceConst_three, show (3 : ℕ) - 1 = 2 from rfl]

end CircumferenceViaDifferentiationOQ02
