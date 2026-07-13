/-
Erdős Problem #1215 (Mac Lane 1953) — the **area** of the sublevel region of a
unit-circle-rooted polynomial.

Parent: `Proofs.Erdos1215Problem`; radius companion:
`Proofs.Erdos1215UnitCircleRadius`.

The radius companion pins the closed sublevel set
`closedLevelSet P C = {z : |P(z)| ≤ C}` of an `Erdos1215.IsUnitCirclePolynomial P`
between two concentric balls:

* outer — `closedLevelSet_subset_closedBall`: contained in `closedBall(0, 1 + C^{1/deg})`;
* inner — `closedBall_subset_closedLevelSet` (for `C ≥ 1`): contains
  `closedBall(0, C^{1/deg} − 1)`.

Both radii are geometric data about the *labyrinth region* that Mac Lane's forced
paths thread.  This file converts that radial sandwich into a **planar-area
sandwich**: monotonicity of the 2-dimensional Lebesgue measure `volume` on `ℂ`,
together with Mathlib's `Complex.volume_closedBall a r = ENNReal.ofReal r ^ 2 · π`,
turns the two ball inclusions into explicit lower/upper bounds on
`volume (closedLevelSet P C)`.  The upshot: the Mac Lane sublevel region of *any*
unit-circle polynomial of degree `d` has area

  `π · (C^{1/d} − 1)²  ≤  area  ≤  π · (C^{1/d} + 1)²`   (for `C ≥ 1`),

a bound that depends only on `C` and `d`, not on the individual roots.  In
particular the region has **finite** area (equivalently: it is bounded/compact).

Main results:
* `volume_closedLevelSet_le`      : outer area bound `area ≤ π·(1 + C^{1/deg})²`.
* `le_volume_closedLevelSet`      : inner area bound `π·(C^{1/deg} − 1)² ≤ area` (`C ≥ 1`).
* `volume_closedLevelSet_lt_top`  : the sublevel region has finite area
                                    (reusing `isCompact_closedLevelSet`).
* `volume_closedLevelSet_ne_top`  : `≠ ⊤` restatement of finiteness.
* `toReal_volume_closedLevelSet_le` / `le_toReal_volume_closedLevelSet` : the same
                                    sandwich for the honest real-valued area `area.toReal`.

All results are `0`-axiom / `0`-sorry.  (The parent `maclane_labyrinth` — the deep
Mac Lane phenomenon of paths forced through neighbourhoods of `0` — remains
axiomatized; this file supplies unconditional area confinement, not that.)
-/

import Mathlib
import Proofs.Erdos1215UnitCircleRadius

open Complex Polynomial MeasureTheory

namespace Erdos1215UnitCircleArea

open Erdos1215UnitCircleRadius

variable {P : ℂ[X]}

/-- **Outer area bound.** The closed sublevel region of a positive-degree unit-circle
polynomial has 2-dimensional Lebesgue measure at most `π · (1 + C^{1/deg})²`
(the area of the outer confining ball). -/
theorem volume_closedLevelSet_le (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    volume (closedLevelSet P C)
      ≤ ENNReal.ofReal (1 + C ^ ((P.natDegree : ℝ)⁻¹)) ^ 2 * NNReal.pi := by
  calc volume (closedLevelSet P C)
      ≤ volume (Metric.closedBall (0 : ℂ) (1 + C ^ ((P.natDegree : ℝ)⁻¹))) :=
        measure_mono (closedLevelSet_subset_closedBall h hdeg C hC)
    _ = ENNReal.ofReal (1 + C ^ ((P.natDegree : ℝ)⁻¹)) ^ 2 * NNReal.pi :=
        Complex.volume_closedBall _ _

/-- **Inner area bound.** For `C ≥ 1`, the closed sublevel region of a positive-degree
unit-circle polynomial has 2-dimensional Lebesgue measure at least
`π · (C^{1/deg} − 1)²` (the area of the inner ball it contains). -/
theorem le_volume_closedLevelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 1 ≤ C) :
    ENNReal.ofReal (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ^ 2 * NNReal.pi
      ≤ volume (closedLevelSet P C) := by
  calc ENNReal.ofReal (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ^ 2 * NNReal.pi
      = volume (Metric.closedBall (0 : ℂ) (C ^ ((P.natDegree : ℝ)⁻¹) - 1)) :=
        (Complex.volume_closedBall _ _).symm
    _ ≤ volume (closedLevelSet P C) :=
        measure_mono (closedBall_subset_closedLevelSet h hdeg C hC)

/-- **The sublevel region has finite area.** Directly from compactness
(`isCompact_closedLevelSet`) via `IsCompact.measure_lt_top`, since `volume` on `ℂ` is
finite on compact sets. -/
theorem volume_closedLevelSet_lt_top (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    volume (closedLevelSet P C) < ⊤ :=
  (isCompact_closedLevelSet h hdeg C hC).measure_lt_top

/-- `≠ ⊤` restatement of `volume_closedLevelSet_lt_top`. -/
theorem volume_closedLevelSet_ne_top (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    volume (closedLevelSet P C) ≠ ⊤ :=
  (volume_closedLevelSet_lt_top h hdeg C hC).ne

/-- **Outer area bound, real-valued.** The honest real-number area
`(volume (closedLevelSet P C)).toReal` is at most `π · (1 + C^{1/deg})²`. -/
theorem toReal_volume_closedLevelSet_le (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 0 ≤ C) :
    (volume (closedLevelSet P C)).toReal
      ≤ Real.pi * (1 + C ^ ((P.natDegree : ℝ)⁻¹)) ^ 2 := by
  have hRnn : (0 : ℝ) ≤ 1 + C ^ ((P.natDegree : ℝ)⁻¹) := by positivity
  have hle := volume_closedLevelSet_le h hdeg C hC
  have hballtop : (ENNReal.ofReal (1 + C ^ ((P.natDegree : ℝ)⁻¹)) ^ 2 * NNReal.pi)
      ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.coe_ne_top
  have hmono := ENNReal.toReal_le_toReal (volume_closedLevelSet_ne_top h hdeg C hC) hballtop
  have hval : (ENNReal.ofReal (1 + C ^ ((P.natDegree : ℝ)⁻¹)) ^ 2 * NNReal.pi).toReal
      = Real.pi * (1 + C ^ ((P.natDegree : ℝ)⁻¹)) ^ 2 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hRnn,
      ENNReal.coe_toReal, NNReal.coe_real_pi, mul_comm]
  rw [← hval]
  exact hmono.mpr hle

/-- **Inner area bound, real-valued.** For `C ≥ 1`, the real-number area
`(volume (closedLevelSet P C)).toReal` is at least `π · (C^{1/deg} − 1)²`. -/
theorem le_toReal_volume_closedLevelSet (h : Erdos1215.IsUnitCirclePolynomial P)
    (hdeg : 0 < P.natDegree) (C : ℝ) (hC : 1 ≤ C) :
    Real.pi * (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ^ 2
      ≤ (volume (closedLevelSet P C)).toReal := by
  have hRnn : (0 : ℝ) ≤ C ^ ((P.natDegree : ℝ)⁻¹) - 1 := by
    have : (1 : ℝ) ≤ C ^ ((P.natDegree : ℝ)⁻¹) := by
      have hkpos : (0 : ℝ) ≤ (P.natDegree : ℝ)⁻¹ := by positivity
      simpa using Real.one_le_rpow (by linarith) hkpos
    linarith
  have hle := le_volume_closedLevelSet h hdeg C hC
  have hballtop : (ENNReal.ofReal (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ^ 2 * NNReal.pi)
      ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.coe_ne_top
  have hmono := ENNReal.toReal_le_toReal hballtop
    (volume_closedLevelSet_ne_top h hdeg C (le_trans zero_le_one hC))
  have hval : (ENNReal.ofReal (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ^ 2 * NNReal.pi).toReal
      = Real.pi * (C ^ ((P.natDegree : ℝ)⁻¹) - 1) ^ 2 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hRnn,
      ENNReal.coe_toReal, NNReal.coe_real_pi, mul_comm]
  rw [← hval]
  exact hmono.mpr hle

end Erdos1215UnitCircleArea
