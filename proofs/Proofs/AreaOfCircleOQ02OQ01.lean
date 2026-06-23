/-
nball_volume_scaling: Proving the Scaling Law for n-Ball Volumes

Parent: area-of-circle-oq-02 (N-Dimensional Ball Volume Formula)
Problem: area-of-circle-oq-02-oq-01

The parent file (AreaOfCircleOQ02.lean) uses an axiom:

  axiom nball_volume_scaling (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      ENNReal.ofReal (r ^ n * unitBallVolume n)

This file PROVES the scaling law for n ≥ 1 using EuclideanSpace.volume_ball from Mathlib.

## The Key Tool (from Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls)

  EuclideanSpace.volume_ball (x : EuclideanSpace ℝ ι) (r : ℝ) [Nonempty ι] :
      volume (ball x r) = (ofReal r) ^ card ι * ofReal (√π ^ card ι / Γ(card ι / 2 + 1))

## The Bridge Lemma

Both formulas compute the unit ball volume, but in different forms:
  Mathlib form:        √π ^ n / Γ(n/2 + 1)
  unitBallVolume n:    π ^ (n/2) / Γ(n/2 + 1)

These are equal: (√π)^n = π^(n/2), since √π = π^(1/2).

## Edge Case Analysis: n = 0

The axiom as stated in the parent has a bug at n = 0, r = 0:
  - LHS: volume(ball 0 0) = volume(∅) = 0     [empty ball]
  - RHS: ofReal(0^0 * unitBallVolume 0) = ofReal(1 · 1) = 1   [since 0^0 = 1 in ℝ]

This contradiction (0 = 1) shows the axiom is FALSE at n = 0, r = 0.

The correct statement requires n ≥ 1 OR 0 < r as an additional hypothesis.
For n ≥ 1, the formula holds for all r ≥ 0 (when r = 0, r^n = 0 fixes the issue).

References:
  - Parent: Proofs.AreaOfCircleOQ02
  - Mathlib: Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-/

import Proofs.AreaOfCircleOQ02

open MeasureTheory Metric Real MeasureTheory.Measure ENNReal

namespace AreaOfCircleOQ02OQ01

open NBallVolume

-- ═══════════════════════════════════════════════════════════════
-- PART I: KEY LEMMA — (√π)^n = π^(n/2)
-- ═══════════════════════════════════════════════════════════════

/-- The n-th power of √π equals π^(n/2).

    Proof: √π = π^(1/2) by `sqrt_eq_rpow`, then use:
    - `← rpow_natCast`: convert Nat.pow to rpow
    - `← rpow_mul`: (π^a)^b = π^(a·b)
    - `ring`: 1/2 · n = n/2 -/
lemma sqrt_pi_pow_eq (n : ℕ) : (Real.sqrt π) ^ n = π ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) n,
      ← Real.rpow_mul pi_nonneg.le]
  congr 1
  ring

-- ═══════════════════════════════════════════════════════════════
-- PART II: THE SCALING THEOREM FOR n ≥ 1
-- ═══════════════════════════════════════════════════════════════

/-- **Scaling law for n-ball volumes** (n ≥ 1, r ≥ 0):
    Vol(Bⁿ(r)) = rⁿ · Vol(Bⁿ(1)) = rⁿ · π^(n/2) / Γ(n/2 + 1)

    This proves `nball_volume_scaling` from AreaOfCircleOQ02 for n ≥ 1.

    **Proof strategy:**
    1. Apply `EuclideanSpace.volume_ball` (requires `Nonempty (Fin n)`, hence n ≥ 1):
         volume(ball 0 r) = (ofReal r)^n · ofReal(√π^n / Γ(n/2+1))
    2. Convert: `(ofReal r)^n = ofReal(r^n)` via `ofReal_pow` (r ≥ 0)
    3. Merge: `ofReal(r^n) · ofReal(x) = ofReal(r^n · x)` via `ofReal_mul` (r^n ≥ 0)
    4. Bridge: `√π^n = π^(n/2)` via `sqrt_pi_pow_eq` -/
theorem nball_volume_scaling_theorem (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) =
    ENNReal.ofReal (r ^ n * unitBallVolume n) := by
  -- EuclideanSpace.volume_ball requires [Nonempty (Fin n)]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Apply Mathlib's formula for volume of n-ball
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  -- Convert (ENNReal.ofReal r)^n → ENNReal.ofReal (r^n)
  rw [← ENNReal.ofReal_pow hr]
  -- Merge: ENNReal.ofReal (r^n) * ENNReal.ofReal x → ENNReal.ofReal (r^n * x)
  rw [← ENNReal.ofReal_mul (pow_nonneg hr n)]
  -- Reduce to real arithmetic
  congr 1
  -- Goal: r^n * (√π^n / Γ(n/2+1)) = r^n * unitBallVolume n
  unfold unitBallVolume
  -- Goal: r^n * (√π^n / Γ(n/2+1)) = r^n * (π^(n/2) / Γ(n/2+1))
  congr 1
  -- Goal: √π^n / Γ(n/2+1) = π^(n/2) / Γ(n/2+1)
  congr 1
  -- Goal: (√π)^n = π^(n/2)
  exact sqrt_pi_pow_eq n

-- ═══════════════════════════════════════════════════════════════
-- PART III: DIRECT INSTANCES — CIRCLE AND SPHERE
-- ═══════════════════════════════════════════════════════════════

/-- **2D ball (disk/circle)**: Vol(B²(r)) = π · r².
    This recovers the area-of-circle formula A = πr² with a verified scaling law. -/
theorem area_2ball_scaling (r : ℝ) (hr : 0 ≤ r) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 2)) r) =
    ENNReal.ofReal (π * r ^ 2) := by
  rw [nball_volume_scaling_theorem 2 (by norm_num) r hr, unitBallVolume_two]
  congr 1
  ring

/-- **3D ball (solid sphere)**: Vol(B³(r)) = (4π/3) · r³. -/
theorem vol_3ball_scaling (r : ℝ) (hr : 0 ≤ r) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 3)) r) =
    ENNReal.ofReal (4 * π / 3 * r ^ 3) := by
  rw [nball_volume_scaling_theorem 3 (by norm_num) r hr, unitBallVolume_three]
  congr 1
  ring

-- ═══════════════════════════════════════════════════════════════
-- PART IV: THE n = 0 EDGE CASE IS GENUINELY FALSE
-- ═══════════════════════════════════════════════════════════════

/-- The axiom `nball_volume_scaling` from the parent file is FALSE at n = 0, r = 0.

    The formula gives ofReal(0^0 · unitBallVolume 0) = ofReal(1 · 1) = 1,
    but the actual volume of the empty ball is 0.
    The bug is that 0^0 = 1 in ℝ, while ball(0, 0) = ∅ has measure 0. -/
example : ¬ (volume (ball (0 : EuclideanSpace ℝ (Fin 0)) (0 : ℝ)) =
              ENNReal.ofReal ((0 : ℝ) ^ 0 * unitBallVolume 0)) := by
  have hempty : ball (0 : EuclideanSpace ℝ (Fin 0)) (0 : ℝ) = ∅ :=
    Metric.ball_eq_empty.mpr (le_refl 0)
  rw [hempty, measure_empty, unitBallVolume_zero, pow_zero, mul_one, ENNReal.ofReal_one]
  exact zero_ne_one

/-!
## Summary

**Proved (0 sorries, 0 axioms):**
1. **sqrt_pi_pow_eq**: (√π)^n = π^(n/2) for all n : ℕ
2. **nball_volume_scaling_theorem**: For n ≥ 1 and r ≥ 0,
   `volume(Bⁿ(r)) = ENNReal.ofReal(rⁿ · unitBallVolume n)`
3. **area_2ball_scaling**: Vol(B²(r)) = πr² (circle area formula, fully verified)
4. **vol_3ball_scaling**: Vol(B³(r)) = (4π/3)r³ (sphere volume, fully verified)
5. The negative example showing the parent axiom is false at n=0, r=0

**Key achievement**: The parent file `AreaOfCircleOQ02.lean` has 1 axiom
(`nball_volume_scaling`). This file proves the axiom is:
- Provable for all n ≥ 1 (using EuclideanSpace.volume_ball from Mathlib)
- False at the degenerate case n=0, r=0 (due to 0^0 = 1 in ℝ)

The correct fix for the parent file: change the axiom hypothesis from
`(hr : 0 ≤ r)` to `(hn : 0 < n)` or add `(hn : 0 < n)`.
-/

end AreaOfCircleOQ02OQ01
