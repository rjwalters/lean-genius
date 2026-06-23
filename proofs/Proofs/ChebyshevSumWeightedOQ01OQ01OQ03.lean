import Mathlib
import Proofs.ChebyshevSumWeightedOQ01OQ01

/-
# Weighted power-mean monotonicity from the weighted square bound

The parent file `ChebyshevSumWeightedOQ01OQ01` derives, from the weighted
Chebyshev sum inequality, the **weighted square bound** (a weighted
Cauchy–Schwarz / power-mean estimate)

  (∑ i ∈ s, w i * f i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i ^ 2,

valid for nonnegative weights `w` and *any* real `f`.

This file answers the open question: **derive the weighted power-mean /
Cauchy–Schwarz "chain" (weighted Lᵖ monotonicity) from that square bound.**
The square bound is exactly the `p = 1 ≤ 2` rung of the power-mean ladder;
substituting `f i = a i ^ r` and iterating climbs it.

## Contents

* `pow_sum_sq_le` — the **Cauchy–Schwarz / Lyapunov chain** for natural-exponent
  power sums `P m = ∑ wᵢ aᵢ^m`:
    `P (m + t) ^ 2 ≤ P m * P (m + 2 t)`,
  obtained by applying the square bound to weights `wᵢ aᵢ^m` and function `aᵢ^t`.
  This is the discrete log-convexity (Lyapunov) inequality for power sums.

* `pow_sum_log_convex` — the consecutive case `P (m+1)^2 ≤ P m * P (m+2)`.

* `rpow_sum_sq_le` — the real-exponent form `(∑ wᵢ aᵢ^r)^2 ≤ W · ∑ wᵢ aᵢ^(2r)`
  for nonnegative data, the square bound specialised to `f = a^r`.

* `weightedPowerMean` and `weightedPowerMean_le_double` — the headline:
  the **weighted power mean** `M r = (∑ wᵢ aᵢ^r / ∑ wᵢ)^(1/r)` satisfies
  `M r ≤ M (2 r)` for `r > 0`. This is weighted Lᵖ monotonicity along the dyadic
  ladder of exponents, exactly the reach of the square bound (the continuous
  monotonicity `M p ≤ M q` for all `p ≤ q` needs Hölder, which is out of scope here).

* `weightedPowerMean_le_pow_two_mul` — iterating gives `M r ≤ M (2^k r)`.

All results are fully verified with no extra axioms.
-/

namespace ChebyshevSumWeightedPowerMean

open Finset

variable {ι : Type*}

/-! ## Natural-exponent Lyapunov chain (no roots) -/

/-- **Cauchy–Schwarz / Lyapunov chain for power sums.** For nonnegative data `a`
and nonnegative weights `w`, the power sums `P m = ∑ wᵢ aᵢ^m` obey
`P (m + t) ^ 2 ≤ P m * P (m + 2 t)`.

This is the discrete log-convexity of the power-sum sequence, obtained by feeding
the weighted square bound the weights `wᵢ aᵢ^m` and the function `aᵢ^t`. -/
theorem pow_sum_sq_le (a w : ι → ℝ) (s : Finset ι)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) (m t : ℕ) :
    (∑ i ∈ s, w i * a i ^ (m + t)) ^ 2
      ≤ (∑ i ∈ s, w i * a i ^ m) * ∑ i ∈ s, w i * a i ^ (m + 2 * t) := by
  have hw' : ∀ i ∈ s, 0 ≤ w i * a i ^ m := fun i hi =>
    mul_nonneg (hw i hi) (pow_nonneg (ha i hi) m)
  have h := ChebyshevSumWeighted.weighted_sq_sum_le (fun i => w i * a i ^ m)
    (fun i => a i ^ t) s hw'
  have e1 : ∑ i ∈ s, (w i * a i ^ m) * a i ^ t = ∑ i ∈ s, w i * a i ^ (m + t) :=
    Finset.sum_congr rfl fun i _ => by rw [mul_assoc, ← pow_add]
  have e2 : ∑ i ∈ s, (w i * a i ^ m) * (a i ^ t) ^ 2 = ∑ i ∈ s, w i * a i ^ (m + 2 * t) :=
    Finset.sum_congr rfl fun i _ => by
      rw [← pow_mul, mul_assoc, ← pow_add, Nat.mul_comm t 2]
  simpa only [e1, e2] using h

/-- **Log-convexity of power sums** (consecutive case): `P (m+1)^2 ≤ P m · P (m+2)`. -/
theorem pow_sum_log_convex (a w : ι → ℝ) (s : Finset ι)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) (m : ℕ) :
    (∑ i ∈ s, w i * a i ^ (m + 1)) ^ 2
      ≤ (∑ i ∈ s, w i * a i ^ m) * ∑ i ∈ s, w i * a i ^ (m + 2) := by
  simpa using pow_sum_sq_le a w s ha hw m 1

/-! ## Real-exponent square bound -/

/-- **Real-exponent square bound.** For nonnegative data and weights,
`(∑ wᵢ aᵢ^r)^2 ≤ (∑ wᵢ) · ∑ wᵢ aᵢ^(2r)`. This is the parent's square bound applied
to `f i = a i ^ r` (real `rpow`), the `r ↦ 2r` rung of the power-mean ladder. -/
theorem rpow_sum_sq_le (a w : ι → ℝ) (s : Finset ι)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) (r : ℝ) :
    (∑ i ∈ s, w i * a i ^ r) ^ 2
      ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * a i ^ (2 * r) := by
  have h := ChebyshevSumWeighted.weighted_sq_sum_le w (fun i => a i ^ r) s hw
  have e : ∑ i ∈ s, w i * (a i ^ r) ^ 2 = ∑ i ∈ s, w i * a i ^ (2 * r) :=
    Finset.sum_congr rfl fun i hi => by
      rw [← Real.rpow_natCast (a i ^ r) 2, ← Real.rpow_mul (ha i hi),
        show r * ((2 : ℕ) : ℝ) = 2 * r from by push_cast; ring]
  simpa only [e] using h

/-! ## The weighted power mean and its dyadic monotonicity -/

/-- The **weighted power mean** of order `r` of data `a` with weights `w` on `s`:
`M r = (∑ wᵢ aᵢ^r / ∑ wᵢ)^(1/r)`. -/
noncomputable def weightedPowerMean (w a : ι → ℝ) (s : Finset ι) (r : ℝ) : ℝ :=
  ((∑ i ∈ s, w i * a i ^ r) / (∑ i ∈ s, w i)) ^ (1 / r)

/-- **Weighted power-mean monotonicity along the dyadic ladder.** For nonnegative
data and weights with positive total mass, and any order `r > 0`,
`M r ≤ M (2 r)`. This is weighted Lᵖ monotonicity, derived purely from the
weighted square bound (the `r ↦ 2r` rung). -/
theorem weightedPowerMean_le_double (w a : ι → ℝ) (s : Finset ι)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) {r : ℝ} (hr : 0 < r) :
    weightedPowerMean w a s r ≤ weightedPowerMean w a s (2 * r) := by
  have hrne : r ≠ 0 := hr.ne'
  have hSr : 0 ≤ ∑ i ∈ s, w i * a i ^ r :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (ha i hi) r)
  have hsq : (∑ i ∈ s, w i * a i ^ r) ^ 2
      ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * a i ^ (2 * r) := rpow_sum_sq_le a w s ha hw r
  simp only [weightedPowerMean]
  set W := ∑ i ∈ s, w i with hWdef
  set Sr := ∑ i ∈ s, w i * a i ^ r with hSrdef
  set S2r := ∑ i ∈ s, w i * a i ^ (2 * r) with hS2rdef
  have hNr : 0 ≤ Sr / W := div_nonneg hSr hW.le
  have hW2 : (0 : ℝ) < W ^ 2 := by positivity
  have hN : (Sr / W) ^ 2 ≤ S2r / W := by
    rw [div_pow, div_le_div_iff₀ hW2 hW]
    nlinarith [mul_le_mul_of_nonneg_right hsq hW.le]
  have hexp : ((2 : ℕ) : ℝ) * (1 / (2 * r)) = 1 / r := by
    rw [Nat.cast_ofNat, one_div, one_div, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (two_ne_zero), one_mul]
  calc (Sr / W) ^ (1 / r)
      = ((Sr / W) ^ (2 : ℕ)) ^ (1 / (2 * r)) := by
        rw [← Real.rpow_natCast (Sr / W) 2, ← Real.rpow_mul hNr, hexp]
    _ ≤ (S2r / W) ^ (1 / (2 * r)) :=
        Real.rpow_le_rpow (pow_nonneg hNr 2) hN (by positivity)

/-- Iterating `weightedPowerMean_le_double`: `M r ≤ M (2^k r)` for every `k`. -/
theorem weightedPowerMean_le_pow_two_mul (w a : ι → ℝ) (s : Finset ι)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    weightedPowerMean w a s r ≤ weightedPowerMean w a s (2 ^ k * r) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hrn : (0 : ℝ) < 2 ^ n * r := by positivity
    have step := weightedPowerMean_le_double w a s ha hw hW hrn
    calc weightedPowerMean w a s r
        ≤ weightedPowerMean w a s (2 ^ n * r) := ih
      _ ≤ weightedPowerMean w a s (2 * (2 ^ n * r)) := step
      _ = weightedPowerMean w a s (2 ^ (n + 1) * r) := by
            rw [show (2 : ℝ) * (2 ^ n * r) = 2 ^ (n + 1) * r from by ring]

/-! ## Worked instance -/

/-- A concrete dyadic power-mean comparison `M 1 ≤ M 2` for the data `0, 1, 2`
with weights `1, 2, 3`, an instance of `weightedPowerMean_le_double`. -/
example :
    weightedPowerMean (fun i : ℕ => (i : ℝ) + 1) (fun i : ℕ => (i : ℝ)) (range 3) 1
      ≤ weightedPowerMean (fun i : ℕ => (i : ℝ) + 1) (fun i : ℕ => (i : ℝ)) (range 3) 2 := by
  have h := weightedPowerMean_le_double (fun i : ℕ => (i : ℝ) + 1) (fun i : ℕ => (i : ℝ))
    (range 3) (fun i _ => by positivity) (fun i _ => by positivity)
    (by norm_num [Finset.sum_range_succ]) (show (0 : ℝ) < 1 by norm_num)
  simpa using h

end ChebyshevSumWeightedPowerMean
