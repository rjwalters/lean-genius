import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# Even/Odd Splitting of the Geometric Series: ∑ r^(2n) = 1/(1−r²)

## What This Proves

For a real ratio `r` with `‖r‖ < 1`, the geometric series splits over its even
and odd index subsequences into two geometric series of ratio `r²`:

  ∑_{n=0}^{∞} r^(2n)    =  1/(1 − r²)        (even-power subseries)
  ∑_{n=0}^{∞} r^(2n+1)  =  r/(1 − r²)        (odd-power subseries)

and these recombine into the full geometric series

  ∑_{n=0}^{∞} r^(2n) + ∑_{n=0}^{∞} r^(2n+1)  =  ∑_{n=0}^{∞} rⁿ  =  1/(1 − r),

which is the analytic identity `1/(1−r²) + r/(1−r²) = 1/(1−r)` underneath the
factorisation `1 − r² = (1 − r)(1 + r)`.

## Why This Is Not Already in Mathlib

Mathlib provides the plain geometric series `tsum_geometric_of_norm_lt_one`
(`∑ rⁿ = (1−r)⁻¹`) but does not record the index-parity subsums.  Each of the
two subsums is *itself* a geometric series — but of ratio `r²`, not `r` — so the
content here is the reindexing `r^(2n) = (r²)ⁿ` together with the bound
`‖r²‖ = ‖r‖² < 1` that makes Mathlib's lemma applicable at the new ratio, plus
the recombination identity.

## Proof Strategy

1. **Even subseries.** Rewrite `r^(2n) = (r²)ⁿ` (`pow_mul`) and apply
   `hasSum_geometric_of_norm_lt_one` at ratio `r²`, valid because
   `‖r²‖ = ‖r‖² < 1`.
2. **Odd subseries.** Factor `r^(2n+1) = r · r^(2n)` and use `HasSum.mul_left r`
   on the even subseries; the value `r · (1−r²)⁻¹` is `r/(1−r²)`.
3. **Recombination.** Add the two `tsum` values and simplify
   `(1−r²)⁻¹ + r(1−r²)⁻¹ = (1−r)⁻¹` with `field_simp; ring` (both `1−r ≠ 0` and
   `1−r² ≠ 0` hold since `r² < 1`).

## Status: 0 sorries, 0 axioms
-/

namespace GeometricSeriesOQ09

variable {r : ℝ}

/-! ## Nonvanishing denominators -/

/-- `1 - r ≠ 0` whenever `‖r‖ < 1` (so `r ≠ 1`). -/
lemma one_sub_ne_zero (hr : ‖r‖ < 1) : (1 : ℝ) - r ≠ 0 :=
  sub_ne_zero.mpr fun h => by simp [← h] at hr

/-- `‖r²‖ < 1` whenever `‖r‖ < 1`, the key bound that lets us apply the
geometric-series lemma at the squared ratio. -/
lemma norm_sq_lt_one (hr : ‖r‖ < 1) : ‖r ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg r) hr (by norm_num)

/-- `1 - r² ≠ 0` whenever `‖r‖ < 1` (so `r² ≠ 1`). -/
lemma one_sub_sq_ne_zero (hr : ‖r‖ < 1) : (1 : ℝ) - r ^ 2 ≠ 0 :=
  sub_ne_zero.mpr fun h => by simpa [← h] using norm_sq_lt_one hr

/-! ## Even-power subseries -/

/-- **Even subseries, `HasSum` form**: `∑ r^(2n) = 1/(1 − r²)`. -/
theorem hasSum_geometric_even (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => r ^ (2 * n)) (1 - r ^ 2)⁻¹ := by
  have h := hasSum_geometric_of_norm_lt_one (norm_sq_lt_one hr)
  simpa only [pow_mul] using h

/-- **Even subseries, `tsum` form**: `∑ r^(2n) = 1/(1 − r²)`. -/
theorem tsum_geometric_even (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ (2 * n) = (1 - r ^ 2)⁻¹ :=
  (hasSum_geometric_even hr).tsum_eq

/-- The even subseries is summable. -/
theorem summable_geometric_even (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => r ^ (2 * n)) :=
  (hasSum_geometric_even hr).summable

/-! ## Odd-power subseries -/

/-- **Odd subseries, `HasSum` form**: `∑ r^(2n+1) = r/(1 − r²)`. -/
theorem hasSum_geometric_odd (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => r ^ (2 * n + 1)) (r * (1 - r ^ 2)⁻¹) := by
  have key : (fun n : ℕ => r ^ (2 * n + 1)) = (fun n : ℕ => r * r ^ (2 * n)) := by
    funext n; rw [pow_succ, mul_comm]
  rw [key]
  exact (hasSum_geometric_even hr).mul_left r

/-- **Odd subseries, `tsum` form**: `∑ r^(2n+1) = r/(1 − r²)`. -/
theorem tsum_geometric_odd (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ (2 * n + 1) = r * (1 - r ^ 2)⁻¹ :=
  (hasSum_geometric_odd hr).tsum_eq

/-- The odd subseries is summable. -/
theorem summable_geometric_odd (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => r ^ (2 * n + 1)) :=
  (hasSum_geometric_odd hr).summable

/-! ## Recombination into the full geometric series -/

/-- The even and odd subsums recombine into the full geometric series:
`∑ r^(2n) + ∑ r^(2n+1) = ∑ rⁿ = 1/(1 − r)`. -/
theorem tsum_even_add_odd (hr : ‖r‖ < 1) :
    (∑' n : ℕ, r ^ (2 * n)) + (∑' n : ℕ, r ^ (2 * n + 1)) = ∑' n : ℕ, r ^ n := by
  rw [tsum_geometric_even hr, tsum_geometric_odd hr, tsum_geometric_of_norm_lt_one hr]
  have h1 : (1 : ℝ) - r ≠ 0 := one_sub_ne_zero hr
  have h2 : (1 : ℝ) - r ^ 2 ≠ 0 := one_sub_sq_ne_zero hr
  field_simp
  ring

/-! ## Concrete values -/

/-- Sanity check at `r = 1/2`: `∑ (1/2)^(2n) = ∑ (1/4)ⁿ = 4/3`. -/
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ (2 * n) = 4 / 3 := by
  rw [tsum_geometric_even (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

/-- Sanity check at `r = 1/2`: `∑ (1/2)^(2n+1) = 2/3`. -/
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ (2 * n + 1) = 2 / 3 := by
  rw [tsum_geometric_odd (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

end GeometricSeriesOQ09
