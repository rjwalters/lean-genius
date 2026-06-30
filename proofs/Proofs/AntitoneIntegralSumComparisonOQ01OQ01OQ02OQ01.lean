import Mathlib
import Proofs.AntitoneIntegralSumComparisonOQ01OQ01OQ02

/-
# Matching lower bound and two-sided sandwich for the p-series tail

The parent file `AntitoneIntegralSumComparisonOQ01OQ01OQ02` proved the **upper**
remainder bound for the p-series via the antitone integral test: for `p > 1` and `N ≥ 1`,

  ∑_{n > N} 1/nᵖ  ≤  ∫_N^∞ x^{−p} dx  =  N^{1−p}/(p−1).

That file's own open question asks for the **matching lower bound**, obtained from the
*left* Riemann sum instead of the right one.  A decreasing function over-estimates its
integral when sampled at left endpoints, so

  ∑_{n > N} 1/nᵖ  ≥  ∫_{N+1}^∞ x^{−p} dx  =  (N+1)^{1−p}/(p−1).

This file proves that lower bound and assembles the two-sided **sandwich**

  (N+1)^{1−p}/(p−1)  ≤  ∑_{n > N} 1/nᵖ  ≤  N^{1−p}/(p−1),

pinning the remainder between two consecutive values of the same primitive
`x ↦ x^{1−p}/(p−1)` and confirming its leading order is exactly `N^{1−p}`.

For the Basel exponent `p = 2` the sandwich collapses to the textbook estimate

  1/(N+1)  ≤  ∑_{n > N} 1/n²  ≤  1/N.

Results (all fully machine-verified, 0 sorries, 0 axioms):

* `pseries_tail_partial_ge`  — every finite tail partial sum dominates the integral
  `∫_{N+1}^{N+1+m} x^{−p} dx`, i.e. `((N+1)^{1−p} − (N+1+m)^{1−p})/(p−1) ≤ ∑_{i<m} 1/(N+1+i)ᵖ`.
* `pseries_tail_tsum_ge`  — passing to the limit, `(N+1)^{1−p}/(p−1) ≤ ∑'_i 1/(N+1+i)ᵖ`.
* `pseries_tail_ge_explicit`  — the textbook form `1/((p−1)·(N+1)^{p−1}) ≤ tail`.
* `pseries_tail_sandwich`  — the two-sided bound, combining the new lower bound with the
  parent's upper bound.
-/

namespace AntitoneIntegralSumComparisonOQ01OQ01OQ02OQ01

open scoped BigOperators
open Finset intervalIntegral Filter Topology

/-! ## The tail partial-sum lower bound -/

/-- **Tail partial-sum lower bound.**  For `p > 1` and `N ≥ 1`, every finite tail
`∑_{i<m} 1/(N+1+i)ᵖ` dominates the integral `∫_{N+1}^{N+1+m} x^{−p} dx`, whose value is
`((N+1)^{1−p} − (N+1+m)^{1−p})/(p−1)`.  This is the antitone integral test applied to
`1/xᵖ` on `[N+1, N+1+m]` in its *left*-Riemann form (`AntitoneOn.integral_le_sum`): a
decreasing function over-estimates its integral on left endpoints. -/
theorem pseries_tail_partial_ge (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) (m : ℕ) :
    (((N : ℝ) + 1) ^ (1 - p) - (((N : ℝ) + 1) + (m : ℝ)) ^ (1 - p)) / (p - 1)
      ≤ ∑ i ∈ Finset.range m, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- `1/xᵖ` is antitone on `[N+1, N+1+m]`.
  have hanti : AntitoneOn (fun x : ℝ => 1 / x ^ p)
      (Set.Icc ((N : ℝ) + 1) (((N : ℝ) + 1) + (m : ℝ))) := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hN1pos hx.1
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 p)
      (Real.rpow_le_rpow hx0.le hxy hp0.le)
  -- Rewrite `1/xᵖ` as `x^{−p}` on the interval, to use `integral_rpow`.
  have hcongr : (∫ x in ((N : ℝ) + 1)..((N : ℝ) + 1) + (m : ℝ), 1 / x ^ p)
      = ∫ x in ((N : ℝ) + 1)..((N : ℝ) + 1) + (m : ℝ), x ^ (-p) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (by positivity))] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hN1pos hx.1
    rw [Real.rpow_neg hx0.le, one_div]
  -- Evaluate the integral.
  have hint : (∫ x in ((N : ℝ) + 1)..((N : ℝ) + 1) + (m : ℝ), 1 / x ^ p)
      = ((((N : ℝ) + 1) + (m : ℝ)) ^ (-p + 1) - ((N : ℝ) + 1) ^ (-p + 1)) / (-p + 1) := by
    rw [hcongr, integral_rpow (Or.inr ⟨ne_of_lt (by linarith),
      Set.notMem_uIcc_of_lt hN1pos
        (lt_of_lt_of_le hN1pos (le_add_of_nonneg_right (by positivity)))⟩)]
  -- The integral test (left Riemann sum): the integral underestimates the sum.
  have key := hanti.integral_le_sum
  -- Reconcile the summation index `(N+1) + i` with `i + (N+1)`.
  have hsum_eq : (∑ i ∈ Finset.range m, 1 / (((N : ℝ) + 1) + (i : ℝ)) ^ p)
      = ∑ i ∈ Finset.range m, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show (((N : ℝ) + 1) + (i : ℝ)) = (((i + (N + 1) : ℕ)) : ℝ) by push_cast; ring]
  rw [hint, hsum_eq] at key
  -- `key : (integral value) ≤ ∑_{i<m} 1/(i+(N+1))ᵖ`.  Now match the LHS.
  refine le_trans ?_ key
  rw [show (-p + 1) = (1 - p) by ring]
  have hp1ne : (1 : ℝ) - p ≠ 0 := by linarith
  have hpm_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hval : (((N : ℝ) + 1) ^ (1 - p) - (((N : ℝ) + 1) + (m : ℝ)) ^ (1 - p)) / (p - 1)
      = ((((N : ℝ) + 1) + (m : ℝ)) ^ (1 - p) - ((N : ℝ) + 1) ^ (1 - p)) / (1 - p) := by
    field_simp
    ring
  rw [hval]

/-! ## The tail lower bound (full tsum) -/

set_option maxHeartbeats 800000 in
/-- **Tail lower bound for the p-series.**  For `p > 1` and `N ≥ 1`, the full tail
`∑'_{i} 1/(N+1+i)ᵖ` is bounded below by `(N+1)^{1−p}/(p−1)`, the value of the improper
integral `∫_{N+1}^∞ x^{−p} dx`.  The uniform partial-sum lower bound
`((N+1)^{1−p} − (N+1+m)^{1−p})/(p−1)` converges up to `(N+1)^{1−p}/(p−1)` as `m → ∞`
(the subtracted term `(N+1+m)^{1−p} → 0` since `1 − p < 0`), and each partial sum is `≤`
the tsum, so the limit is `≤` the tsum. -/
theorem pseries_tail_tsum_ge (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ (1 - p) / (p - 1) ≤ ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by
  have hsummable : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hsummable_tail : Summable (fun i : ℕ => 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p) :=
    (summable_nat_add_iff (N + 1)).mpr hsummable
  -- The uniform lower bound `u m ≤ tsum` for every `m`.
  have hle : ∀ m : ℕ,
      (((N : ℝ) + 1) ^ (1 - p) - (((N : ℝ) + 1) + (m : ℝ)) ^ (1 - p)) / (p - 1)
        ≤ ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by
    intro m
    refine le_trans (pseries_tail_partial_ge p hp N hN m) ?_
    exact Summable.sum_le_tsum (Finset.range m) (fun i _ => by positivity) hsummable_tail
  -- `u m → (N+1)^{1−p}/(p−1)` as `m → ∞`.
  have hbase : Tendsto (fun m : ℕ => ((N : ℝ) + 1) + (m : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop ((N : ℝ) + 1) tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun x : ℝ => x ^ (1 - p)) atTop (𝓝 0) := by
    rw [show (1 - p) = -(p - 1) by ring]
    exact tendsto_rpow_neg_atTop (by linarith)
  have h1 : Tendsto (fun m : ℕ => (((N : ℝ) + 1) + (m : ℝ)) ^ (1 - p)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hneg.comp hbase
  have h2 : Tendsto
      (fun m : ℕ => ((N : ℝ) + 1) ^ (1 - p) - (((N : ℝ) + 1) + (m : ℝ)) ^ (1 - p))
      atTop (𝓝 (((N : ℝ) + 1) ^ (1 - p) - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds h1
  have h3 := h2.div_const (p - 1)
  rw [sub_zero] at h3
  exact le_of_tendsto' h3 hle

/-! ## The explicit `1/((p−1)·(N+1)^{p−1})` form -/

/-- **Explicit lower bound, textbook form.**  Rewriting `(N+1)^{1−p}/(p−1)` as
`1/((p−1)·(N+1)^{p−1})` exhibits the `O(N^{1−p})` order of the p-series tail from below. -/
theorem pseries_tail_ge_explicit (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    1 / ((p - 1) * ((N : ℝ) + 1) ^ (p - 1)) ≤ ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by
  have h := pseries_tail_tsum_ge p hp N hN
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpm_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hNp : (0 : ℝ) < ((N : ℝ) + 1) ^ (p - 1) := Real.rpow_pos_of_pos hN1pos _
  have heq : ((N : ℝ) + 1) ^ (1 - p) / (p - 1) = 1 / ((p - 1) * ((N : ℝ) + 1) ^ (p - 1)) := by
    rw [show (1 - p) = -(p - 1) by ring, Real.rpow_neg hN1pos.le]
    field_simp
  rwa [heq] at h

/-! ## The two-sided sandwich -/

/-- **Two-sided remainder sandwich.**  For `p > 1` and `N ≥ 1`, the p-series tail is
pinned between two consecutive values of the primitive `x ↦ x^{1−p}/(p−1)`:

  `(N+1)^{1−p}/(p−1) ≤ ∑'_{i} 1/(N+1+i)ᵖ ≤ N^{1−p}/(p−1)`.

The lower bound is the new `pseries_tail_tsum_ge` (left Riemann sum / `∫_{N+1}^∞`); the
upper bound is the parent's `pseries_tail_tsum_le` (right Riemann sum / `∫_N^∞`).  Both
flanks have leading order `N^{1−p}`, so the remainder's order is exactly `N^{1−p}`. -/
theorem pseries_tail_sandwich (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ (1 - p) / (p - 1) ≤ ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p ∧
      (∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p) ≤ (N : ℝ) ^ (1 - p) / (p - 1) :=
  ⟨pseries_tail_tsum_ge p hp N hN,
   AntitoneIntegralSumComparisonOQ01OQ01OQ02.pseries_tail_tsum_le p hp N hN⟩

/-! ## Worked witnesses -/

/-- **Basel-exponent sandwich.**  For `p = 2`, the two-sided bound is the clean estimate
`1/(N+1) ≤ ∑_{n>N} 1/n² ≤ 1/N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ≤ ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ (2 : ℝ) ∧
      (∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ (2 : ℝ)) ≤ 1 / (N : ℝ) := by
  obtain ⟨hlo, hhi⟩ := pseries_tail_sandwich 2 (by norm_num) N hN
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨?_, ?_⟩
  · have hleq : ((N : ℝ) + 1) ^ ((1 : ℝ) - 2) / ((2 : ℝ) - 1) = 1 / ((N : ℝ) + 1) := by
      rw [show ((1 : ℝ) - 2) = -(1 : ℝ) by norm_num, Real.rpow_neg hN1pos.le, Real.rpow_one]
      norm_num
    rwa [hleq] at hlo
  · have hheq : (N : ℝ) ^ ((1 : ℝ) - 2) / ((2 : ℝ) - 1) = 1 / (N : ℝ) := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      rw [show ((1 : ℝ) - 2) = -(1 : ℝ) by norm_num, Real.rpow_neg hNpos.le, Real.rpow_one]
      norm_num
    rwa [hheq] at hhi

/-- The lower bound is a genuine quantitative floor on the truncation error of `∑ 1/n²`:
`1/11 ≤ ∑_{n>10} 1/n²` (the explicit textbook form at `p = 2`, `N = 10`). -/
example : 1 / ((11 : ℝ)) ≤ ∑' i : ℕ, 1 / (((i + (10 + 1) : ℕ)) : ℝ) ^ (2 : ℝ) := by
  have h := pseries_tail_ge_explicit 2 (by norm_num) 10 (by norm_num)
  have heq : 1 / (((2 : ℝ) - 1) * (((10 : ℕ) : ℝ) + 1) ^ ((2 : ℝ) - 1)) = 1 / (11 : ℝ) := by
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one]
    norm_num
  rwa [heq] at h

end AntitoneIntegralSumComparisonOQ01OQ01OQ02OQ01
