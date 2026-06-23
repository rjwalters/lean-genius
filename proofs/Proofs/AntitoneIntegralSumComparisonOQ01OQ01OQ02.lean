import Mathlib

/-
# Explicit Remainder Bound for the p-Series Tail

This is the open-question companion to `AntitoneIntegralSumComparisonOQ01OQ01`.  That
parent file used the **antitone integral test** to show that every partial sum of the
p-series `∑ 1/nᵖ` is bounded by `1/(p−1)`, the value of the improper integral
`∫₁^∞ x^{−p} dx`, thereby proving convergence for `p > 1` *directly from the comparison*.

The bound `1/(p−1)` is a single uniform constant; it says nothing about **how fast** the
series converges.  The open question asks for the **explicit remainder** — a quantitative
rate of convergence.  Running the very same integral test, but starting the comparison at
`x = N` instead of `x = 1`, pins the tail down sharply:

  ∑_{n > N} 1/nᵖ  ≤  ∫_N^∞ x^{−p} dx  =  N^{1−p}/(p−1)  =  1/((p−1) · N^{p−1}).

Concretely, the development below proves, for `p > 1` and `N ≥ 1`:

* **Tail partial-sum bound** (`pseries_tail_partial_le`): every finite tail
  `∑_{i<m} 1/(N+1+i)ᵖ` is bounded by `N^{1−p}/(p−1)`, uniformly in `m`.
* **Tail bound** (`pseries_tail_tsum_le`): passing to the limit,
  `∑'_{i} 1/(N+1+i)ᵖ ≤ N^{1−p}/(p−1)`.
* **Remainder bound** (`pseries_remainder_le`): identifying the tail with the genuine
  truncation error, `(∑'_n 1/nᵖ) − (∑_{n ≤ N} 1/nᵖ) ≤ N^{1−p}/(p−1)`.
* **Explicit form** (`pseries_tail_explicit`): the same bound written as the textbook
  `1/((p−1) · N^{p−1})`, exhibiting the `O(N^{1−p})` decay of the remainder.

The Basel exponent `p = 2` then gives the clean estimate `∑_{n>N} 1/n² ≤ 1/N`.

All results are fully machine-verified: 0 sorries, 0 axioms.
-/

namespace AntitoneIntegralSumComparisonOQ01OQ01OQ02

open scoped BigOperators
open Finset intervalIntegral

/-! ## The tail partial-sum bound -/

/-- **Tail partial-sum bound.**  For `p > 1` and `N ≥ 1`, every finite tail
`∑_{i<m} 1/(N+1+i)ᵖ` is bounded by `N^{1−p}/(p−1)`, the value of the improper integral
`∫_N^∞ x^{−p} dx`.  This is the antitone integral test applied to `1/xᵖ` on `[N, N+m]`,
the parent's `pseries_partial_sum_le` shifted to start at `N`. -/
theorem pseries_tail_partial_le (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) (m : ℕ) :
    (∑ i ∈ Finset.range m, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p) ≤ (N : ℝ) ^ (1 - p) / (p - 1) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- `1/xᵖ` is antitone on `[N, N+m]`.
  have hanti : AntitoneOn (fun x : ℝ => 1 / x ^ p) (Set.Icc (N : ℝ) ((N : ℝ) + (m : ℝ))) := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hNpos hx.1
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 p)
      (Real.rpow_le_rpow hx0.le hxy hp0.le)
  -- Rewrite `1/xᵖ` as `x^{−p}` on the interval, to use `integral_rpow`.
  have hcongr : (∫ x in (N : ℝ)..(N : ℝ) + (m : ℝ), 1 / x ^ p)
      = ∫ x in (N : ℝ)..(N : ℝ) + (m : ℝ), x ^ (-p) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (by positivity))] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hNpos hx.1
    rw [Real.rpow_neg hx0.le, one_div]
  -- Evaluate the integral.
  have hint : (∫ x in (N : ℝ)..(N : ℝ) + (m : ℝ), 1 / x ^ p)
      = (((N : ℝ) + (m : ℝ)) ^ (-p + 1) - (N : ℝ) ^ (-p + 1)) / (-p + 1) := by
    rw [hcongr, integral_rpow (Or.inr ⟨ne_of_lt (by linarith),
      Set.notMem_uIcc_of_lt hNpos
        (lt_of_lt_of_le hNpos (le_add_of_nonneg_right (by positivity)))⟩)]
  -- The integral test: the right Riemann sum is below the integral.
  have key : (∑ i ∈ Finset.range m, 1 / ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ p)
      ≤ ∫ x in (N : ℝ)..(N : ℝ) + (m : ℝ), 1 / x ^ p :=
    hanti.sum_le_integral
  -- Reconcile the summation index `N + (i+1)` with `i + (N+1)`.
  have hsum_eq : (∑ i ∈ Finset.range m, 1 / ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ p)
      = ∑ i ∈ Finset.range m, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) = (((i + (N + 1) : ℕ)) : ℝ) by push_cast; ring]
  rw [hint] at key
  rw [← hsum_eq]
  refine le_trans key ?_
  -- Bound the integral value `((N+m)^{1−p} − N^{1−p})/(1−p)` by `N^{1−p}/(p−1)`.
  rw [show (-p + 1) = (1 - p) by ring]
  have hA : (0 : ℝ) ≤ (N : ℝ) ^ (1 - p) := Real.rpow_nonneg hNpos.le _
  have hB : (0 : ℝ) ≤ ((N : ℝ) + (m : ℝ)) ^ (1 - p) := Real.rpow_nonneg (by positivity) _
  have hpm : (0 : ℝ) < p - 1 := by linarith
  have hp1ne : (1 : ℝ) - p ≠ 0 := by linarith
  have hpm_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsplit : (((N : ℝ) + (m : ℝ)) ^ (1 - p) - (N : ℝ) ^ (1 - p)) / (1 - p)
      = (N : ℝ) ^ (1 - p) / (p - 1) - ((N : ℝ) + (m : ℝ)) ^ (1 - p) / (p - 1) := by
    field_simp
    ring
  rw [hsplit]
  have hBnn : (0 : ℝ) ≤ ((N : ℝ) + (m : ℝ)) ^ (1 - p) / (p - 1) := div_nonneg hB hpm.le
  linarith

/-! ## The tail bound -/

/-- **Tail bound for the p-series.**  For `p > 1` and `N ≥ 1`, the full tail
`∑'_{i} 1/(N+1+i)ᵖ` is bounded by `N^{1−p}/(p−1)`.  Obtained from the uniform
partial-sum bound by passing to the limit (`Real.tsum_le_of_sum_range_le`). -/
theorem pseries_tail_tsum_le (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    (∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p) ≤ (N : ℝ) ^ (1 - p) / (p - 1) := by
  apply Real.tsum_le_of_sum_range_le
  · intro i; positivity
  · intro m; exact pseries_tail_partial_le p hp N hN m

/-! ## The genuine remainder bound -/

/-- **Explicit remainder bound.**  For `p > 1` and `N ≥ 1`, the truncation error of the
p-series after the first `N + 1` terms (indices `0, …, N`) is bounded by `N^{1−p}/(p−1)`.
The remainder is identified with the tail via `Summable.sum_add_tsum_nat_add`. -/
theorem pseries_remainder_le (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ p) - (∑ i ∈ Finset.range (N + 1), 1 / (i : ℝ) ^ p)
      ≤ (N : ℝ) ^ (1 - p) / (p - 1) := by
  have hsummable : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  -- `∑'_n = (∑_{i ≤ N}) + (tail)`, so `remainder = tail`.
  have hrem : (∑' n : ℕ, 1 / (n : ℝ) ^ p)
      = (∑ i ∈ Finset.range (N + 1), 1 / (i : ℝ) ^ p)
        + ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p :=
    (hsummable.sum_add_tsum_nat_add (N + 1)).symm
  have hcancel : (∑ i ∈ Finset.range (N + 1), 1 / (i : ℝ) ^ p)
        + (∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p)
        - (∑ i ∈ Finset.range (N + 1), 1 / (i : ℝ) ^ p)
      = ∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p := by ring
  rw [hrem, hcancel]
  exact pseries_tail_tsum_le p hp N hN

/-! ## The explicit `1/((p−1)·N^{p−1})` form -/

/-- **Explicit remainder, textbook form.**  Rewriting `N^{1−p}/(p−1)` as
`1/((p−1)·N^{p−1})` exhibits the `O(N^{1−p})` decay of the p-series tail. -/
theorem pseries_tail_explicit (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    (∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ p) ≤ 1 / ((p - 1) * (N : ℝ) ^ (p - 1)) := by
  have h := pseries_tail_tsum_le p hp N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpm_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hNp : (0 : ℝ) < (N : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hNpos _
  have heq : (N : ℝ) ^ (1 - p) / (p - 1) = 1 / ((p - 1) * (N : ℝ) ^ (p - 1)) := by
    rw [show (1 - p) = -(p - 1) by ring, Real.rpow_neg hNpos.le]
    field_simp
  rwa [heq] at h

/-! ## Worked witnesses -/

/-- **Basel-exponent rate.**  For `p = 2`, the explicit tail bound is the clean estimate
`∑_{n>N} 1/n² ≤ 1/N`. -/
example (N : ℕ) (hN : 1 ≤ N) :
    (∑' i : ℕ, 1 / (((i + (N + 1) : ℕ)) : ℝ) ^ (2 : ℝ)) ≤ 1 / (N : ℝ) := by
  have h := pseries_tail_explicit 2 (by norm_num) N hN
  have heq : (1 : ℝ) / (((2 : ℝ) - 1) * (N : ℝ) ^ ((2 : ℝ) - 1)) = 1 / (N : ℝ) := by
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one]
    norm_num
  rwa [heq] at h

/-- The remainder bound is genuinely a bound on the truncation error of `∑ 1/n²`. -/
example : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) - (∑ i ∈ Finset.range 11, 1 / (i : ℝ) ^ (2 : ℝ))
    ≤ (10 : ℝ) ^ (1 - 2 : ℝ) / ((2 : ℝ) - 1) :=
  pseries_remainder_le 2 (by norm_num) 10 (by norm_num)

end AntitoneIntegralSumComparisonOQ01OQ01OQ02
