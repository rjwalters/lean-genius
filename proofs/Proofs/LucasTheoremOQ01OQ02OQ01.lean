import Mathlib
import Proofs.LucasTheoremOQ01

/-!
# Almost all binomial coefficients are even — density `0` and the Sierpiński dimension

The grandparent file (`Proofs.LucasTheoremOQ01`) proves **Glaisher's closed form**
`oddCount n = 2 ^ s₂(n)` for the number of odd entries in a single row of Pascal's
triangle.  The parent next step ("sum over rows") established the **Sierpiński count**:
the first `2^m` rows hold exactly `3^m` odd entries,
`∑_{n < 2^m} oddCount n = 3^m`.

This file pushes that count to its two classical consequences.

* **Total entries.**  The first `2^m` rows contain `∑_{n<2^m}(n+1) = 2^{m-1}(2^m+1)`
  entries in all; we record the clean integer identity
  `2 · totalEntries m = 2^m · (2^m + 1)`.  Since the odd entries are a subset,
  `3^m ≤ totalEntries m`, so the **even** entries number `totalEntries m − 3^m`.

* **Density `0` (almost all binomial coefficients are even).**  The proportion of odd
  entries among the first `2^m` rows is `3^m / totalEntries m`, which is squeezed below
  `2·(3/4)^m` and hence tends to `0`.  Equivalently, the natural density of *odd*
  binomial coefficients is `0`: **almost every binomial coefficient is even.**

* **The Sierpiński box-counting dimension.**  Colour the odd entries black: a
  `2^m`-tall block resolves the Sierpiński gasket at scale `2^{-m}`, covering it with
  `3^m` cells of side `2^{-m}`.  The box-counting exponent is therefore *exactly*
  `log(3^m) / log(2^m) = log 3 / log 2 = log₂ 3` for every `m ≥ 1`, with
  `1 < log₂ 3 < 2` — strictly between a curve and a region, the hallmark of a fractal.

The block-sum engine (`s2_two_pow_add`, `sum_oddCount_eq_three_pow`) is reproved inline
from the grandparent's Glaisher formula so this file is self-contained.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat Finset

open LucasOddEntries

namespace LucasSierpinskiDimension

/-! ## Block-sum engine (reproved from the grandparent's Glaisher formula) -/

/-- The binary-digit-sum recursion `s₂ n = (n mod 2) + s₂(n / 2)`, valid for all `n`. -/
theorem s2_step (n : ℕ) : s2 n = n % 2 + s2 (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s2]
  · exact s2_pos n hn

/-- Prepending a leading `1`-bit at position `m` increments the binary digit sum:
for `k < 2^m`, `s₂(2^m + k) = s₂(k) + 1`. -/
theorem s2_two_pow_add (m : ℕ) : ∀ k, k < 2 ^ m → s2 (2 ^ m + k) = s2 k + 1 := by
  induction m with
  | zero =>
    intro k hk
    interval_cases k
    simp only [pow_zero, Nat.add_zero]
    rw [s2_step 1, s2_zero]
  | succ m ih =>
    intro k hk
    rw [s2_step (2 ^ (m + 1) + k)]
    have e1 : (2 ^ (m + 1) + k) % 2 = k % 2 := by rw [pow_succ]; omega
    have e2 : (2 ^ (m + 1) + k) / 2 = 2 ^ m + k / 2 := by rw [pow_succ]; omega
    have hk2 : k / 2 < 2 ^ m := by rw [pow_succ] at hk; omega
    rw [e1, e2, ih (k / 2) hk2, s2_step k]
    ring

/-- The Sierpiński block sum in abstract form: `∑_{n<2^m} 2^{s₂ n} = 3^m`. -/
theorem sum_two_pow_s2 (m : ℕ) : ∑ n ∈ range (2 ^ m), 2 ^ s2 n = 3 ^ m := by
  induction m with
  | zero => simp [s2_zero]
  | succ m ih =>
    have hsplit : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    rw [hsplit, Finset.sum_range_add]
    have hsecond : ∑ n ∈ range (2 ^ m), 2 ^ s2 (2 ^ m + n)
        = 2 * ∑ n ∈ range (2 ^ m), 2 ^ s2 n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_range] at hn
      rw [s2_two_pow_add m n hn, pow_succ]
      ring
    rw [hsecond, ih, pow_succ]
    ring

/-- **Sierpiński count.** The first `2^m` rows of Pascal's triangle contain `3^m` odd
entries. -/
theorem sum_oddCount_eq_three_pow (m : ℕ) :
    ∑ n ∈ range (2 ^ m), oddCount n = 3 ^ m := by
  rw [← sum_two_pow_s2 m]
  exact Finset.sum_congr rfl (fun n _ => oddCount_eq_two_pow_s2 n)

/-! ## Total entry count -/

/-- The total number of entries in the first `N` rows of Pascal's triangle is the
triangular number `∑_{n<N}(n+1) = N(N+1)/2`. -/
def totalEntries (m : ℕ) : ℕ := ∑ n ∈ range (2 ^ m), (n + 1)

/-- Gauss' sum, doubled to stay in `ℕ`: `(∑_{n<N}(n+1))·2 = N(N+1)`. -/
theorem sum_range_succ_mul_two (N : ℕ) : (∑ n ∈ range N, (n + 1)) * 2 = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

/-- The clean integer identity for the number of entries in the first `2^m` rows:
`2 · totalEntries m = 2^m · (2^m + 1)` (so `totalEntries m = 2^{m-1}(2^m+1)`). -/
theorem two_mul_totalEntries (m : ℕ) :
    2 * totalEntries m = 2 ^ m * (2 ^ m + 1) := by
  rw [totalEntries, mul_comm]
  exact sum_range_succ_mul_two (2 ^ m)

/-- The odd entries are a subset of the row, so each row has at most `n+1` odd entries. -/
theorem oddCount_le_row (n : ℕ) : oddCount n ≤ n + 1 := by
  have : oddRow n ⊆ range (n + 1) := Finset.filter_subset _ _
  calc oddCount n = (oddRow n).card := rfl
    _ ≤ (range (n + 1)).card := Finset.card_le_card this
    _ = n + 1 := by rw [Finset.card_range]

/-- The `3^m` odd entries are a subset of all `totalEntries m` entries. -/
theorem three_pow_le_totalEntries (m : ℕ) : 3 ^ m ≤ totalEntries m := by
  rw [← sum_oddCount_eq_three_pow m, totalEntries]
  exact Finset.sum_le_sum (fun n _ => oddCount_le_row n)

/-- The number of **even** entries among the first `2^m` rows is `totalEntries m − 3^m`;
this records that they account for the complement of the `3^m` odd ones. -/
theorem evenEntries_eq (m : ℕ) :
    totalEntries m - 3 ^ m + 3 ^ m = totalEntries m :=
  Nat.sub_add_cancel (three_pow_le_totalEntries m)

/-! ## Density of odd binomial coefficients is `0` -/

/-- A real lower bound on the total entry count: `4^m / 2 ≤ totalEntries m`.  (Indeed
`2·totalEntries m = 2^m(2^m+1) = 4^m + 2^m ≥ 4^m`.) -/
theorem four_pow_div_two_le_totalEntries (m : ℕ) :
    (4 : ℝ) ^ m / 2 ≤ (totalEntries m : ℝ) := by
  have h : ((2 * totalEntries m : ℕ) : ℝ) = ((2 ^ m * (2 ^ m + 1) : ℕ) : ℝ) := by
    rw [two_mul_totalEntries]
  push_cast at h
  -- h : 2 * ↑(totalEntries m) = 2^m * (2^m + 1)
  have h4 : (4 : ℝ) ^ m = (2 : ℝ) ^ m * (2 : ℝ) ^ m := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
  nlinarith [h, h4, hpos]

/-- The proportion of **odd** entries among the first `2^m` rows of Pascal's triangle,
`oddDensity m = 3^m / totalEntries m`. -/
noncomputable def oddDensity (m : ℕ) : ℝ := (3 : ℝ) ^ m / (totalEntries m : ℝ)

/-- The odd-entry proportion is squeezed below `2·(3/4)^m`. -/
theorem oddDensity_le (m : ℕ) : oddDensity m ≤ 2 * (3 / 4 : ℝ) ^ m := by
  have hstep : oddDensity m ≤ (3 : ℝ) ^ m / ((4 : ℝ) ^ m / 2) := by
    rw [oddDensity]
    gcongr
    exact four_pow_div_two_le_totalEntries m
  have hsimp : (3 : ℝ) ^ m / ((4 : ℝ) ^ m / 2) = 2 * (3 / 4 : ℝ) ^ m := by
    rw [div_pow]
    field_simp
  rw [hsimp] at hstep
  exact hstep

/-- **Almost all binomial coefficients are even.**  The proportion of odd entries among
the first `2^m` rows of Pascal's triangle tends to `0` as `m → ∞`. -/
theorem oddDensity_tendsto_zero :
    Filter.Tendsto oddDensity Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun m => 2 * (3 / 4 : ℝ) ^ m) Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun m => (3 / 4 : ℝ) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := hbase.const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero (fun m => ?_) oddDensity_le hg
  rw [oddDensity]
  positivity

/-! ## The Sierpiński box-counting dimension -/

/-- The fractal (box-counting / Hausdorff) dimension of the Sierpiński gasket,
`log₂ 3 = log 3 / log 2 ≈ 1.585`. -/
noncomputable def sierpinskiDimension : ℝ := Real.logb 2 3

/-- **Exact box-counting dimension.**  Resolving the odd-entry pattern at scale `2^{-m}`
covers it with `3^m` cells, so the box-counting exponent `log(#cells)/log(1/scale)` is
*exactly* the Sierpiński dimension `log₂ 3` for every `m ≥ 1` (no limit required). -/
theorem boxCount_ratio_eq_dimension (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((3 : ℝ) ^ m) / Real.log ((2 : ℝ) ^ m) = sierpinskiDimension := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.log_pow, Real.log_pow, sierpinskiDimension, Real.logb,
      mul_div_mul_left _ _ hm0]

/-- `1 < log₂ 3`: the Sierpiński gasket is strictly more than `1`-dimensional. -/
theorem one_lt_sierpinskiDimension : 1 < sierpinskiDimension := by
  rw [sierpinskiDimension, Real.logb]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h2, one_mul]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `log₂ 3 < 2`: the Sierpiński gasket is strictly less than `2`-dimensional. -/
theorem sierpinskiDimension_lt_two : sierpinskiDimension < 2 := by
  rw [sierpinskiDimension, Real.logb]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ h2]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  calc Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    _ = 2 * Real.log 2 := hlog4

/-! ## Sanity checks -/

/-- The first `4 = 2²` rows hold `1+2+3+4 = 10` entries, of which `9 = 3²` are odd and
`1` is even (the single `2` in row `2`). -/
example : totalEntries 2 = 10 := by decide

/-- The first `8 = 2³` rows hold `36` entries: `27 = 3³` odd and `9` even. -/
example : totalEntries 3 = 36 := by decide

/-- `2 · totalEntries 3 = 8 · 9 = 72`. -/
example : 2 * totalEntries 3 = 2 ^ 3 * (2 ^ 3 + 1) := by decide

end LucasSierpinskiDimension
