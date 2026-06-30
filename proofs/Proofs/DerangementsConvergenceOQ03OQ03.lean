/-
  Derangements: effective second-order sandwich for |D(n) - n!/e|
  Open Question: derangements-convergence-oq-03-oq-03

  The parent (derangements-convergence-oq-03) proved the *rounding* result
  D(n) = round(n!/e), which only needs the one-sided bound
    |D(n) - n!/e| ≤ 1/(n+1).
  This entry sharpens that estimate to a two-sided sandwich, pinning down the
  error to within an interval of width 1/((n+1)(n+2)):

    1/(n+1) - 1/((n+1)(n+2))  ≤  |D(n) - n!/e|  ≤  1/(n+1).

  ## Main Result

  `derangements_second_order_sandwich` (PROVED, 0-axiom): for every n,
    1/(n+1) - 1/((n+1)(n+2)) ≤ |↑(numDerangements n) - n! * rexp(-1)| ≤ 1/(n+1).

  (The candidate asked for n ≥ 2; the statement in fact holds for all n. The
  n ≥ 2 regime is exactly where the lower bound forces the error to be a
  positive distance away from 1/2, which is what made the rounding result
  non-trivial.)

  ## Proof Strategy

  Write the exact tail
    D(n)/n! - rexp(-1) = -(-1)^(n+1) · A,    A := ∑'_k (-1)^k / ((n+1+k)!),
  so |D(n) - n! rexp(-1)| = n! · A with A ≥ 0.  The alternating series A is
  controlled by its first two terms:
    1/(n+1)! - 1/(n+2)!  ≤  A  ≤  1/(n+1)!.
  Multiplying through by n! gives the sandwich.

  The upper bound A ≤ 1/(n+1)! and nonnegativity A ≥ 0 are repackaged from the
  parent's `alt_partial_sum_le_first` / `alt_partial_sum_nonneg`.  The new
  ingredient is the refined lower bound `alt_partial_sum_ge_first_sub_second`:
  for N ≥ 2 the alternating partial sum exceeds (first term − second term),
  because the remaining tail is itself a nonnegative alternating sum.
-/

import Mathlib
import Proofs.DerangementsConvergence

open Finset Nat Real BigOperators Filter Topology

namespace DerangementsConvergenceOQ03OQ03

/-- The shifted alternating summand `(-1)^k / (m+k)!` is summable.
    (Mirrors the local computation inside `alternating_tail_bound`.) -/
lemma summable_shiftedAlt (m : ℕ) :
    Summable (fun k => (-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  have hbnd_summable : Summable (fun k => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
    have h1 : Summable (fun (k : ℕ) => (1 : ℝ) / (k.factorial : ℝ)) := by
      simpa only [one_pow] using summable_pow_div_factorial (1 : ℝ)
    exact h1.comp_injective (fun ⦃a b⦄ (h : m + a = m + b) => by omega)
  exact Summable.of_norm_bounded_eventually hbnd_summable (by
    filter_upwards with k
    apply le_of_eq
    simp only [norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast])

/-- Refined lower bound on the alternating partial sums: for `N ≥ 2` the partial
    sum exceeds the first term minus the second.  This is the new ingredient
    beyond the parent file (which only had `alt_partial_sum_le_first`). -/
lemma alt_partial_sum_ge_first_sub_second (m N : ℕ) :
    1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) ≤
    ∑ k ∈ range (N + 2), ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  -- Peel the two leading terms; the rest is a nonnegative alternating tail.
  have hdecomp :
      ∑ k ∈ range (N + 2), ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) =
        (1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ)) +
        ∑ k ∈ range N, ((-1 : ℝ) ^ k / (((m + 2) + k).factorial : ℝ)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hcongr :
        ∑ k ∈ range N, ((-1 : ℝ) ^ (k + 1 + 1) / ((m + (k + 1 + 1)).factorial : ℝ)) =
        ∑ k ∈ range N, ((-1 : ℝ) ^ k / (((m + 2) + k).factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k _
      have hpow : (-1 : ℝ) ^ (k + 1 + 1) = (-1 : ℝ) ^ k := by
        rw [pow_succ, pow_succ]; ring
      have hidx : m + (k + 1 + 1) = (m + 2) + k := by omega
      rw [hpow, hidx]
    rw [hcongr]
    simp only [Nat.add_zero, Nat.zero_add, pow_zero, pow_one, one_div]
    ring
  rw [hdecomp]
  have hnn := alt_partial_sum_nonneg (m + 2) N
  linarith

/-- Nonnegativity of the shifted alternating tail `A(m) = ∑'_k (-1)^k/(m+k)!`. -/
lemma shiftedAlt_tsum_nonneg (m : ℕ) :
    0 ≤ ∑' k, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (summable_shiftedAlt m).hasSum.tendsto_sum_nat
  filter_upwards with N
  exact alt_partial_sum_nonneg m N

/-- Upper bound: `A(m) ≤ 1/m!`. -/
lemma shiftedAlt_tsum_le_first (m : ℕ) :
    ∑' k, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) ≤ 1 / (m.factorial : ℝ) := by
  apply le_of_tendsto (summable_shiftedAlt m).hasSum.tendsto_sum_nat
  filter_upwards with N
  exact alt_partial_sum_le_first m N

/-- Lower bound: `A(m) ≥ 1/m! - 1/(m+1)!`. -/
lemma shiftedAlt_tsum_ge_first_sub_second (m : ℕ) :
    1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) ≤
    ∑' k, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  apply ge_of_tendsto (summable_shiftedAlt m).hasSum.tendsto_sum_nat
  filter_upwards [eventually_ge_atTop 2] with N hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  exact alt_partial_sum_ge_first_sub_second m M

/-- The signed error `D(n) - n!·e⁻¹` equals `-(-1)^(n+1) · n! · A(n+1)`,
    hence its absolute value is exactly `n! · A(n+1)`. -/
lemma abs_error_eq (n : ℕ) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| =
    (n.factorial : ℝ) * ∑' k, ((-1 : ℝ) ^ k / (((n + 1) + k).factorial : ℝ)) := by
  set A := ∑' k, ((-1 : ℝ) ^ k / (((n + 1) + k).factorial : ℝ)) with hA
  -- rexp(-1) = partial sum + tail, and tail = (-1)^(n+1) · A
  have htail : (∑' k, altFactTerm (n + 1 + k)) = (-1 : ℝ) ^ (n + 1) * A := by
    have hfactor : ∀ k, altFactTerm (n + 1 + k) =
        (-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ k / (((n + 1) + k).factorial : ℝ)) := by
      intro k; simp only [altFactTerm]; rw [pow_add]; ring
    rw [hA]
    rw [show (∑' k, altFactTerm (n + 1 + k)) =
        ∑' k, (-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ k / (((n + 1) + k).factorial : ℝ)) from
      tsum_congr hfactor, tsum_mul_left]
  -- assemble D(n) - n!·e⁻¹ = -n! · tail
  have hexp : rexp (-1) = altFactPartialSum n + ∑' k, altFactTerm (n + 1 + k) := by
    rw [exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  have hD : (numDerangements n : ℝ) = (n.factorial : ℝ) * altFactPartialSum n :=
    numDerangements_eq_factorial_mul_altSum n
  have hsigned : (numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1) =
      -((-1 : ℝ) ^ (n + 1) * ((n.factorial : ℝ) * A)) := by
    rw [hD, hexp, htail]; ring
  rw [hsigned, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
    Nat.abs_cast, abs_of_nonneg (shiftedAlt_tsum_nonneg (n + 1))]

/-- **Second-order sandwich for the derangement count.**
    For every `n`,
      `1/(n+1) - 1/((n+1)(n+2)) ≤ |D(n) - n!/e| ≤ 1/(n+1)`.
    This sharpens the parent rounding bound `|D(n) - n!/e| ≤ 1/(n+1)` with a
    matching lower bound of the same leading order. -/
theorem derangements_second_order_sandwich (n : ℕ) :
    1 / ((n : ℝ) + 1) - 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤
      |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| ∧
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| ≤ 1 / ((n : ℝ) + 1) := by
  rw [abs_error_eq n]
  set A := ∑' k, ((-1 : ℝ) ^ k / (((n + 1) + k).factorial : ℝ)) with hA
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr n.factorial_pos
  -- factorial ratio identities, m = n+1
  have hr1 : (n.factorial : ℝ) * (1 / (((n + 1).factorial : ℝ))) = 1 / ((n : ℝ) + 1) := by
    rw [Nat.factorial_succ]; push_cast; field_simp; try ring
  have hr2 : (n.factorial : ℝ) * (1 / (((n + 1 + 1).factorial : ℝ))) =
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; field_simp; try ring
  constructor
  · -- lower bound
    have hlo := shiftedAlt_tsum_ge_first_sub_second (n + 1)
    rw [← hA] at hlo
    have : (n.factorial : ℝ) *
        (1 / (((n + 1).factorial : ℝ)) - 1 / (((n + 1 + 1).factorial : ℝ))) ≤
        (n.factorial : ℝ) * A := by
      apply mul_le_mul_of_nonneg_left hlo hfact_pos.le
    rw [mul_sub, hr1, hr2] at this
    linarith
  · -- upper bound
    have hhi := shiftedAlt_tsum_le_first (n + 1)
    rw [← hA] at hhi
    have : (n.factorial : ℝ) * A ≤ (n.factorial : ℝ) * (1 / (((n + 1).factorial : ℝ))) := by
      apply mul_le_mul_of_nonneg_left hhi hfact_pos.le
    rw [hr1] at this
    linarith

end DerangementsConvergenceOQ03OQ03
