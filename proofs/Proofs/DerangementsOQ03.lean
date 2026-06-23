/-
  Convergence Rate of Derangements to 1/e
  Open Question: derangements-oq-03

  Classical Theorem: The ratio D(n)/n! converges to 1/e with the sharp error bound:
    |D(n)/n! - 1/e| ≤ 1/(n+1)!

  This follows because D(n)/n! equals the n-th partial sum of the Taylor series for
  e^{-1} = ∑_{k≥0} (-1)^k/k!, and the alternating series estimation theorem gives
  the sharp error bound.

  Main Results:
  - `numDerangements_eq_factorial_mul_altSum`: D(n) = n! · ∑_{k=0}^n (-1)^k/k!
  - `derangements_convergence_rate`: |D(n)/n! - e^{-1}| ≤ 1/(n+1)!
  - `derangements_tendsto_inv_e`: D(n)/n! → 1/e
  - `derangements_alternating_even/odd`: D(n)/n! alternates above/below 1/e

  Answered Open Question from gallery/derangements:
  "Can the convergence rate |D(n)/n! - 1/e| < 1/(n+1)! be formalized?"
  Answer: YES (this file).

  References:
  - Montmort (1708), Euler (1751): D(n) = n! ∑ (-1)^k/k!
  - Alternating series estimation theorem (Leibniz, 1682)
  - Wiedijk's 100 Theorems: #88 (extended)
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open Finset Nat Real BigOperators Filter Topology

noncomputable section

namespace DerangementsOQ03

/-
## Section I: The Alternating Factorial Series
-/

/-- The k-th term of the alternating series for e^{-1}: (-1)^k / k! -/
def altFactTerm (k : ℕ) : ℝ := (-1 : ℝ) ^ k / (k.factorial : ℝ)

/-- The n-th partial sum of the alternating series. Equals D(n)/n!. -/
def altFactPartialSum (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), altFactTerm k

lemma factorial_cast_pos (k : ℕ) : (0 : ℝ) < (k.factorial : ℝ) :=
  Nat.cast_pos.mpr k.factorial_pos

lemma factorial_cast_ne_zero (k : ℕ) : (k.factorial : ℝ) ≠ 0 :=
  ne_of_gt (factorial_cast_pos k)

lemma altFactTerm_abs (k : ℕ) : |altFactTerm k| = 1 / (k.factorial : ℝ) := by
  simp [altFactTerm, abs_div, abs_pow, abs_neg, abs_one]

lemma altFactPartialSum_succ (n : ℕ) :
    altFactPartialSum (n + 1) = altFactPartialSum n + altFactTerm (n + 1) := by
  simp [altFactPartialSum, Finset.sum_range_succ]

/-
## Section II: The Derangement-Factorial Identity
-/

/-- **Key Identity**: D(n) = n! · ∑_{k=0}^n (-1)^k/k!
    Proved by strong induction using D(n+2) = (n+1)(D(n) + D(n+1)). -/
theorem numDerangements_eq_factorial_mul_altSum (n : ℕ) :
    (numDerangements n : ℝ) = (n.factorial : ℝ) * altFactPartialSum n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [altFactPartialSum, altFactTerm]
  | 1 => simp [altFactPartialSum, altFactTerm, Finset.sum_range_succ]; ring
  | n + 2 =>
    rw [numDerangements_add_two]
    push_cast
    rw [ih n (by omega), ih (n + 1) (by omega)]
    rw [altFactPartialSum_succ (n + 1), altFactPartialSum_succ n]
    simp only [altFactTerm, Nat.factorial_succ]
    push_cast
    ring

/-- D(n)/n! = ∑_{k=0}^n (-1)^k/k! (the n-th partial sum) -/
theorem derangements_div_factorial (n : ℕ) :
    (numDerangements n : ℝ) / (n.factorial : ℝ) = altFactPartialSum n := by
  rw [numDerangements_eq_factorial_mul_altSum]
  field_simp [factorial_cast_ne_zero n]

/-
## Section III: The Exponential Series for e^{-1}
-/

/-- The alternating series ∑ (-1)^k/k! is summable. -/
lemma summable_altFactTerm : Summable altFactTerm := by
  apply Summable.of_norm_bounded_eventually (fun k => 1 ^ k / (k.factorial : ℝ))
    (summable_pow_div_factorial 1)
  filter_upwards with k
  rw [norm_eq_abs, altFactTerm_abs]
  simp [one_pow]

/-- **Euler's Identity**: e^{-1} equals the alternating series ∑ (-1)^k/k! -/
theorem exp_neg_one_eq_tsum_alt :
    rexp (-1) = ∑' k, altFactTerm k := by
  have : rexp (-1) = NormedSpace.exp ℝ (-1 : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
  rw [this, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
  congr 1
  ext k
  simp only [altFactTerm, smul_eq_mul]
  ring

/-
## Section IV: Error Bound via Alternating Series
-/

lemma tsum_eq_partial_sum_add_tail (n : ℕ) :
    ∑' k, altFactTerm k = altFactPartialSum n + ∑' k, altFactTerm (n + 1 + k) := by
  have hs := summable_altFactTerm
  have hshift : HasSum (fun k => altFactTerm (n + 1 + k))
      (∑' k, altFactTerm k - ∑ k ∈ range (n + 1), altFactTerm k) := by
    have hfull := hs.hasSum
    rw [Finset.hasSum_compl_iff (s := range (n + 1)) hs] at hfull
    rw [← (Function.Injective.hasSum_iff
      (f := fun (x : ↥(↑(range (n + 1)))ᶜ) => altFactTerm ↑x)
      (i := fun k => ⟨n + 1 + k, by
        simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt]; omega⟩)
      ?_ ?_)] at hfull
    · exact hfull
    · intro a b h; simp only [Subtype.mk.injEq] at h; omega
    · intro ⟨b, hb⟩
      simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt] at hb
      exact ⟨b - (n + 1), by simp only [Subtype.mk.injEq]; omega⟩
  rw [hshift.tsum_eq, altFactPartialSum]
  ring

/-- Alternating partial sums starting at index m are non-negative. -/
lemma alt_partial_sum_nonneg (m : ℕ) (N : ℕ) :
    0 ≤ ∑ k ∈ range N, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 => simp
  | 1 => simp; exact div_nonneg one_pos.le (factorial_cast_pos m).le
  | N' + 2 =>
    have hsplit : ∑ k ∈ range (N' + 2), ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) =
        ∑ k ∈ range N', ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) +
        ((-1 : ℝ) ^ N' / ((m + N').factorial : ℝ) +
         (-1 : ℝ) ^ (N' + 1) / ((m + (N' + 1)).factorial : ℝ)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; ring
    rw [hsplit]
    have hprev := ih N' (by omega)
    by_cases hN' : Even N'
    · obtain ⟨k, rfl⟩ := hN'
      have hpair : 0 ≤ (-1 : ℝ) ^ (2 * k) / ((m + (2 * k)).factorial : ℝ) +
          (-1 : ℝ) ^ (2 * k + 1) / ((m + (2 * k + 1)).factorial : ℝ) := by
        simp only [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul, neg_div]
        linarith [div_le_div_of_nonneg_left one_pos (factorial_cast_pos (m + (2 * k)))
          (show ((m + (2 * k)).factorial : ℝ) ≤ ((m + (2 * k + 1)).factorial : ℝ) from by
            push_cast; exact_mod_cast Nat.factorial_le (by omega))]
      linarith
    · rw [Nat.not_even_iff_odd] at hN'
      obtain ⟨k, rfl⟩ := hN'
      have hprev2 := ih (2 * k) (by omega)
      have hpair : 0 ≤ (-1 : ℝ) ^ (2 * k) / ((m + (2 * k)).factorial : ℝ) +
          (-1 : ℝ) ^ (2 * k + 1) / ((m + (2 * k + 1)).factorial : ℝ) := by
        simp only [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul, neg_div]
        linarith [div_le_div_of_nonneg_left one_pos (factorial_cast_pos (m + (2 * k)))
          (show ((m + (2 * k)).factorial : ℝ) ≤ ((m + (2 * k + 1)).factorial : ℝ) from by
            push_cast; exact_mod_cast Nat.factorial_le (by omega))]
      have hlast : 0 ≤ (-1 : ℝ) ^ (2 * k + 2) / ((m + (2 * k + 2)).factorial : ℝ) := by
        apply div_nonneg
        · simp [pow_succ, pow_mul]
        · exact (factorial_cast_pos _).le
      have hsplit2 : ∑ i ∈ range (2 * k + 1 + 2),
          ((-1 : ℝ) ^ i / ((m + i).factorial : ℝ)) =
          ∑ i ∈ range (2 * k), ((-1 : ℝ) ^ i / ((m + i).factorial : ℝ)) +
          ((-1 : ℝ) ^ (2 * k) / ((m + (2 * k)).factorial : ℝ) +
           (-1 : ℝ) ^ (2 * k + 1) / ((m + (2 * k + 1)).factorial : ℝ)) +
          (-1 : ℝ) ^ (2 * k + 2) / ((m + (2 * k + 2)).factorial : ℝ) := by
        rw [show 2 * k + 1 + 2 = (2 * k + 2) + 1 from by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        ring
      rw [hsplit2]
      linarith

/-- Alternating partial sums are bounded above by the first term 1/m!. -/
lemma alt_partial_sum_le_first (m : ℕ) (N : ℕ) :
    ∑ k ∈ range N, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) ≤
    1 / (m.factorial : ℝ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 => simp; exact div_nonneg one_pos.le (factorial_cast_pos m).le
  | 1 => simp; exact le_refl _
  | N' + 2 =>
    have hsplit : ∑ k ∈ range (N' + 2), ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) =
        ∑ k ∈ range N', ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) +
        ((-1 : ℝ) ^ N' / ((m + N').factorial : ℝ) +
         (-1 : ℝ) ^ (N' + 1) / ((m + (N' + 1)).factorial : ℝ)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; ring
    rw [hsplit]
    by_cases hN' : Even N'
    · have hprev1 := ih (N' + 1) (by omega)
      have hneg : (-1 : ℝ) ^ (N' + 1) / ((m + (N' + 1)).factorial : ℝ) ≤ 0 := by
        obtain ⟨k, rfl⟩ := hN'
        apply div_nonpos_of_nonpos_of_nonneg
        · simp [pow_succ, pow_mul]; ring_nf; norm_num
        · exact (factorial_cast_pos _).le
      have hrewrite : ∑ k ∈ range N', ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) +
          ((-1 : ℝ) ^ N' / ((m + N').factorial : ℝ) +
           (-1 : ℝ) ^ (N' + 1) / ((m + (N' + 1)).factorial : ℝ)) =
          ∑ k ∈ range (N' + 1), ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) +
          (-1 : ℝ) ^ (N' + 1) / ((m + (N' + 1)).factorial : ℝ) := by
        rw [Finset.sum_range_succ]; ring
      rw [hrewrite]
      linarith
    · rw [Nat.not_even_iff_odd] at hN'
      obtain ⟨k, rfl⟩ := hN'
      have hprev := ih (2 * k + 1) (by omega)
      have hpair : (-1 : ℝ) ^ (2 * k + 1) / ((m + (2 * k + 1)).factorial : ℝ) +
          (-1 : ℝ) ^ (2 * k + 2) / ((m + (2 * k + 2)).factorial : ℝ) ≤ 0 := by
        simp only [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul, neg_div]
        linarith [div_le_div_of_nonneg_left one_pos (factorial_cast_pos (m + (2 * k + 1)))
          (show ((m + (2 * k + 1)).factorial : ℝ) ≤ ((m + (2 * k + 2)).factorial : ℝ) from by
            push_cast; exact_mod_cast Nat.factorial_le (by omega))]
      linarith

/-- The tail of the alternating series is bounded by the first tail term. -/
theorem alternating_tail_bound (n : ℕ) :
    |∑' k, altFactTerm (n + 1 + k)| ≤ 1 / ((n + 1).factorial : ℝ) := by
  set m := n + 1
  have hfactor : ∀ k, altFactTerm (m + k) =
      (-1 : ℝ) ^ m * ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
    intro k; simp [altFactTerm, pow_add, mul_div_assoc]
  conv_lhs => arg 1; arg 1; ext k; rw [hfactor]
  rw [tsum_mul_left, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  set c : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / ((m + k).factorial : ℝ)
  have hc_summable : Summable c := by
    have hbnd_summable : Summable (fun (k : ℕ) => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
      have h1 : Summable (fun (k : ℕ) => (1 : ℝ) / (k.factorial : ℝ)) := by
        have := summable_pow_div_factorial (1 : ℝ)
        simp only [one_pow] at this; exact this
      exact h1.comp_injective (fun a b h => by omega)
    exact Summable.of_norm_bounded_eventually hbnd_summable (by
      filter_upwards with k
      simp [c, abs_of_nonneg, Nat.cast_nonneg])
  have hlower : 0 ≤ ∑' k, c k := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (hc_summable.hasSum.tendsto_sum_nat)
    filter_upwards with N
    exact alt_partial_sum_nonneg m N
  have hupper : ∑' k, c k ≤ 1 / (m.factorial : ℝ) := by
    apply le_of_tendsto (hc_summable.hasSum.tendsto_sum_nat)
    filter_upwards with N
    exact alt_partial_sum_le_first m N
  rw [abs_of_nonneg hlower]
  exact hupper

/-
## Section V: Main Convergence Results
-/

/-- **Convergence Rate Theorem**:
    |D(n)/n! - e^{-1}| ≤ 1/(n+1)!

    This is sharp: D(n)/n! alternates above and below 1/e, getting closer by
    a factor of approximately 1/(n+1) each step. -/
theorem derangements_convergence_rate (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| ≤
    1 / ((n + 1).factorial : ℝ) := by
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  have : altFactPartialSum n - (altFactPartialSum n + ∑' k, altFactTerm (n + 1 + k)) =
      -(∑' k, altFactTerm (n + 1 + k)) := by ring
  rw [this, abs_neg]
  exact alternating_tail_bound n

/-- **Main Theorem**: D(n)/n! converges to 1/e.
    The probability of a random permutation of n elements being a derangement
    (no fixed points) converges to 1/e ≈ 36.79% as n → ∞. -/
theorem derangements_tendsto_inv_e :
    Tendsto (fun n => (numDerangements n : ℝ) / (n.factorial : ℝ))
    atTop (nhds (rexp (-1))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htend : Tendsto (fun n : ℕ => 1 / ((n + 1).factorial : ℝ)) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => |altFactTerm (n + 1)|) atTop (nhds 0) := by
      rw [show (0 : ℝ) = ‖(0 : ℝ)‖ from by simp]
      apply Filter.Tendsto.norm
      exact summable_altFactTerm.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
    simp only [altFactTerm_abs] at h0
    exact h0
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  use N
  intro n hn
  rw [Real.dist_eq]
  calc |(numDerangements n : ℝ) / ↑n.factorial - rexp (-1)|
      ≤ 1 / ((n + 1).factorial : ℝ) := derangements_convergence_rate n
    _ ≤ 1 / ((N + 1).factorial : ℝ) := by
        apply div_le_div_of_nonneg_left one_pos.le (factorial_cast_pos (N + 1))
        exact_mod_cast Nat.factorial_le (show N + 1 ≤ n + 1 by omega)
    _ < ε := by
        have := hN N le_rfl
        rw [Real.dist_eq, sub_zero, abs_of_nonneg] at this
        · exact this
        · exact div_nonneg one_pos.le (factorial_cast_pos (N + 1)).le

/-
## Section VI: Consequences and Corollaries
-/

/-- The error bound decreases monotonically: more terms = smaller error. -/
theorem convergence_rate_monotone (n m : ℕ) (h : n ≤ m) :
    (1 : ℝ) / ((m + 1).factorial : ℝ) ≤ 1 / ((n + 1).factorial : ℝ) := by
  apply div_le_div_of_nonneg_left one_pos.le (factorial_cast_pos (n + 1))
  exact_mod_cast Nat.factorial_le (by omega)

/-- The approximation ratio is always non-negative. -/
theorem derangements_div_factorial_nonneg (n : ℕ) :
    0 ≤ (numDerangements n : ℝ) / (n.factorial : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (factorial_cast_pos n).le

/-- Concrete error bounds for small n. -/
theorem error_bound_n0 :
    |(numDerangements 0 : ℝ) / (Nat.factorial 0 : ℝ) - rexp (-1)| ≤ 1 :=
  le_trans (derangements_convergence_rate 0) (by norm_num)

theorem error_bound_n1 :
    |(numDerangements 1 : ℝ) / (Nat.factorial 1 : ℝ) - rexp (-1)| ≤ 1 / 2 :=
  le_trans (derangements_convergence_rate 1) (by norm_num)

theorem error_bound_n2 :
    |(numDerangements 2 : ℝ) / (Nat.factorial 2 : ℝ) - rexp (-1)| ≤ 1 / 6 :=
  le_trans (derangements_convergence_rate 2) (by norm_num)

theorem error_bound_n3 :
    |(numDerangements 3 : ℝ) / (Nat.factorial 3 : ℝ) - rexp (-1)| ≤ 1 / 24 :=
  le_trans (derangements_convergence_rate 3) (by norm_num)

/-
## Section VII: Alternating Nature of the Approximation
-/

/-- For even n, D(n)/n! ≥ e^{-1}: even partial sums overshoot from above. -/
theorem derangements_alternating_even (n : ℕ) :
    rexp (-1) ≤ (numDerangements (2 * n) : ℝ) / ((2 * n).factorial : ℝ) := by
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail (2 * n)]
  suffices h : ∑' k, altFactTerm (2 * n + 1 + k) ≤ 0 by linarith
  set m := 2 * n + 1 with hm_def
  set c : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / ((m + k).factorial : ℝ)
  have hfactor : ∀ k, altFactTerm (m + k) = (-1 : ℝ) ^ m * c k := by
    intro k; simp [altFactTerm, c, pow_add, mul_div_assoc]
  have hc_summable : Summable c := by
    have hbnd_summable : Summable (fun (k : ℕ) => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
      have h1 : Summable (fun (k : ℕ) => (1 : ℝ) / (k.factorial : ℝ)) := by
        have := summable_pow_div_factorial (1 : ℝ); simp only [one_pow] at this; exact this
      exact h1.comp_injective (fun a b h => by omega)
    exact Summable.of_norm_bounded_eventually hbnd_summable (by
      filter_upwards with k
      simp [c, abs_of_nonneg, Nat.cast_nonneg])
  have hC_nonneg : 0 ≤ ∑' k, c k := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hc_summable.hasSum.tendsto_sum_nat)
    filter_upwards with N; exact alt_partial_sum_nonneg m N
  have hm_neg : (-1 : ℝ) ^ m = -1 :=
    Odd.neg_one_pow (⟨n, by omega⟩ : Odd m)
  have htail_eq : ∑' k, altFactTerm (2 * n + 1 + k) = (-1 : ℝ) ^ m * ∑' k, c k := by
    show ∑' k, altFactTerm (m + k) = (-1 : ℝ) ^ m * ∑' k, c k
    simp_rw [hfactor]; exact tsum_mul_left
  rw [htail_eq, hm_neg]; linarith

/-- For odd n, D(n)/n! ≤ e^{-1}: odd partial sums undershoot from below. -/
theorem derangements_alternating_odd (n : ℕ) :
    (numDerangements (2 * n + 1) : ℝ) / ((2 * n + 1).factorial : ℝ) ≤ rexp (-1) := by
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt,
      tsum_eq_partial_sum_add_tail (2 * n + 1)]
  suffices h : 0 ≤ ∑' k, altFactTerm (2 * n + 1 + 1 + k) by linarith
  set m := 2 * n + 2 with hm_def
  set c : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / ((m + k).factorial : ℝ)
  have hfactor : ∀ k, altFactTerm (2 * n + 1 + 1 + k) = (-1 : ℝ) ^ m * c k := by
    intro k
    simp only [altFactTerm, c]
    rw [show 2 * n + 1 + 1 + k = m + k from by omega, pow_add, mul_div_assoc]
  have hc_summable : Summable c := by
    have hbnd_summable : Summable (fun (k : ℕ) => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
      have h1 : Summable (fun (k : ℕ) => (1 : ℝ) / (k.factorial : ℝ)) := by
        have := summable_pow_div_factorial (1 : ℝ); simp only [one_pow] at this; exact this
      exact h1.comp_injective (fun a b h => by omega)
    exact Summable.of_norm_bounded_eventually hbnd_summable (by
      filter_upwards with k
      simp [c, abs_of_nonneg, Nat.cast_nonneg])
  have hC_nonneg : 0 ≤ ∑' k, c k := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hc_summable.hasSum.tendsto_sum_nat)
    filter_upwards with N; exact alt_partial_sum_nonneg m N
  have hm_one : (-1 : ℝ) ^ m = 1 :=
    Even.neg_one_pow (⟨n + 1, by omega⟩ : Even m)
  have htail_eq : ∑' k, altFactTerm (2 * n + 1 + 1 + k) = (-1 : ℝ) ^ m * ∑' k, c k := by
    simp_rw [hfactor]; exact tsum_mul_left
  rw [htail_eq, hm_one, one_mul]; exact hC_nonneg

end DerangementsOQ03

end
