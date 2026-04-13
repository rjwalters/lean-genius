/-
  Closed-Form Error: D(n)/n! - 1/e as Alternating Sum
  Open Question: derangements-oq-03-oq-01-oq-02

  The error D(n)/n! - 1/e has an exact closed-form representation as a
  signed alternating series:

    D(n)/n! - 1/e = (-1)^n · ∑_{k=0}^∞ (-1)^k / (n+1+k)!

  The positive factor ∑ (-1)^k/(n+1+k)! is the tail of the exponential series
  for e^{-1}, starting at index n+1, with the global sign factored out.

  Key consequences:
  - For even n: D(n)/n! > 1/e (strict)
  - For odd n: D(n)/n! < 1/e (strict)
  - Error recurrence: e(n+1) = e(n) + (-1)^{n+1}/(n+1)!
  - Normalized error: (-1)^n · e(n) · (n+1)! → 1

  Main Results:
  - `error_closed_form`: D(n)/n! - 1/e = (-1)^n · errorTailSum(n+1)
  - `errorTailSum_pos`: strict positivity of the tail sum
  - `error_recurrence`: the additive recurrence for consecutive errors
  - `error_strict_pos_even`/`error_strict_neg_odd`: strict sign alternation
  - `normalized_error_tendsto`: (-1)^n · e(n) · (n+1)! → 1

  Building on DerangementsOQ03OQ01 (second-order convergence rate).

  Axioms: 0
  Sorries: 0
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open Finset Nat Real BigOperators Filter Topology

noncomputable section

namespace DerangementsOQ03OQ01OQ02

-- ============================================================
-- Foundations (self-contained definitions and basic facts)
-- ============================================================

private def altFactTerm (k : ℕ) : ℝ := (-1 : ℝ) ^ k / (k.factorial : ℝ)

private def altFactPartialSum (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), altFactTerm k

private lemma fpos (k : ℕ) : (0 : ℝ) < (k.factorial : ℝ) :=
  Nat.cast_pos.mpr k.factorial_pos

private lemma fne (k : ℕ) : (k.factorial : ℝ) ≠ 0 := (fpos k).ne'

private lemma altFactPartialSum_succ (n : ℕ) :
    altFactPartialSum (n + 1) = altFactPartialSum n + altFactTerm (n + 1) := by
  simp [altFactPartialSum, Finset.sum_range_succ]

private lemma summable_altFactTerm : Summable altFactTerm :=
  summable_pow_div_factorial (-1)

private theorem exp_neg_one_eq_tsum_alt :
    rexp (-1) = ∑' k, altFactTerm k := by
  rw [show rexp (-1) = NormedSpace.exp ℝ (-1 : ℝ) from Real.exp_eq_exp_ℝ,
      NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
  apply tsum_congr; intro k; simp only [altFactTerm, smul_eq_mul]; ring

-- ============================================================
-- Core identity: D(n) = n! · partial sum
-- ============================================================

private theorem numDerangements_eq_factorial_mul_altSum (n : ℕ) :
    (numDerangements n : ℝ) = (n.factorial : ℝ) * altFactPartialSum n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => simp [altFactPartialSum, altFactTerm]
  | 1 => simp [altFactPartialSum, altFactTerm, Finset.sum_range_succ]; ring
  | n + 2 =>
    rw [numDerangements_add_two]; push_cast
    rw [ih n (by omega), ih (n + 1) (by omega)]
    rw [altFactPartialSum_succ (n + 1), altFactPartialSum_succ n]
    simp only [altFactTerm, Nat.factorial_succ]; push_cast; ring

private theorem derangements_div_factorial (n : ℕ) :
    (numDerangements n : ℝ) / (n.factorial : ℝ) = altFactPartialSum n := by
  rw [numDerangements_eq_factorial_mul_altSum]; field_simp [fne n]

-- ============================================================
-- Tail splitting
-- ============================================================

private lemma tsum_split (N : ℕ) :
    ∑' k, altFactTerm k = ∑ k ∈ range N, altFactTerm k + ∑' k, altFactTerm (N + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hshift : Summable (fun k => altFactTerm (N + k)) :=
      summable_altFactTerm.comp_injective (fun a b h => by omega)
    have hstep : ∑' k, altFactTerm (N + k) = altFactTerm N + ∑' k, altFactTerm (N + 1 + k) := by
      rw [hshift.tsum_eq_zero_add]; simp only [Nat.add_zero]
      congr 1; apply tsum_congr; intro k; congr 1; omega
    rw [ih, hstep, Finset.sum_range_succ]; ring

-- ============================================================
-- Alternating partial sum bounds
-- ============================================================

private lemma alt_partial_sum_nonneg (m : ℕ) (N : ℕ) :
    0 ≤ ∑ k ∈ range N, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 => simp
  | 1 =>
    simp only [range_one, sum_singleton, pow_zero, zero_add]
    exact div_nonneg one_pos.le (fpos m).le
  | N' + 2 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hN' : Even N'
    · obtain ⟨j, rfl⟩ := hN'
      have hpair : 0 ≤ (-1 : ℝ) ^ (2 * j) / ((m + 2 * j).factorial : ℝ) +
          (-1 : ℝ) ^ (2 * j + 1) / ((m + (2 * j + 1)).factorial : ℝ) := by
        have h1 : (-1 : ℝ) ^ (2 * j) = 1 := by simp [pow_mul, neg_one_sq]
        have h2 : (-1 : ℝ) ^ (2 * j + 1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
        rw [h1, h2]
        have hle : ((m + 2 * j).factorial : ℝ) ≤ ((m + (2 * j + 1)).factorial : ℝ) :=
          by exact_mod_cast Nat.factorial_le (by omega)
        rw [show (1 : ℝ) / ((m + 2 * j).factorial : ℝ) + (-1) / ((m + (2 * j + 1)).factorial : ℝ) =
          (((m + (2 * j + 1)).factorial : ℝ) - ((m + 2 * j).factorial : ℝ)) /
          (((m + 2 * j).factorial : ℝ) * ((m + (2 * j + 1)).factorial : ℝ)) from by
            field_simp; ring]
        exact div_nonneg (by linarith) (mul_pos (fpos _) (fpos _)).le
      linarith [ih (2 * j) (by omega)]
    · rw [Nat.not_even_iff_odd] at hN'; obtain ⟨j, rfl⟩ := hN'
      have hpair : 0 ≤ (-1 : ℝ) ^ (2 * j) / ((m + 2 * j).factorial : ℝ) +
          (-1 : ℝ) ^ (2 * j + 1) / ((m + (2 * j + 1)).factorial : ℝ) := by
        have h1 : (-1 : ℝ) ^ (2 * j) = 1 := by simp [pow_mul, neg_one_sq]
        have h2 : (-1 : ℝ) ^ (2 * j + 1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
        rw [h1, h2]
        have hle : ((m + 2 * j).factorial : ℝ) ≤ ((m + (2 * j + 1)).factorial : ℝ) :=
          by exact_mod_cast Nat.factorial_le (by omega)
        rw [show (1 : ℝ) / ((m + 2 * j).factorial : ℝ) + (-1) / ((m + (2 * j + 1)).factorial : ℝ) =
          (((m + (2 * j + 1)).factorial : ℝ) - ((m + 2 * j).factorial : ℝ)) /
          (((m + 2 * j).factorial : ℝ) * ((m + (2 * j + 1)).factorial : ℝ)) from by
            field_simp; ring]
        exact div_nonneg (by linarith) (mul_pos (fpos _) (fpos _)).le
      have hlast : 0 ≤ (-1 : ℝ) ^ (2 * j + 2) / ((m + (2 * j + 2)).factorial : ℝ) := by
        apply div_nonneg _ (fpos _).le
        rw [show 2 * j + 2 = 2 * (j + 1) from by ring]; simp [pow_mul, neg_one_sq]
      have hss := Finset.sum_range_succ (fun i => (-1 : ℝ) ^ i / ((m + i).factorial : ℝ)) (2 * j)
      linarith [ih (2 * j) (by omega)]

private lemma alt_partial_sum_le_first (m : ℕ) (N : ℕ) :
    ∑ k ∈ range N, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) ≤ 1 / (m.factorial : ℝ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 => simp; exact div_nonneg one_pos.le (fpos m).le
  | 1 => simp only [range_one, sum_singleton, pow_zero, zero_add]; exact le_refl _
  | N' + 2 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hN' : Even N'
    · obtain ⟨j, rfl⟩ := hN'
      have hneg : (-1 : ℝ) ^ (2 * j + 1) / ((m + (2 * j + 1)).factorial : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (by simp [pow_succ, pow_mul, neg_one_sq]) (fpos _).le
      have hss := Finset.sum_range_succ (fun i => (-1 : ℝ) ^ i / ((m + i).factorial : ℝ)) (2 * j)
      linarith [ih (2 * j + 1) (by omega)]
    · rw [Nat.not_even_iff_odd] at hN'; obtain ⟨j, rfl⟩ := hN'
      have hpair : (-1 : ℝ) ^ (2 * j + 1) / ((m + (2 * j + 1)).factorial : ℝ) +
          (-1 : ℝ) ^ (2 * j + 2) / ((m + (2 * j + 2)).factorial : ℝ) ≤ 0 := by
        have h1 : (-1 : ℝ) ^ (2 * j + 1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
        have h2 : (-1 : ℝ) ^ (2 * j + 2) = 1 := by
          rw [show 2 * j + 2 = 2 * (j + 1) from by ring]; simp [pow_mul, neg_one_sq]
        rw [h1, h2]
        have hle : ((m + (2 * j + 1)).factorial : ℝ) ≤ ((m + (2 * j + 2)).factorial : ℝ) :=
          by exact_mod_cast Nat.factorial_le (by omega)
        rw [show (-1 : ℝ) / ((m + (2 * j + 1)).factorial : ℝ) + 1 / ((m + (2 * j + 2)).factorial : ℝ) =
          (((m + (2 * j + 1)).factorial : ℝ) - ((m + (2 * j + 2)).factorial : ℝ)) /
          (((m + (2 * j + 1)).factorial : ℝ) * ((m + (2 * j + 2)).factorial : ℝ)) from by
            field_simp; ring]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_pos (fpos _) (fpos _)).le
      linarith [ih (2 * j + 1) (by omega)]

-- ============================================================
-- Error Tail Sum
-- ============================================================

/-- The positive alternating tail sum: ∑' k, (-1)^k / (m+k)!.
    When m = n+1, this captures the absolute magnitude of the derangement error. -/
def errorTailSum (m : ℕ) : ℝ := ∑' k, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ))

private lemma summable_errorTailSum_terms (m : ℕ) :
    Summable (fun k => ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ))) := by
  have hbnd : Summable (fun k : ℕ => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / (k.factorial : ℝ)) :=
      (summable_pow_div_factorial 1).congr (fun k => by simp [one_pow])
    exact h1.comp_injective (fun a b h => by omega)
  exact Summable.of_norm_bounded_eventually hbnd (by
    filter_upwards with k; simp [abs_div, abs_pow, abs_neg, abs_one, Nat.cast_nonneg])

-- ============================================================
-- Bounds on the Error Tail Sum
-- ============================================================

/-- The error tail sum is non-negative. -/
lemma errorTailSum_nonneg (m : ℕ) : 0 ≤ errorTailSum m := by
  exact ge_of_tendsto (summable_errorTailSum_terms m).hasSum.tendsto_sum_nat
    (by filter_upwards with N; exact alt_partial_sum_nonneg m N)

/-- The error tail sum is at most 1/m!. -/
lemma errorTailSum_le (m : ℕ) : errorTailSum m ≤ 1 / (m.factorial : ℝ) := by
  exact le_of_tendsto (summable_errorTailSum_terms m).hasSum.tendsto_sum_nat
    (by filter_upwards with N; exact alt_partial_sum_le_first m N)

/-- Recurrence: errorTailSum m = 1/m! - errorTailSum(m+1). -/
theorem errorTailSum_recurrence (m : ℕ) :
    errorTailSum m = 1 / (m.factorial : ℝ) - errorTailSum (m + 1) := by
  -- Split: ∑' k, f k = f 0 + ∑' k, f(k+1), then show ∑' k, f(k+1) = -errorTailSum(m+1)
  have hs := summable_errorTailSum_terms m
  have hs1 := summable_errorTailSum_terms (m + 1)
  -- Step 1: Split first term
  have hfirst : errorTailSum m = 1 / (m.factorial : ℝ) +
      ∑' k, ((-1 : ℝ) ^ (k + 1) / ((m + 1 + k).factorial : ℝ)) := by
    simp only [errorTailSum]
    conv_lhs => rw [hs.tsum_eq_zero_add]
    simp only [Nat.zero_add, pow_zero, one_div]
    congr 1
    apply tsum_congr; intro k
    congr 2; omega
  -- Step 2: The tail is -errorTailSum(m+1)
  have hneg : ∑' k, ((-1 : ℝ) ^ (k + 1) / ((m + 1 + k).factorial : ℝ)) =
      -errorTailSum (m + 1) := by
    simp only [errorTailSum, ← tsum_neg (summable := hs1)]
    apply tsum_congr; intro k
    rw [pow_succ]; ring
  linarith

/-- The error tail sum is strictly positive.
    For m ≥ 1: direct from 1/(m+1)! < 1/m!.
    For m = 0: reduce to errorTailSum 2 > 0 via the double recurrence. -/
theorem errorTailSum_pos (m : ℕ) : 0 < errorTailSum m := by
  -- Prove for m ≥ 1
  suffices hmain : ∀ m, 0 < m → 0 < errorTailSum m by
    match m with
    | 0 =>
      -- errorTailSum 0 = 1/0! - errorTailSum 1 = 1 - (1 - errorTailSum 2) = errorTailSum 2
      rw [errorTailSum_recurrence 0, errorTailSum_recurrence 1]
      simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
      linarith [hmain 2 (by omega)]
    | m + 1 => exact hmain (m + 1) (by omega)
  intro m hm
  rw [errorTailSum_recurrence m]
  have h1 : errorTailSum (m + 1) ≤ 1 / ((m + 1).factorial : ℝ) := errorTailSum_le (m + 1)
  -- 1/(m+1)! < 1/m! since m ≥ 1 implies (m+1)! > m!
  have h2 : (1 : ℝ) / ((m + 1).factorial : ℝ) < 1 / (m.factorial : ℝ) := by
    apply one_div_lt_one_div_of_lt (fpos m)
    push_cast
    exact_mod_cast show m.factorial < (m + 1).factorial from by
      rw [Nat.factorial_succ]; nlinarith [Nat.factorial_pos m]
  linarith

/-- Tight lower bound: errorTailSum m ≥ 1/m! - 1/(m+1)!. -/
theorem errorTailSum_ge (m : ℕ) :
    1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) ≤ errorTailSum m := by
  rw [errorTailSum_recurrence m]
  linarith [errorTailSum_le (m + 1)]

-- ============================================================
-- Factoring Identity
-- ============================================================

/-- The tail of altFactTerm equals (-1)^m times the error tail sum. -/
private theorem tail_eq_signed (m : ℕ) :
    ∑' k, altFactTerm (m + k) = (-1 : ℝ) ^ m * errorTailSum m := by
  simp only [errorTailSum, altFactTerm]
  simp_rw [show ∀ k, (-1 : ℝ) ^ (m + k) / ((m + k).factorial : ℝ) =
    (-1 : ℝ) ^ m * ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) from
    fun k => by rw [pow_add]; ring]
  exact tsum_mul_left

-- ============================================================
-- Main Closed-Form Identity
-- ============================================================

/-- **Closed-Form Error Identity**: The derangement error D(n)/n! - 1/e equals
    (-1)^n times the strictly positive alternating tail sum.

    D(n)/n! - 1/e = (-1)^n · ∑_{k=0}^∞ (-1)^k / (n+1+k)! -/
theorem error_closed_form (n : ℕ) :
    (numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) =
    (-1 : ℝ) ^ n * errorTailSum (n + 1) := by
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt]
  have hsplit := tsum_split (n + 1)
  have hcancel : altFactPartialSum n - ∑' k, altFactTerm k =
      -(∑' k, altFactTerm (n + 1 + k)) := by
    rw [hsplit]; ring
  rw [hcancel, tail_eq_signed (n + 1)]
  rw [show (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1) from pow_succ (-1) n]
  ring

-- ============================================================
-- Error Recurrence
-- ============================================================

/-- **Error Recurrence**: The derangement error at n+1 equals the error at n
    plus (-1)^{n+1}/(n+1)!. Each step adds one more term of the exponential series. -/
theorem error_recurrence (n : ℕ) :
    (numDerangements (n + 1) : ℝ) / ((n + 1).factorial : ℝ) - rexp (-1) =
    ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) +
    (-1 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [derangements_div_factorial, derangements_div_factorial, altFactPartialSum_succ]
  simp only [altFactTerm]; ring

-- ============================================================
-- Strict Sign Alternation
-- ============================================================

/-- For even n, D(n)/n! strictly exceeds 1/e. -/
theorem error_strict_pos_even (n : ℕ) :
    rexp (-1) < (numDerangements (2 * n) : ℝ) / ((2 * n).factorial : ℝ) := by
  have h := error_closed_form (2 * n)
  rw [show (-1 : ℝ) ^ (2 * n) = 1 from by simp [pow_mul]] at h
  linarith [errorTailSum_pos (2 * n + 1)]

/-- For odd n, D(n)/n! is strictly less than 1/e. -/
theorem error_strict_neg_odd (n : ℕ) :
    (numDerangements (2 * n + 1) : ℝ) / ((2 * n + 1).factorial : ℝ) < rexp (-1) := by
  have h := error_closed_form (2 * n + 1)
  rw [show (-1 : ℝ) ^ (2 * n + 1) = -1 from by simp [pow_succ, pow_mul]] at h
  linarith [errorTailSum_pos (2 * n + 2)]

-- ============================================================
-- Normalized Error Limit
-- ============================================================

/-- **Asymptotic Precision**: The normalized error (-1)^n · (D(n)/n! - 1/e) · (n+1)!
    converges to 1 as n → ∞. This shows the error is asymptotically (-1)^n / (n+1)!. -/
theorem normalized_error_tendsto :
    Tendsto (fun n => (-1 : ℝ) ^ n *
      ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) *
      ((n + 1).factorial : ℝ))
    atTop (nhds 1) := by
  -- Simplify to errorTailSum(n+1) * (n+1)!
  have hsimp : ∀ n, (-1 : ℝ) ^ n *
      ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) *
      ((n + 1).factorial : ℝ) =
      errorTailSum (n + 1) * ((n + 1).factorial : ℝ) := by
    intro n; rw [error_closed_form]
    have : (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * errorTailSum (n + 1)) = errorTailSum (n + 1) := by
      rw [← mul_assoc, ← pow_add, show n + n = 2 * n from by ring]; simp [pow_mul]
    linarith
  simp_rw [hsimp]
  -- Squeeze between 1 - 1/(n+2) and 1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℝ) / (↑N + 2) < ε := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
    exact ⟨M, by
      rw [div_lt_iff (show (0 : ℝ) < ↑M + 2 by positivity)]
      calc (1 : ℝ) < ε * ↑M := by rwa [div_lt_iff hε] at hM
        _ ≤ ε * (↑M + 2) := by linarith [hε]⟩
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq]
    have hle := errorTailSum_le (n + 1)
    have hge := errorTailSum_ge (n + 1)
    have hfp := fpos (n + 1)
    -- Upper: errorTailSum(n+1) · (n+1)! ≤ 1
    have hupper : errorTailSum (n + 1) * ((n + 1).factorial : ℝ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hle hfp.le
      rwa [div_mul_cancel₀ _ (fne (n + 1))] at this
    -- Lower: 1 - 1/(n+2) ≤ errorTailSum(n+1) · (n+1)!
    have hlower : 1 - 1 / (↑n + 2 : ℝ) ≤
        errorTailSum (n + 1) * ((n + 1).factorial : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hge hfp.le
      rwa [show (1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ)) *
          ((n + 1).factorial : ℝ) = 1 - 1 / (↑n + 2 : ℝ) from by
        rw [sub_mul, div_mul_cancel₀ _ (fne (n + 1))]
        congr 1
        rw [show (n + 2).factorial = (n + 1).factorial * (n + 2) from by
          rw [Nat.factorial_succ]; ring]
        push_cast; field_simp] at hmul
    -- Combine: |expr - 1| ≤ 1/(n+2) ≤ 1/(N+2) < ε
    have habs : |errorTailSum (n + 1) * ((n + 1).factorial : ℝ) - 1| ≤
        1 / (↑n + 2 : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    calc |errorTailSum (n + 1) * ((n + 1).factorial : ℝ) - 1|
        ≤ 1 / (↑n + 2 : ℝ) := habs
      _ ≤ 1 / (↑N + 2 : ℝ) := by
          apply div_le_div_of_nonneg_left one_pos (show (0 : ℝ) < ↑N + 2 by positivity)
          push_cast; exact_mod_cast show N + 2 ≤ n + 2 by omega
      _ < ε := hN⟩

-- ============================================================
-- Concrete Values
-- ============================================================

/-- D(0)/0! - 1/e = 1 - 1/e > 0. -/
theorem error_n0_pos : rexp (-1) < (numDerangements 0 : ℝ) / (Nat.factorial 0 : ℝ) :=
  error_strict_pos_even 0

/-- D(1)/1! - 1/e = 0 - 1/e < 0. -/
theorem error_n1_neg : (numDerangements 1 : ℝ) / (Nat.factorial 1 : ℝ) < rexp (-1) :=
  error_strict_neg_odd 0

end DerangementsOQ03OQ01OQ02

end
