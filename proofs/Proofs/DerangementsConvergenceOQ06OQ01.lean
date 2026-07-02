/-
  Derangements: an effective TWO-SIDED sandwich on the error |D(n) − n!·e⁻¹|
  Open question: derangements-convergence-oq-06-oq-01

  ## Context

  The parent chain proves the *one-sided* rate bound
    |D(n)/n! − e⁻¹| ≤ 1/(n+1)!          (`derangements_convergence_rate`)
  and, at integer scale, |D(n) − n!·e⁻¹| ≤ 1/(n+1), which is exactly what pins
  down the rounding identity D(n) = round(n!/e).

  ## What this file adds

  We complement the upper bound with a matching LOWER bound, giving an effective
  two-sided sandwich. The error is exactly the alternating factorial tail
    T(m) := ∑' k, (−1)ᵏ/(m+k)!,     with   |D(n)/n! − e⁻¹| = T(n+1).
  The single clean fact driving everything is the tail recurrence
    T(m) = 1/m! − T(m+1),
  obtained by peeling off the k = 0 term. Combined with the parent's envelope
  0 ≤ T(m) ≤ 1/m! (from `alt_partial_sum_nonneg` / `alt_partial_sum_le_first`),
  the recurrence yields
    1/m! − 1/(m+1)! ≤ T(m) ≤ 1/m!.
  Specialising m = n+1 and multiplying by n! gives the headline sandwich
    1/(n+2) ≤ |D(n) − n!·e⁻¹| ≤ 1/(n+1),      for all n,
  since n!·(1/(n+1)! − 1/(n+2)!) = 1/(n+1) − 1/((n+1)(n+2)) = 1/(n+2).

  This shows the parent's upper bound 1/(n+1) is essentially sharp: the true
  error stays trapped in the band [1/(n+2), 1/(n+1)].

  ## Main results
  - `tailFrom`                     : the alternating factorial tail T(m)
  - `tailFrom_succ`                : T(m) = 1/m! − T(m+1)                (recurrence)
  - `tailFrom_le` / `tailFrom_nonneg` / `tailFrom_ge` : the two-sided envelope on T
  - `abs_err_eq_tailFrom`          : |D(n)/n! − e⁻¹| = T(n+1)
  - `abs_err_le` / `abs_err_ge`    : two-sided bound at the /n! scale
  - `abs_derangements_sub_le`      : |D(n) − n!·e⁻¹| ≤ 1/(n+1)
  - `abs_derangements_sub_ge`      : |D(n) − n!·e⁻¹| ≥ 1/(n+2)
  - `derangements_two_sided_sandwich` : the sharp band, both bounds at once
-/
import Mathlib
import Proofs.DerangementsConvergence

open Finset Nat Real BigOperators Filter Topology

namespace DerangementsConvergenceOQ06OQ01

/-- The alternating factorial tail `T(m) = ∑' k, (−1)ᵏ/(m+k)!`. This is exactly
    the quantity controlling the derangement error (see `abs_err_eq_tailFrom`). -/
noncomputable def tailFrom (m : ℕ) : ℝ := ∑' k, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ))

/-- The tail summand is summable (dominated by `1/(m+k)!`). Mirrors the local
    `hc_summable` inside the parent's `alternating_tail_bound`. -/
lemma summable_altTail (m : ℕ) :
    Summable (fun k => (-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  have hbnd : Summable (fun k => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
    have h1 : Summable (fun (k : ℕ) => (1 : ℝ) / (k.factorial : ℝ)) := by
      simpa only [one_pow] using summable_pow_div_factorial (1 : ℝ)
    exact h1.comp_injective (fun ⦃a b⦄ (h : m + a = m + b) => by omega)
  refine Summable.of_norm_bounded_eventually hbnd ?_
  filter_upwards with k
  apply le_of_eq
  simp only [norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]

/-- `0 ≤ T(m)`. -/
lemma tailFrom_nonneg (m : ℕ) : 0 ≤ tailFrom m := by
  unfold tailFrom
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    ((summable_altTail m).hasSum.tendsto_sum_nat)
  filter_upwards with N
  exact alt_partial_sum_nonneg m N

/-- `T(m) ≤ 1/m!`. -/
lemma tailFrom_le (m : ℕ) : tailFrom m ≤ 1 / (m.factorial : ℝ) := by
  unfold tailFrom
  apply le_of_tendsto ((summable_altTail m).hasSum.tendsto_sum_nat)
  filter_upwards with N
  exact alt_partial_sum_le_first m N

/-- The tail recurrence: peeling off the `k = 0` term gives `T(m) = 1/m! − T(m+1)`. -/
lemma tailFrom_succ (m : ℕ) :
    tailFrom m = 1 / (m.factorial : ℝ) - tailFrom (m + 1) := by
  unfold tailFrom
  rw [(summable_altTail m).tsum_eq_zero_add]
  have etail : (∑' b : ℕ, (-1 : ℝ) ^ (b + 1) / ((m + (b + 1)).factorial : ℝ))
      = - ∑' b : ℕ, (-1 : ℝ) ^ b / (((m + 1) + b).factorial : ℝ) := by
    rw [← tsum_neg]
    refine tsum_congr (fun b => ?_)
    have hfac : m + (b + 1) = (m + 1) + b := by omega
    rw [hfac, pow_succ]; ring
  rw [etail]
  simp only [pow_zero, Nat.add_zero, one_div]
  ring

/-- Two-sided envelope, lower half: `1/m! − 1/(m+1)! ≤ T(m)`. -/
lemma tailFrom_ge (m : ℕ) :
    1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) ≤ tailFrom m := by
  rw [tailFrom_succ m]
  have := tailFrom_le (m + 1)
  linarith

/-- The derangement error equals the tail: `|D(n)/n! − e⁻¹| = T(n+1)`. -/
lemma abs_err_eq_tailFrom (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| = tailFrom (n + 1) := by
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  have h1 : altFactPartialSum n - (altFactPartialSum n + ∑' k, altFactTerm (n + 1 + k))
      = -(∑' k, altFactTerm (n + 1 + k)) := by ring
  rw [h1, abs_neg]
  set m := n + 1 with hm
  have hfactor : ∀ k, altFactTerm (m + k)
      = (-1 : ℝ) ^ m * ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
    intro k; simp [altFactTerm, pow_add, mul_div_assoc]
  have h2 : (∑' k, altFactTerm (m + k)) = (-1 : ℝ) ^ m * tailFrom m := by
    unfold tailFrom
    rw [← tsum_mul_left]
    exact tsum_congr hfactor
  rw [h2, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (tailFrom_nonneg _)]

/-- Upper bound at the `/n!` scale (recovers the parent's rate). -/
theorem abs_err_le (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| ≤ 1 / ((n + 1).factorial : ℝ) := by
  rw [abs_err_eq_tailFrom]; exact tailFrom_le (n + 1)

/-- Lower bound at the `/n!` scale. -/
theorem abs_err_ge (n : ℕ) :
    1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ)
      ≤ |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| := by
  rw [abs_err_eq_tailFrom]
  have h := tailFrom_ge (n + 1)
  have he : (n + 1 + 1) = (n + 2) := by omega
  rw [he] at h
  exact h

/-- Rewrite the integer-scale error as `n!` times the `/n!`-scale error. -/
lemma abs_int_eq_factorial_mul (n : ℕ) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)|
      = (n.factorial : ℝ) * |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| := by
  have hn : (0 : ℝ) < (n.factorial : ℝ) := factorial_cast_pos' n
  have hrw : (numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)
      = (n.factorial : ℝ) * ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos hn]

/-- Integer-scale upper bound: `|D(n) − n!·e⁻¹| ≤ 1/(n+1)`. -/
theorem abs_derangements_sub_le (n : ℕ) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| ≤ 1 / (n + 1 : ℝ) := by
  rw [abs_int_eq_factorial_mul]
  have hle := abs_err_le n
  have hn : (0 : ℝ) < (n.factorial : ℝ) := factorial_cast_pos' n
  calc (n.factorial : ℝ) * |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)|
      ≤ (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hle hn.le
    _ = 1 / (n + 1 : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; field_simp

/-- Integer-scale lower bound: `|D(n) − n!·e⁻¹| ≥ 1/(n+2)`. -/
theorem abs_derangements_sub_ge (n : ℕ) :
    1 / (n + 2 : ℝ) ≤ |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| := by
  rw [abs_int_eq_factorial_mul]
  have hge := abs_err_ge n
  have hn : (0 : ℝ) < (n.factorial : ℝ) := factorial_cast_pos' n
  calc 1 / (n + 2 : ℝ)
      = (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ)) := by
        rw [show (n + 2).factorial = (n + 2) * (n + 1).factorial from by
              rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ],
            show (n + 1).factorial = (n + 1) * n.factorial from Nat.factorial_succ n]
        push_cast
        have h1 : (n.factorial : ℝ) ≠ 0 := factorial_cast_ne_zero' n
        have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
        have h3 : (n : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ (n.factorial : ℝ) * |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| := by
        apply mul_le_mul_of_nonneg_left hge hn.le

/-- The sharp two-sided sandwich: the derangement error is trapped in
    `[1/(n+2), 1/(n+1)]` for every `n`. -/
theorem derangements_two_sided_sandwich (n : ℕ) :
    1 / (n + 2 : ℝ) ≤ |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)|
    ∧ |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| ≤ 1 / (n + 1 : ℝ) :=
  ⟨abs_derangements_sub_ge n, abs_derangements_sub_le n⟩

end DerangementsConvergenceOQ06OQ01
