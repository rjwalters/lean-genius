/-
  Derangements: sign and sharp decay of the asymptotic gap  n!/e − D(n)
  Open Question: derangements-convergence-oq-03-oq-01-oq-02

  The grandparent entry (`DerangementsConvergence`) proved the convergence rate
  `|D(n)/n! − e⁻¹| ≤ 1/(n+1)!`, and the parent (`...OQ03OQ01`) packaged the
  resulting nearest-integer forms `D(n) = round(n!/e)` from the *absolute* bound
  `|D(n) − n!/e| < 1/2`.

  Both of those discard the **sign** of the error.  This entry recovers it.
  Writing the signed gap

      G(n)  :=  n!·e⁻¹ − D(n),

  we show that `G(n)` is exactly `n!` times the alternating tail
  `∑_{k≥n+1} (−1)ᵏ/k!`, hence

    * **Sign (alternation).**  `G(n)` has the sign of `(−1)^{n+1}`:
        - `n` even  ⟹  `D(n) > n!/e`   (`G(n) < 0`),
        - `n` odd   ⟹  `D(n) < n!/e`   (`G(n) > 0`).
      Equivalently `0 < (−1)^{n+1}·G(n)` for every `n`.  So the integers `D(n)`
      straddle the real number `n!/e`, jumping above and below it alternately.

    * **Sharp two-sided decay.**  For every `n`,
        `1/(n+2) ≤ |G(n)| ≤ 1/(n+1)`.
      The upper bound `1/(n+1)` is the grandparent rate scaled by `n!`; the lower
      bound `1/(n+2)` is new and shows the gap does **not** decay faster than the
      leading tail term — `|G(n)|` is squeezed between two consecutive unit
      fractions, with `|G(n)|·(n+1) → 1`.

  ## Main Results

  `signed_gap_eq_factorial_mul_tail` : G(n) = n! · ∑'ₖ altFactTerm (n+1+k).
  `gap_sign`                         : 0 < (−1)^{n+1} · G(n).
  `gap_neg_of_even` / `gap_pos_of_odd` : the even/odd specialisations.
  `abs_gap_le`                       : |G(n)| ≤ 1/(n+1).
  `abs_gap_ge`                       : 1/(n+2) ≤ |G(n)|.
  `abs_gap_bounds`                   : 1/(n+2) ≤ |G(n)| ≤ 1/(n+1).

  ## Proof Strategy

  Everything rests on the *signed* alternating-tail series
      S(m) := ∑'ₖ (−1)ᵏ/(m+k)!     (here m = n+1).
  The grandparent's helper lemmas `alt_partial_sum_nonneg`/`alt_partial_sum_le_first`
  already give `0 ≤ S(m) ≤ 1/m!` (partial sums sandwiched, then `le_of_tendsto`).
  Splitting off the first two terms,
      S(m) = 1/m! − 1/(m+1)! + S(m+2),    S(m+2) ≥ 0,
  upgrades the lower bound to the *sharp* `1/m! − 1/(m+1)! ≤ S(m)` (> 0).
  Multiplying the sandwich `1/m! − 1/(m+1)! ≤ S(m) ≤ 1/m!` by `n!` and using
  `n!/(n+1)! = 1/(n+1)`, `n!/(n+2)! = 1/((n+1)(n+2))` collapses the endpoints to
  the consecutive unit fractions `1/(n+2)` and `1/(n+1)`.  The factor `(−1)^{n+1}`
  pulled out of the tail (`altFactTerm (m+k) = (−1)ᵐ·(−1)ᵏ/(m+k)!`) supplies the
  sign.

  This is self-contained on top of the grandparent `DerangementsConvergence`; it
  re-uses that file's alternating-series lemmas rather than re-proving them.
-/

import Mathlib
import Proofs.DerangementsConvergence

open Finset Nat Real BigOperators Filter Topology

noncomputable section

namespace DerangementsConvergenceOQ03OQ01OQ02

/-- The signed alternating term `(−1)ᵏ/(m+k)!`.  This is `altFactTerm (m+k)` with
the global sign `(−1)ᵐ` factored out, so it is termwise nonnegative-leading. -/
def cTerm (m k : ℕ) : ℝ := (-1 : ℝ) ^ k / ((m + k).factorial : ℝ)

lemma cTerm_zero (m : ℕ) : cTerm m 0 = 1 / (m.factorial : ℝ) := by
  simp [cTerm]

lemma cTerm_one (m : ℕ) : cTerm m 1 = -(1 / ((m + 1).factorial : ℝ)) := by
  rw [cTerm, pow_one]; ring

/-- `cTerm` shifted by two indices is `cTerm` of the shifted base: the `(−1)²`
sign cancels. -/
lemma cTerm_add_two (m k : ℕ) : cTerm m (k + 2) = cTerm (m + 2) k := by
  unfold cTerm
  rw [show m + (k + 2) = (m + 2) + k by ring, show (-1 : ℝ) ^ (k + 2) = (-1) ^ k by
    rw [pow_add]; simp]

/-- The signed alternating tail series `S(m) = ∑'ₖ (−1)ᵏ/(m+k)!` is summable.
(Same comparison as the grandparent's `summable_altFactTerm`, reindexed.) -/
lemma summable_cTerm (m : ℕ) : Summable (cTerm m) := by
  have hbnd_summable : Summable (fun k => (1 : ℝ) / ((m + k).factorial : ℝ)) := by
    have h1 : Summable (fun (k : ℕ) => (1 : ℝ) / (k.factorial : ℝ)) := by
      simpa only [one_pow] using summable_pow_div_factorial (1 : ℝ)
    exact h1.comp_injective (fun ⦃a b⦄ (h : m + a = m + b) => by omega)
  refine Summable.of_norm_bounded_eventually hbnd_summable ?_
  filter_upwards with k
  apply le_of_eq
  simp only [cTerm, norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]

/-- Lower envelope: `0 ≤ S(m)`.  Lifted from the grandparent's
`alt_partial_sum_nonneg` via `le_of_tendsto`. -/
lemma tsum_cTerm_nonneg (m : ℕ) : 0 ≤ ∑' k, cTerm m k := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    ((summable_cTerm m).hasSum.tendsto_sum_nat)
  filter_upwards with N
  exact alt_partial_sum_nonneg m N

/-- Upper envelope: `S(m) ≤ 1/m!`.  Lifted from the grandparent's
`alt_partial_sum_le_first` via `le_of_tendsto`. -/
lemma tsum_cTerm_le_first (m : ℕ) : ∑' k, cTerm m k ≤ 1 / (m.factorial : ℝ) := by
  apply le_of_tendsto ((summable_cTerm m).hasSum.tendsto_sum_nat)
  filter_upwards with N
  exact alt_partial_sum_le_first m N

/-- **Sharp lower envelope.**  Peeling off the first two terms,
`S(m) = 1/m! − 1/(m+1)! + S(m+2)` with `S(m+2) ≥ 0`, gives
`1/m! − 1/(m+1)! ≤ S(m)`. -/
lemma tsum_cTerm_ge_first_two (m : ℕ) :
    1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) ≤ ∑' k, cTerm m k := by
  have hsplit := (summable_cTerm m).sum_add_tsum_nat_add 2
  -- hsplit : (∑ k ∈ range 2, cTerm m k) + ∑' k, cTerm m (2 + k) = ∑' k, cTerm m k
  have hhead : ∑ k ∈ range 2, cTerm m k =
      1 / (m.factorial : ℝ) - 1 / ((m + 1).factorial : ℝ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, cTerm_zero, cTerm_one]; ring
  have htail_nonneg : 0 ≤ ∑' k, cTerm m (k + 2) := by
    have hcongr : ∑' k, cTerm m (k + 2) = ∑' k, cTerm (m + 2) k :=
      tsum_congr fun k => cTerm_add_two m k
    rw [hcongr]
    exact tsum_cTerm_nonneg (m + 2)
  rw [hhead] at hsplit
  linarith [hsplit, htail_nonneg]
end DerangementsConvergenceOQ03OQ01OQ02

namespace DerangementsConvergenceOQ03OQ01OQ02

/-- The grandparent's alternating tail, with the global sign factored out:
`∑'ₖ altFactTerm (n+1+k) = (−1)^{n+1} · S(n+1)`. -/
lemma tail_eq_sign_mul_cTerm (n : ℕ) :
    ∑' k, altFactTerm (n + 1 + k) = (-1 : ℝ) ^ (n + 1) * ∑' k, cTerm (n + 1) k := by
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [altFactTerm, cTerm]
  rw [show n + 1 + k = (n + 1) + k from rfl, pow_add, mul_div_assoc]

/-- **Signed gap formula.**  The gap `G(n) = n!·e⁻¹ − D(n)` equals `n!` times the
alternating tail `∑_{k≥n+1} (−1)ᵏ/k!`.  This is the exact (unsigned-bound-free)
statement of the error. -/
theorem signed_gap_eq_factorial_mul_tail (n : ℕ) :
    (n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)
      = (n.factorial : ℝ) * ∑' k, altFactTerm (n + 1 + k) := by
  rw [numDerangements_eq_factorial_mul_altSum,
    exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  ring

/-- The gap written as `(−1)^{n+1} · n! · S(n+1)` with `S(n+1) ≥ 0`. -/
theorem signed_gap_eq_sign_form (n : ℕ) :
    (n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)
      = (-1 : ℝ) ^ (n + 1) * ((n.factorial : ℝ) * ∑' k, cTerm (n + 1) k) := by
  rw [signed_gap_eq_factorial_mul_tail, tail_eq_sign_mul_cTerm]; ring

/-- `n!/(m+1)! < n!/m!` packaged: the sharp lower envelope `S(m)` is strictly
positive, since `1/m! − 1/(m+1)! > 0`. -/
lemma tsum_cTerm_pos (n : ℕ) : 0 < ∑' k, cTerm (n + 1) k := by
  have hlow := tsum_cTerm_ge_first_two (n + 1)
  have hstrict : 0 < 1 / (((n + 1).factorial : ℝ)) - 1 / (((n + 1 + 1).factorial : ℝ)) := by
    have h1 : (((n + 1).factorial : ℝ)) < (((n + 1 + 1).factorial : ℝ)) := by
      have hnat : (n + 1).factorial < (n + 1 + 1).factorial := by
        rw [Nat.factorial_lt (by omega : 0 < n + 1)]; omega
      exact_mod_cast hnat
    have hp1 := factorial_cast_pos' (n + 1)
    have hp2 := factorial_cast_pos' (n + 1 + 1)
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hp1 h1
  linarith

/-- **Sign of the gap (alternation).**  For every `n`,
`0 < (−1)^{n+1} · (n!·e⁻¹ − D(n))`.  Thus `D(n)` lies strictly on the side of
`n!/e` dictated by the parity of `n`: the derangement counts straddle `n!/e`. -/
theorem gap_sign (n : ℕ) :
    0 < (-1 : ℝ) ^ (n + 1) * ((n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)) := by
  rw [signed_gap_eq_sign_form]
  have hsq : (-1 : ℝ) ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) *
      ((n.factorial : ℝ) * ∑' k, cTerm (n + 1) k))
      = (n.factorial : ℝ) * ∑' k, cTerm (n + 1) k := by
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [hsq]
  exact mul_pos (factorial_cast_pos' n) (tsum_cTerm_pos n)

/-- For even `n`, the derangement count exceeds `n!/e`:  `D(n) > n!/e`. -/
theorem gap_neg_of_even (n : ℕ) (hn : Even n) :
    (n.factorial : ℝ) * rexp (-1) < (numDerangements n : ℝ) := by
  have h := gap_sign n
  have hsign : (-1 : ℝ) ^ (n + 1) = -1 := by
    rw [pow_succ, hn.neg_one_pow]; ring
  rw [hsign] at h
  nlinarith [h]

/-- For odd `n`, the derangement count is below `n!/e`:  `D(n) < n!/e`. -/
theorem gap_pos_of_odd (n : ℕ) (hn : Odd n) :
    (numDerangements n : ℝ) < (n.factorial : ℝ) * rexp (-1) := by
  have h := gap_sign n
  have hsign : (-1 : ℝ) ^ (n + 1) = 1 := by
    rw [pow_succ, hn.neg_one_pow]; ring
  rw [hsign] at h
  nlinarith [h]

/-- Helper: `n!/(n+1)! = 1/(n+1)` as reals. -/
lemma factorial_ratio_succ (n : ℕ) :
    (n.factorial : ℝ) / ((n + 1).factorial : ℝ) = 1 / (n + 1 : ℝ) := by
  rw [Nat.factorial_succ]; push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := factorial_cast_ne_zero' n
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Helper: `n!/(n+2)! = 1/((n+1)(n+2))` as reals. -/
lemma factorial_ratio_succ_succ (n : ℕ) :
    (n.factorial : ℝ) / ((n + 2).factorial : ℝ) = 1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  rw [show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The absolute gap equals `n! · S(n+1)`. -/
lemma abs_gap_eq (n : ℕ) :
    |(n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)|
      = (n.factorial : ℝ) * ∑' k, cTerm (n + 1) k := by
  rw [signed_gap_eq_sign_form, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg]
  exact mul_nonneg (factorial_cast_pos' n).le (tsum_cTerm_nonneg (n + 1))

/-- **Upper decay bound.**  `|n!·e⁻¹ − D(n)| ≤ 1/(n+1)` (the grandparent rate,
scaled by `n!`). -/
theorem abs_gap_le (n : ℕ) :
    |(n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)| ≤ 1 / (n + 1 : ℝ) := by
  rw [abs_gap_eq]
  calc (n.factorial : ℝ) * ∑' k, cTerm (n + 1) k
      ≤ (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (tsum_cTerm_le_first (n + 1)) (factorial_cast_pos' n).le
    _ = (n.factorial : ℝ) / ((n + 1).factorial : ℝ) := by rw [mul_one_div]
    _ = 1 / (n + 1 : ℝ) := factorial_ratio_succ n

/-- **Sharp lower decay bound.**  `1/(n+2) ≤ |n!·e⁻¹ − D(n)|`.  This is the new
content: the gap does not decay faster than the leading tail term. -/
theorem abs_gap_ge (n : ℕ) :
    1 / (n + 2 : ℝ) ≤ |(n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)| := by
  rw [abs_gap_eq]
  have hkey : (n.factorial : ℝ) *
      (1 / (((n + 1).factorial : ℝ)) - 1 / (((n + 1 + 1).factorial : ℝ)))
      = 1 / (n + 2 : ℝ) := by
    rw [mul_sub, mul_one_div, mul_one_div]
    rw [show n + 1 + 1 = n + 2 by ring, factorial_ratio_succ n, factorial_ratio_succ_succ n]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  calc 1 / (n + 2 : ℝ)
      = (n.factorial : ℝ) *
          (1 / (((n + 1).factorial : ℝ)) - 1 / (((n + 1 + 1).factorial : ℝ))) := hkey.symm
    _ ≤ (n.factorial : ℝ) * ∑' k, cTerm (n + 1) k :=
        mul_le_mul_of_nonneg_left (tsum_cTerm_ge_first_two (n + 1)) (factorial_cast_pos' n).le

/-- **Sharp two-sided decay.**  The gap is squeezed between consecutive unit
fractions:  `1/(n+2) ≤ |n!·e⁻¹ − D(n)| ≤ 1/(n+1)`. -/
theorem abs_gap_bounds (n : ℕ) :
    1 / (n + 2 : ℝ) ≤ |(n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)|
      ∧ |(n.factorial : ℝ) * rexp (-1) - (numDerangements n : ℝ)| ≤ 1 / (n + 1 : ℝ) :=
  ⟨abs_gap_ge n, abs_gap_le n⟩

end DerangementsConvergenceOQ03OQ01OQ02
