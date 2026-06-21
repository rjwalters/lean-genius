/-
# Derangements: the sign of the error and sharp two-sided bracketing of 1/e

Open Question: derangements-convergence-oq-02

The parent file `DerangementsConvergence.lean` proves the *magnitude* of the
approximation error:
  |D(n)/n! - e⁻¹| ≤ 1/(n+1)!.

This file pins down the *sign* of that error and the resulting sharp two-sided
bracketing of 1/e by consecutive derangement ratios.  Writing
  a(n) = D(n)/n! = ∑_{k=0}^n (-1)^k/k!   (the n-th partial sum of e⁻¹),
the alternating structure forces:

  * even partial sums lie strictly **above** e⁻¹,
  * odd partial sums lie strictly **below** e⁻¹,

so 1/e is *bracketed*:  a(2k+1) < e⁻¹ < a(2k).  The even-indexed ratios form a
strictly decreasing sequence and the odd-indexed ratios a strictly increasing
one, both converging to e⁻¹; these are *nested intervals* of exact width
a(2k) - a(2k+1) = 1/(2k+1)! shrinking to 0.

This is strictly more information than the parent's one-sided rate bound: it
gives the exact sign of D(n)/n! - e⁻¹ for every n, not merely its size.

## Main Results

- `ratio_even_gt`     : e⁻¹ < a(2k)                          (even ratios above)
- `ratio_odd_lt`      : a(2k+1) < e⁻¹                         (odd ratios below)
- `numDerangements_bracket` : a(2k+1) < e⁻¹ < a(2k)          (two-sided bracket)
- `aSeq_error_sign`   : 0 < (-1)^n · (a(n) - e⁻¹)            (exact sign, unified)
- `numDerangements_error_sign` : same, in D(n)/n! form
- `consecutive_error_opposite` : (a(n)-e⁻¹)·(a(n+1)-e⁻¹) < 0 (signs alternate)
- `nested_interval_width` : a(2k) - a(2k+1) = 1/(2k+1)!      (exact nesting width)
- `numDerangements_gt_of_even` : n!·e⁻¹ < D(n)   for even n
- `numDerangements_lt_of_odd`  : D(n) < n!·e⁻¹   for odd  n

All results are fully machine-checked: no `sorry`, no `axiom` declarations, and
no structure-encoded assumptions (only Lean/Mathlib's foundational
`propext` / `Classical.choice` / `Quot.sound`).

## References

- Montmort (1708), Euler (1751) — derangement numbers
- Leibniz alternating series estimation (sign of the remainder)
-/

import Proofs.DerangementsConvergence
import Mathlib.Tactic

open Nat Real Filter Topology

noncomputable section

namespace DerangementsConvergenceOQ02

/- ## §1. Sign of the alternating terms -/

lemma altFactTerm_of_even {m : ℕ} (h : Even m) :
    altFactTerm m = 1 / (m.factorial : ℝ) := by
  simp only [altFactTerm]
  rw [h.neg_one_pow]

lemma altFactTerm_of_odd {m : ℕ} (h : Odd m) :
    altFactTerm m = -(1 / (m.factorial : ℝ)) := by
  simp only [altFactTerm]
  rw [h.neg_one_pow]
  ring

/- ## §2. The two-step recurrence and strict monotonicity of subsequences -/

/-- Stepping the partial sum by two adds two consecutive alternating terms. -/
lemma aSeq_add_two (n : ℕ) :
    altFactPartialSum (n + 2) =
      altFactPartialSum n + altFactTerm (n + 1) + altFactTerm (n + 2) := by
  have h1 := altFactPartialSum_succ (n + 1)
  rw [altFactPartialSum_succ n] at h1
  exact h1

/-- The even-indexed ratios strictly decrease: a(2k+2) < a(2k). -/
lemma aSeq_even_step (k : ℕ) :
    altFactPartialSum (2 * k + 2) < altFactPartialSum (2 * k) := by
  rw [aSeq_add_two]
  rw [altFactTerm_of_odd (show Odd (2 * k + 1) from ⟨k, by ring⟩),
      altFactTerm_of_even (show Even (2 * k + 2) from ⟨k + 1, by ring⟩)]
  have hfac : ((2 * k + 1).factorial : ℝ) < ((2 * k + 2).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_lt (by omega)).mpr (by omega)
  have h1 : (1 : ℝ) / ((2 * k + 2).factorial : ℝ) < 1 / ((2 * k + 1).factorial : ℝ) :=
    one_div_lt_one_div_of_lt (factorial_cast_pos' (2 * k + 1)) hfac
  linarith

/-- The odd-indexed ratios strictly increase: a(2k+1) < a(2k+3). -/
lemma aSeq_odd_step (k : ℕ) :
    altFactPartialSum (2 * k + 1) < altFactPartialSum (2 * k + 3) := by
  rw [show (2 * k + 3) = (2 * k + 1) + 2 by ring, aSeq_add_two]
  rw [altFactTerm_of_even (show Even ((2 * k + 1) + 1) from ⟨k + 1, by ring⟩),
      altFactTerm_of_odd (show Odd ((2 * k + 1) + 2) from ⟨k + 1, by ring⟩)]
  have hfac : (((2 * k + 1) + 1).factorial : ℝ) < (((2 * k + 1) + 2).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_lt (by omega)).mpr (by omega)
  have h1 : (1 : ℝ) / (((2 * k + 1) + 2).factorial : ℝ)
      < 1 / (((2 * k + 1) + 1).factorial : ℝ) :=
    one_div_lt_one_div_of_lt (factorial_cast_pos' ((2 * k + 1) + 1)) hfac
  linarith

lemma aeven_strictAnti : StrictAnti (fun k => altFactPartialSum (2 * k)) :=
  strictAnti_nat_of_succ_lt (fun k => by
    have h := aSeq_even_step k
    simpa [Nat.mul_succ] using h)

lemma aodd_strictMono : StrictMono (fun k => altFactPartialSum (2 * k + 1)) :=
  strictMono_nat_of_lt_succ (fun k => by
    have h := aSeq_odd_step k
    simpa [Nat.mul_succ] using h)

/- ## §3. Both subsequences converge to e⁻¹ -/

/-- The partial sums a(n) = D(n)/n! tend to e⁻¹ (restatement of the parent). -/
lemma aSeq_tendsto :
    Tendsto altFactPartialSum atTop (nhds (rexp (-1))) :=
  derangements_tendsto_inv_e.congr (fun n => derangements_div_factorial n)

lemma tendsto_two_mul : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
  tendsto_atTop_mono (fun k => by simp only [id_eq]; omega) tendsto_id

lemma tendsto_two_mul_add_one : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
  tendsto_atTop_mono (fun k => by simp only [id_eq]; omega) tendsto_id

lemma aeven_tendsto :
    Tendsto (fun k => altFactPartialSum (2 * k)) atTop (nhds (rexp (-1))) := by
  have h := aSeq_tendsto.comp tendsto_two_mul
  simpa [Function.comp] using h

lemma aodd_tendsto :
    Tendsto (fun k => altFactPartialSum (2 * k + 1)) atTop (nhds (rexp (-1))) := by
  have h := aSeq_tendsto.comp tendsto_two_mul_add_one
  simpa [Function.comp] using h

/- ## §4. Strictly monotone convergent sequences stay on one side of the limit -/

/-- A strictly decreasing sequence stays strictly above its limit. -/
lemma lt_of_strictAnti_tendsto {f : ℕ → ℝ} {L : ℝ} (hf : StrictAnti f)
    (hL : Tendsto f atTop (nhds L)) (n : ℕ) : L < f n := by
  have h1 : L ≤ f (n + 1) :=
    le_of_tendsto hL (eventually_atTop.mpr ⟨n + 1, fun m hm => hf.antitone hm⟩)
  exact lt_of_le_of_lt h1 (hf (Nat.lt_succ_self n))

/-- A strictly increasing sequence stays strictly below its limit. -/
lemma gt_of_strictMono_tendsto {f : ℕ → ℝ} {L : ℝ} (hf : StrictMono f)
    (hL : Tendsto f atTop (nhds L)) (n : ℕ) : f n < L := by
  have h1 : f (n + 1) ≤ L :=
    ge_of_tendsto hL (eventually_atTop.mpr ⟨n + 1, fun m hm => hf.monotone hm⟩)
  exact lt_of_lt_of_le (hf (Nat.lt_succ_self n)) h1

/- ## §5. Main bracketing results -/

/-- Even-indexed derangement ratios lie strictly above 1/e. -/
theorem ratio_even_gt (k : ℕ) : rexp (-1) < altFactPartialSum (2 * k) :=
  lt_of_strictAnti_tendsto aeven_strictAnti aeven_tendsto k

/-- Odd-indexed derangement ratios lie strictly below 1/e. -/
theorem ratio_odd_lt (k : ℕ) : altFactPartialSum (2 * k + 1) < rexp (-1) :=
  gt_of_strictMono_tendsto aodd_strictMono aodd_tendsto k

/-- For even `n`, the ratio is above 1/e. -/
theorem aSeq_gt_of_even {n : ℕ} (hn : Even n) :
    rexp (-1) < altFactPartialSum n := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul]
  exact ratio_even_gt k

/-- For odd `n`, the ratio is below 1/e. -/
theorem aSeq_lt_of_odd {n : ℕ} (hn : Odd n) :
    altFactPartialSum n < rexp (-1) := by
  obtain ⟨k, rfl⟩ := hn
  exact ratio_odd_lt k

/-- **Two-sided bracketing.** Consecutive derangement ratios straddle 1/e:
    D(2k+1)/(2k+1)! < e⁻¹ < D(2k)/(2k)!. -/
theorem numDerangements_bracket (k : ℕ) :
    (numDerangements (2 * k + 1) : ℝ) / ((2 * k + 1).factorial : ℝ) < rexp (-1) ∧
    rexp (-1) < (numDerangements (2 * k) : ℝ) / ((2 * k).factorial : ℝ) := by
  rw [derangements_div_factorial, derangements_div_factorial]
  exact ⟨ratio_odd_lt k, ratio_even_gt k⟩

/-- **Exact sign of the error.** For every `n`,
    `(-1)^n · (a(n) - e⁻¹) > 0`: the approximation error alternates in sign. -/
theorem aSeq_error_sign (n : ℕ) :
    0 < (-1 : ℝ) ^ n * (altFactPartialSum n - rexp (-1)) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul, sub_pos]
    exact aSeq_gt_of_even he
  · rw [ho.neg_one_pow, neg_one_mul, neg_pos, sub_neg]
    exact aSeq_lt_of_odd ho

/-- The sign statement in terms of the derangement ratio D(n)/n!. -/
theorem numDerangements_error_sign (n : ℕ) :
    0 < (-1 : ℝ) ^ n *
      ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) := by
  rw [derangements_div_factorial]
  exact aSeq_error_sign n

/-- Consecutive errors have opposite signs, hence negative product. -/
theorem consecutive_error_opposite (n : ℕ) :
    (altFactPartialSum n - rexp (-1)) * (altFactPartialSum (n + 1) - rexp (-1)) < 0 := by
  rcases Nat.even_or_odd n with he | ho
  · exact mul_neg_of_pos_of_neg
      (by linarith [aSeq_gt_of_even he])
      (by linarith [aSeq_lt_of_odd he.add_one])
  · exact mul_neg_of_neg_of_pos
      (by linarith [aSeq_lt_of_odd ho])
      (by linarith [aSeq_gt_of_even ho.add_one])

/-- **Exact nesting width.** The bracketing interval [a(2k+1), a(2k)] has width
    exactly 1/(2k+1)!, which shrinks to 0. -/
theorem nested_interval_width (k : ℕ) :
    altFactPartialSum (2 * k) - altFactPartialSum (2 * k + 1)
      = 1 / ((2 * k + 1).factorial : ℝ) := by
  rw [altFactPartialSum_succ, altFactTerm_of_odd (show Odd (2 * k + 1) from ⟨k, by ring⟩)]
  ring

/- ## §6. Integer-side corollaries -/

/-- For even `n`, the derangement count exceeds n!/e. -/
theorem numDerangements_gt_of_even {n : ℕ} (hn : Even n) :
    (n.factorial : ℝ) * rexp (-1) < (numDerangements n : ℝ) := by
  have h := aSeq_gt_of_even hn
  rw [← derangements_div_factorial, lt_div_iff₀ (factorial_cast_pos' n)] at h
  rw [mul_comm]
  exact h

/-- For odd `n`, the derangement count is below n!/e. -/
theorem numDerangements_lt_of_odd {n : ℕ} (hn : Odd n) :
    (numDerangements n : ℝ) < (n.factorial : ℝ) * rexp (-1) := by
  have h := aSeq_lt_of_odd hn
  rw [← derangements_div_factorial, div_lt_iff₀ (factorial_cast_pos' n)] at h
  rw [mul_comm]
  exact h

end DerangementsConvergenceOQ02
