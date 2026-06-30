/-
# Erdős Problem #396 — OQ-04 → OQ-01: Asymptotics of the Catalan recurrence ratio

The parent entry `Erdos396OQ04` proves the elementary two-term Catalan
recurrence

  `(n+2) · catalan (n+1) = 2·(2n+1) · catalan n`,

equivalently `catalan (n+1) = (4n+2)/(n+2) · catalan n`. This follow-up reads
that recurrence **as a statement about the ratio of consecutive Catalan
numbers** and extracts its asymptotics.

Let `r n = (4n+2)/(n+2)` be the exact multiplicative step of the recurrence.
The key algebraic observation is the partial-fraction identity

  `r n = 4 − 6/(n+2)`,

which immediately gives three facts Mathlib does not record:

* **`ratio_lt_four`** : `r n < 4` for every `n` (the step never reaches `4`);
* **`ratio_strictMono`** : `r` is strictly increasing (it climbs toward `4`);
* **`ratio_tendsto_four`** : `r n → 4` as `n → ∞`.

Combined with the recurrence this yields purely from the recurrence — without
Stirling's formula or any central-binomial estimate — the classical growth
bounds

* **`catalan_succ_lt_four_mul`** : `catalan (n+1) < 4 · catalan n`, and
* **`catalan_lt_four_pow`** : `catalan n < 4^n` for `n ≥ 1`, with the clean
  `catalan_le_four_pow` : `catalan n ≤ 4^n` for all `n`.

The ratio limit `r n → 4` is the discrete shadow of the exponential growth rate
`4` of the Catalan numbers (`catalan n ∼ 4^n / (n^{3/2}√π)`); here it is proved
directly from the integer recurrence.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat Filter Topology

namespace Erdos396OQ01

/- ## The two-term Catalan recurrence (re-derived, self-contained)

We reprove the recurrence from the two Mathlib facts so this file does not
depend on the parent build. -/

/-- `C(2(n+1), n+1) = 2·(2n+1) · catalan n`. -/
theorem centralBinom_succ_eq (n : ℕ) :
    Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom n] at h
  refine Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega) ?_
  rw [h]; ring

/-- **Two-term Catalan recurrence.** `(n+2)·catalan(n+1) = 2·(2n+1)·catalan n`. -/
theorem catalan_recurrence (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := succ_mul_catalan_eq_centralBinom (n + 1)
  rw [centralBinom_succ_eq] at h
  exact h

/-- Positivity of the Catalan numbers (Mathlib has no `catalan_pos`).
    From `(n+1)·catalan n = C(2n,n) > 0`. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  rcases Nat.eq_zero_or_pos (catalan n) with hz | hp
  · rw [hz, mul_zero] at h
    exact absurd h.symm (Nat.centralBinom_pos n).ne'
  · exact hp

/- ## The recurrence ratio -/

/-- The exact multiplicative step of the recurrence,
    `r n = (4n+2)/(n+2) = 2·(2n+1)/(n+2)`, as a real number. -/
noncomputable def catalanRatio (n : ℕ) : ℝ := (4 * n + 2) / (n + 2)

/-- **Partial-fraction form.** `r n = 4 − 6/(n+2)`. The whole asymptotic
    behaviour of the ratio is read off this identity. -/
theorem ratio_eq_four_sub (n : ℕ) :
    catalanRatio n = 4 - 6 / ((n : ℝ) + 2) := by
  have hpos : (n : ℝ) + 2 ≠ 0 := by positivity
  rw [catalanRatio]
  field_simp
  ring

/-- The ratio is the genuine quotient of consecutive Catalan numbers:
    `(catalan (n+1) : ℝ) = r n · catalan n`. -/
theorem catalan_succ_eq_ratio_mul (n : ℕ) :
    (catalan (n + 1) : ℝ) = catalanRatio n * catalan n := by
  have h := catalan_recurrence n
  have hcast : ((n : ℝ) + 2) * (catalan (n + 1) : ℝ)
      = (4 * (n : ℝ) + 2) * (catalan n : ℝ) := by
    have h2 := congrArg (fun k : ℕ => (k : ℝ)) h
    push_cast at h2
    linear_combination h2
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [catalanRatio, div_mul_eq_mul_div, eq_div_iff hpos.ne']
  linear_combination hcast

/-- The step never reaches `4`: `r n < 4`. -/
theorem ratio_lt_four (n : ℕ) : catalanRatio n < 4 := by
  rw [ratio_eq_four_sub]
  have : (0 : ℝ) < 6 / ((n : ℝ) + 2) := by positivity
  linarith

/-- The step is positive: `0 < r n`. -/
theorem ratio_pos (n : ℕ) : 0 < catalanRatio n := by
  rw [catalanRatio]; positivity

/-- The ratio is strictly increasing in `n` (it climbs monotonically to `4`). -/
theorem ratio_strictMono : StrictMono catalanRatio := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [ratio_eq_four_sub, ratio_eq_four_sub]
  have hkey : (6 : ℝ) / (((n : ℝ) + 1) + 2) < 6 / ((n : ℝ) + 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  push_cast
  linarith [hkey]

/-- **Ratio limit.** `r n → 4` as `n → ∞`. -/
theorem ratio_tendsto_four : Tendsto catalanRatio atTop (𝓝 4) := by
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ => 6 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h0 := hden.inv_tendsto_atTop
    have hmul := h0.const_mul (6 : ℝ)
    simpa [div_eq_mul_inv] using hmul
  have hsub : Tendsto (fun n : ℕ => 4 - 6 / ((n : ℝ) + 2)) atTop (𝓝 (4 - 0)) :=
    tendsto_const_nhds.sub hinv
  rw [sub_zero] at hsub
  exact hsub.congr (fun n => (ratio_eq_four_sub n).symm)

/- ## Growth bounds from the recurrence -/

/-- **Sub-`4` growth, integer form.** `catalan (n+1) < 4 · catalan n`.

    From `(n+2)·catalan(n+1) = (4n+2)·catalan n < (4n+8)·catalan n
    = 4(n+2)·catalan n`, cancelling the positive factor `n+2`. -/
theorem catalan_succ_lt_four_mul (n : ℕ) :
    catalan (n + 1) < 4 * catalan n := by
  have hc : 0 < catalan n := catalan_pos n
  have hrec := catalan_recurrence n
  have h2 : 2 * (2 * n + 1) < (n + 2) * 4 := by omega
  have hstep : 2 * (2 * n + 1) * catalan n < (n + 2) * 4 * catalan n :=
    mul_lt_mul_of_pos_right h2 hc
  have hkey : (n + 2) * catalan (n + 1) < (n + 2) * (4 * catalan n) := by
    rw [hrec]
    calc 2 * (2 * n + 1) * catalan n
        < (n + 2) * 4 * catalan n := hstep
      _ = (n + 2) * (4 * catalan n) := by ring
  exact Nat.lt_of_mul_lt_mul_left hkey

/-- `catalan n ≤ 4^n` for every `n`. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : catalan (k + 1) < 4 * catalan k := catalan_succ_lt_four_mul k
    have h2 : 4 * catalan k ≤ 4 * 4 ^ k := Nat.mul_le_mul (le_refl 4) ih
    have h3 : 4 * 4 ^ k = 4 ^ (k + 1) := by rw [pow_succ]; ring
    omega

/-- **Strict growth bound.** `catalan n < 4^n` for `n ≥ 1`. -/
theorem catalan_lt_four_pow (n : ℕ) (hn : 1 ≤ n) : catalan n < 4 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h1 : catalan (m + 1) < 4 * catalan m := catalan_succ_lt_four_mul m
  have h2 : 4 * catalan m ≤ 4 * 4 ^ m := Nat.mul_le_mul (le_refl 4) (catalan_le_four_pow m)
  have h3 : 4 * 4 ^ m = 4 ^ (m + 1) := by rw [pow_succ]; ring
  rw [← h3]
  exact lt_of_lt_of_le h1 h2

/- ## Sanity checks -/

/-- `r 0 = 1`: `catalan 1 = catalan 0`. -/
example : catalanRatio 0 = 1 := by rw [catalanRatio]; norm_num

/-- `r 2 = 10/4 = 5/2`: `catalan 3 = (5/2)·catalan 2`, i.e. `5 = (5/2)·2`. -/
example : catalanRatio 2 = 5 / 2 := by rw [catalanRatio]; norm_num

/-- Growth at `n = 3`: `catalan 3 = 5 < 4³ = 64`. -/
example : catalan 3 < 4 ^ 3 := catalan_lt_four_pow 3 (by norm_num)

end Erdos396OQ01
