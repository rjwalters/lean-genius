/-
  # Higher even lambda values: λ(6) = π⁶/960 and λ(8) = 17π⁸/161280
  # (basel-problem-oq-13-oq-02)

  ## The Open Question

  The parent entry `basel-problem-oq-13` formalizes the *lambda value*
  λ(4) = ∑_{k≥0} 1/(2k+1)⁴ = π⁴/96 by the parity split λ(s) = (1 − 2^(−s)) ζ(s),
  reusing Mathlib's `hasSum_zeta_four` (ζ(4) = π⁴/90). The follow-up question asks to
  **generalize the parity-split template to the full lambda value** λ(s) = (1 − 2^(−s)) ζ(s)
  for higher even s, packaging λ(6) and λ(8) from Mathlib's general even-zeta formula
  `hasSum_zeta_nat` by the *same* even/odd `HasSum` split.

  ## What is new here

  Mathlib provides ζ(2) and ζ(4) explicitly (`hasSum_zeta_two`, `hasSum_zeta_four`),
  but nothing higher as a standalone `HasSum`. The general formula

      ζ(2k) = ∑_n 1/n^(2k) = (−1)^(k+1) · 2^(2k−1) · π^(2k) · B_(2k) / (2k)!

  is `hasSum_zeta_nat`, phrased through the Bernoulli numbers `bernoulli (2k)`.
  Mathlib only computes the Bernoulli numbers up to `bernoulli' 4`, so to instantiate
  the formula at k = 3 and k = 4 we first compute

      bernoulli 6 = 1/42,   bernoulli 8 = −1/30

  from the defining recurrence. These give

      ζ(6) = π⁶/945,        ζ(8) = π⁸/9450.

  ## The parity split

  Splitting ζ(s) into even- and odd-indexed parts via `HasSum.even_add_odd`:

    * even part:  ∑_k 1/(2k)ˢ = 2^(−s) ζ(s),
    * odd part:   λ(s) = ∑_k 1/(2k+1)ˢ = ζ(s) − 2^(−s) ζ(s) = (1 − 2^(−s)) ζ(s).

  For s = 6:  λ(6) = (1 − 1/64)(π⁶/945)  = (63/64)(π⁶/945) = π⁶/960.
  For s = 8:  λ(8) = (1 − 1/256)(π⁸/9450) = (255/256)(π⁸/9450) = 17π⁸/161280.

  Everything is built from `hasSum_zeta_nat` and the even/odd series split — no new
  analytic input beyond the two Bernoulli-number computations.

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real Finset

namespace BaselHigherLambda

/-! ## Step 1: the Bernoulli numbers `B₆` and `B₈`

Mathlib stops at `bernoulli' 4`; we extend the table to the two values we need,
using the defining recurrence `bernoulli'_def` and the vanishing of odd Bernoulli
numbers `bernoulli'_eq_zero_of_odd`. -/

/-- `bernoulli' 6 = 1/42`. -/
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5, Nat.choose]

/-- `bernoulli' 8 = -1/30`. -/
theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_six, h5, h7, Nat.choose]

/-- `bernoulli 6 = 1/42` (the even-index sign is `+`). -/
theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]

/-- `bernoulli 8 = -1/30`. -/
theorem bernoulli_eight : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]

/-! ## Step 2: the zeta values ζ(6) and ζ(8)

Instantiate the general even-zeta formula `hasSum_zeta_nat` at `k = 3` and `k = 4`. -/

/-- **Sixth zeta value**: `∑_n 1/n⁶ = π⁶/945`. -/
theorem hasSum_zeta_six : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (π ^ 6 / 945) := by
  convert hasSum_zeta_nat (k := 3) (by norm_num) using 2
  · norm_num
  · rw [show (2 * 3 : ℕ) = 6 from rfl, bernoulli_six]
    norm_num [Nat.factorial]

/-- **Eighth zeta value**: `∑_n 1/n⁸ = π⁸/9450`. -/
theorem hasSum_zeta_eight : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 8) (π ^ 8 / 9450) := by
  convert hasSum_zeta_nat (k := 4) (by norm_num) using 2
  · norm_num
  · rw [show (2 * 4 : ℕ) = 8 from rfl, bernoulli_eight]
    norm_num [Nat.factorial]

/-! ## Step 3: the even parts, `2^(−s) ζ(s)` -/

/-- Even-indexed sixth-power sum: `∑_k 1/(2k)⁶ = π⁶/60480` (a 64-th of ζ(6)). -/
theorem hasSum_even_zeta_six :
    HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 6) (π ^ 6 / 60480) := by
  have h64 := hasSum_zeta_six.mul_left (1 / 64 : ℝ)
  have hfe : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 6)
      = (fun k : ℕ => (1 / 64 : ℝ) * (1 / (k : ℝ) ^ 6)) := by
    funext k; push_cast; ring
  rw [hfe]
  convert h64 using 1
  ring

/-- Even-indexed eighth-power sum: `∑_k 1/(2k)⁸ = π⁸/2419200` (a 256-th of ζ(8)). -/
theorem hasSum_even_zeta_eight :
    HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 8) (π ^ 8 / 2419200) := by
  have h256 := hasSum_zeta_eight.mul_left (1 / 256 : ℝ)
  have hfe : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 8)
      = (fun k : ℕ => (1 / 256 : ℝ) * (1 / (k : ℝ) ^ 8)) := by
    funext k; push_cast; ring
  rw [hfe]
  convert h256 using 1
  ring

/-! ## Step 4: the odd parts — the lambda values λ(6) and λ(8) -/

/-- **λ(6)**: `∑_k 1/(2k+1)⁶ = π⁶/960`. Derived from `hasSum_zeta_six` by the even/odd
    split: ζ(6) = (even part π⁶/60480) + (odd part), so the odd part is
    π⁶/945 − π⁶/60480 = π⁶/960. -/
theorem hasSum_odd_zeta_six :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 6) (π ^ 6 / 960) := by
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 6) :=
    hasSum_zeta_six.summable.comp_injective (fun a b h => by omega)
  have hkey : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6)
      (π ^ 6 / 60480 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 6) := by
    refine HasSum.even_add_odd ?_ ?_
    · exact hasSum_even_zeta_six
    · exact hodd_summable.hasSum
  have hsum_eq : π ^ 6 / 60480 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 6 = π ^ 6 / 945 :=
    hkey.unique hasSum_zeta_six
  have hval : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 6 = π ^ 6 / 960 := by linarith
  rw [← hval]
  exact hodd_summable.hasSum

/-- **λ(8)**: `∑_k 1/(2k+1)⁸ = 17π⁸/161280`. Derived from `hasSum_zeta_eight` by the
    even/odd split: ζ(8) = (even part π⁸/2419200) + (odd part), so the odd part is
    π⁸/9450 − π⁸/2419200 = 17π⁸/161280. -/
theorem hasSum_odd_zeta_eight :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 8) (17 * π ^ 8 / 161280) := by
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 8) :=
    hasSum_zeta_eight.summable.comp_injective (fun a b h => by omega)
  have hkey : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 8)
      (π ^ 8 / 2419200 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 8) := by
    refine HasSum.even_add_odd ?_ ?_
    · exact hasSum_even_zeta_eight
    · exact hodd_summable.hasSum
  have hsum_eq : π ^ 8 / 2419200 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 8 = π ^ 8 / 9450 :=
    hkey.unique hasSum_zeta_eight
  have hval : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 8 = 17 * π ^ 8 / 161280 := by linarith
  rw [← hval]
  exact hodd_summable.hasSum

/-! ## Step 5: `tsum` forms -/

/-- `∑' k, 1/(2k+1)⁶ = π⁶/960`. -/
theorem tsum_odd_zeta_six :
    ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 6 = π ^ 6 / 960 :=
  hasSum_odd_zeta_six.tsum_eq

/-- `∑' k, 1/(2k+1)⁸ = 17π⁸/161280`. -/
theorem tsum_odd_zeta_eight :
    ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 8 = 17 * π ^ 8 / 161280 :=
  hasSum_odd_zeta_eight.tsum_eq

end BaselHigherLambda

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `bernoulli_six`         | B₆ = 1/42 |
  | `bernoulli_eight`       | B₈ = −1/30 |
  | `hasSum_zeta_six`       | ∑ 1/n⁶ = π⁶/945 |
  | `hasSum_zeta_eight`     | ∑ 1/n⁸ = π⁸/9450 |
  | `hasSum_even_zeta_six`  | ∑ 1/(2k)⁶ = π⁶/60480 |
  | `hasSum_even_zeta_eight`| ∑ 1/(2k)⁸ = π⁸/2419200 |
  | `hasSum_odd_zeta_six`   | λ(6) = ∑ 1/(2k+1)⁶ = π⁶/960 |
  | `hasSum_odd_zeta_eight` | λ(8) = ∑ 1/(2k+1)⁸ = 17π⁸/161280 |
  | `tsum_odd_zeta_six`     | ∑' k, 1/(2k+1)⁶ = π⁶/960 |
  | `tsum_odd_zeta_eight`   | ∑' k, 1/(2k+1)⁸ = 17π⁸/161280 |

  Built entirely from Mathlib's general even-zeta formula `hasSum_zeta_nat`
  (with `bernoulli 6 = 1/42`, `bernoulli 8 = −1/30` computed from the recurrence)
  and the even/odd series split `HasSum.even_add_odd`.

  **Sorries**: 0
  **Axioms**: 0
-/
