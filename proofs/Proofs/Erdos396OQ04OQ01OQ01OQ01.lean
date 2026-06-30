/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-01: Catalan as a telescoping product of recurrence ratios

The grandparent entry `Erdos396OQ04OQ01` reads the two-term Catalan recurrence
as a statement about the **ratio** of consecutive Catalan numbers,

  `r n = (4n+2)/(n+2) = 4 − 6/(n+2)`,        with `catalan (n+1) = r n · catalan n`,

and the parent `Erdos396OQ04OQ01OQ01` studies the *additive* running total of the
ratios, `∑_{k<n} r k = 4n − 6·(H_{n+1} − 1)`.

This follow-up takes the **multiplicative** view that the recurrence itself
suggests. Because each step multiplies by `r k`, the recurrence telescopes into a
closed product

* **`catalan_eq_prod_ratio`** : `(catalan n : ℝ) = ∏_{k<n} r k` — the Catalan
  number *is* the product of the first `n` recurrence ratios.

This is the exact multiplicative companion of the parent's sum identity, and the
two are bridged by the logarithm:

* **`log_catalan_eq_sum_log_ratio`** : `log (catalan n) = ∑_{k<n} log (r k)`.

Reading the product against the limiting rate `4` gives the normalized Catalan
sequence as a product of factors below `1`:

* **`catalan_div_four_pow_eq_prod`** : `catalan n / 4^n = ∏_{k<n} (r k / 4)`, each
  factor `r k / 4 < 1` (**`ratio_div_four_lt_one`**), so
* **`catalan_div_four_pow_strictAnti`** : `catalan (n+1)/4^{n+1} < catalan n/4^n`
  — the normalized sequence `catalan n / 4^n` is **strictly decreasing**, the
  multiplicative shadow of the polynomial correction in `catalan n ∼ 4^n/(n^{3/2}√π)`.

The product form also recovers the grandparent's growth bound directly:

* **`prod_ratio_lt_four_pow`** : `∏_{k<n} r k < 4^n` for `n ≥ 1`, i.e.
  `catalan n < 4^n`, now as a strict product inequality (every factor `< 4`).

Everything is derived from the grandparent's ratio identities by telescoping; no
Stirling estimate or central-binomial bound is used.

Reference: https://erdosproblems.com/396
-/

import Mathlib
import Proofs.Erdos396OQ04OQ01

open Nat Filter Topology Finset

namespace Erdos396OQ01OQ01OQ01

open Erdos396OQ01

/- ## The telescoping product -/

/-- **Telescoping product identity.** `(catalan n : ℝ) = ∏_{k<n} r k`: the `n`-th
    Catalan number is exactly the product of the first `n` recurrence ratios.
    Each step of the recurrence multiplies by `r k`, so the recurrence collapses
    to a finite product. -/
theorem catalan_eq_prod_ratio (n : ℕ) :
    (catalan n : ℝ) = ∏ k ∈ Finset.range n, catalanRatio k := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, catalan_succ_eq_ratio_mul]
    ring

/-- The product of ratios is strictly positive. -/
theorem prod_ratio_pos (n : ℕ) : 0 < ∏ k ∈ Finset.range n, catalanRatio k :=
  Finset.prod_pos (fun k _ => ratio_pos k)

/-- `catalan n / 4^n > 0`. -/
theorem catalan_div_four_pow_pos (n : ℕ) : 0 < (catalan n : ℝ) / 4 ^ n := by
  apply _root_.div_pos
  · exact_mod_cast catalan_pos n
  · positivity

/- ## The sum–product bridge -/

/-- **Logarithmic bridge.** `log (catalan n) = ∑_{k<n} log (r k)`. The logarithm
    converts the telescoping product into the parent's additive running total of
    the (log-)ratios. -/
theorem log_catalan_eq_sum_log_ratio (n : ℕ) :
    Real.log (catalan n) = ∑ k ∈ Finset.range n, Real.log (catalanRatio k) := by
  rw [catalan_eq_prod_ratio, Real.log_prod]
  intro k _
  exact (ratio_pos k).ne'

/- ## The normalized sequence `catalan n / 4^n` -/

/-- Each normalized factor is below `1`: `r n / 4 < 1`. -/
theorem ratio_div_four_lt_one (n : ℕ) : catalanRatio n / 4 < 1 := by
  rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
  exact ratio_lt_four n

/-- **Normalized product form.** `catalan n / 4^n = ∏_{k<n} (r k / 4)`: dividing
    the telescoping product by `4^n` distributes over the factors. -/
theorem catalan_div_four_pow_eq_prod (n : ℕ) :
    (catalan n : ℝ) / 4 ^ n = ∏ k ∈ Finset.range n, catalanRatio k / 4 := by
  rw [catalan_eq_prod_ratio, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_range]

/-- Factoring out one normalized step:
    `catalan (n+1)/4^{n+1} = (r n / 4) · (catalan n / 4^n)`. -/
theorem catalan_div_four_pow_succ (n : ℕ) :
    (catalan (n + 1) : ℝ) / 4 ^ (n + 1)
      = (catalanRatio n / 4) * ((catalan n : ℝ) / 4 ^ n) := by
  rw [catalan_succ_eq_ratio_mul, pow_succ]
  field_simp

/-- **The normalized Catalan sequence is strictly decreasing.**
    `catalan (n+1)/4^{n+1} < catalan n/4^n`.

    Each new factor `r n / 4` is strictly below `1`, so multiplying by it strictly
    shrinks the positive quantity `catalan n / 4^n`. This is the multiplicative
    reason `catalan n / 4^n` carries the polynomial correction `~ 1/(n^{3/2}√π)`
    below the bare exponential `4^n` — proved here purely from the recurrence. -/
theorem catalan_div_four_pow_strictAnti (n : ℕ) :
    (catalan (n + 1) : ℝ) / 4 ^ (n + 1) < (catalan n : ℝ) / 4 ^ n := by
  rw [catalan_div_four_pow_succ]
  calc (catalanRatio n / 4) * ((catalan n : ℝ) / 4 ^ n)
      < 1 * ((catalan n : ℝ) / 4 ^ n) :=
        mul_lt_mul_of_pos_right (ratio_div_four_lt_one n) (catalan_div_four_pow_pos n)
    _ = (catalan n : ℝ) / 4 ^ n := one_mul _

/- ## Growth bound, product form -/

/-- **Product-form growth bound.** `∏_{k<n} r k < 4^n` for `n ≥ 1`, equivalently
    `catalan n < 4^n`: a strict product inequality because every factor `r k < 4`. -/
theorem prod_ratio_lt_four_pow (n : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Finset.range n, catalanRatio k < 4 ^ n := by
  have hne : (Finset.range n).Nonempty := by
    rw [Finset.nonempty_range_iff]; omega
  calc ∏ k ∈ Finset.range n, catalanRatio k
      < ∏ k ∈ Finset.range n, (4 : ℝ) :=
        Finset.prod_lt_prod_of_nonempty (fun k _ => ratio_pos k)
          (fun k _ => ratio_lt_four k) hne
    _ = 4 ^ n := by rw [Finset.prod_const, Finset.card_range]

/-- The grandparent's bound `catalan n < 4^n` (`n ≥ 1`), recovered from the
    product form. -/
theorem catalan_lt_four_pow_of_prod (n : ℕ) (hn : 1 ≤ n) :
    (catalan n : ℝ) < 4 ^ n := by
  rw [catalan_eq_prod_ratio]
  exact prod_ratio_lt_four_pow n hn

/- ## Sanity checks -/

/-- The telescoping product over the first three ratios is `catalan 3 = 5`:
    `r 0 · r 1 · r 2 = 1 · 2 · (5/2) = 5`. -/
example : ∏ k ∈ Finset.range 3, catalanRatio k = 5 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_zero, catalanRatio, catalanRatio, catalanRatio]
  norm_num

/-- The normalized value at `n = 3`: `catalan 3 / 4^3 = 5/64`. -/
example : (catalan 3 : ℝ) / 4 ^ 3 = 5 / 64 := by
  rw [catalan_eq_prod_ratio, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_zero,
      catalanRatio, catalanRatio, catalanRatio]
  norm_num

end Erdos396OQ01OQ01OQ01
