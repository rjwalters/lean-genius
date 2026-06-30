import Mathlib

/-
# Telescoping Product  ∏_{k=2}^{n} (1 − 1/k²) = (n+1)/(2n)

## Open Question OQ-01 (telescoping-product)

The gallery records several *telescoping sums*, but no telescoping **product**.
This file fills that gap with the canonical example:

  ∏_{k=2}^{n} (1 − 1/k²) = (n + 1) / (2n).

The mechanism is the algebraic factorisation of each term,

  1 − 1/k² = (k − 1)(k + 1) / k²,

so that the product of the `(k − 1)/k` parts telescopes against the product of the
`(k + 1)/k` parts, leaving only the endpoint contributions `1/2` (from the bottom)
and `(n + 1)/n` (from the top).  Multiplying these gives `(n + 1)/(2n)`.

We formalise three statements:

1. `factor_eq`            — the per-term collapse `1 − 1/k² = (k−1)(k+1)/k²`.
2. `telescoping_product`  — the closed form `∏_{k=2}^{n} (1 − 1/k²) = (n+1)/(2n)`,
                            proved by induction with `Finset.prod_Icc_succ_top`.
3. `tendsto_closed_form`  — the resulting limit `(n+1)/(2n) → 1/2` as `n → ∞`,
                            so the infinite product converges to `1/2`.

## Mathematical Context

This is the multiplicative analogue of a telescoping sum.  Mathlib provides
`Finset.prod_Icc_succ_top` to peel the top factor of a product over `Finset.Icc`,
which drives the induction; the closed form itself is not named in Mathlib.

## Axioms: 0 | Sorries: 0
-/

namespace TelescopingProductOQ01

open Finset

/-- **Per-term collapse.** For `k ≥ 2`, the factor `1 − 1/k²` equals
`(k − 1)(k + 1) / k²`.  This is the algebraic identity that makes the product
telescope: the `k − 1` of one term cancels a numerator further down, and the
`k + 1` cancels a numerator further up. -/
lemma factor_eq (k : ℕ) (hk : 2 ≤ k) :
    (1 - 1 / (k : ℚ) ^ 2) = ((k : ℚ) - 1) * ((k : ℚ) + 1) / (k : ℚ) ^ 2 := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  field_simp
  ring

/-- **Main identity.** The telescoping product over `2 ≤ k ≤ n` has the closed form

  ∏_{k=2}^{n} (1 − 1/k²) = (n + 1) / (2n)            (for `n ≥ 1`).

The empty product (`n = 1`) reads `1 = 2/2`, and each induction step peels the top
factor with `Finset.prod_Icc_succ_top`, after which `field_simp`/`ring` verify the
rational identity `(m+1)/(2m) · (1 − 1/(m+1)²) = (m+2)/(2(m+1))`. -/
theorem telescoping_product (n : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, (1 - 1 / (k : ℚ) ^ 2) = ((n : ℚ) + 1) / (2 * n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- `Finset.Icc 2 1 = ∅`, so the product is `1`, and the RHS is `2/2 = 1`.
    rw [Finset.Icc_eq_empty (by norm_num)]
    norm_num
  | succ m hm ih =>
    -- Peel the top factor `1 − 1/(m+1)²` and rewrite the remaining product via `ih`.
    rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 1), ih]
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by omega
      exact_mod_cast this
    have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **Limit.** The closed form `(n + 1)/(2n)` converges to `1/2`, so the infinite
telescoping product `∏_{k≥2} (1 − 1/k²)` equals `1/2`. -/
theorem tendsto_closed_form :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (2 * n)) Filter.atTop (nhds (1 / 2)) := by
  -- For `n ≥ 1`, `(n+1)/(2n) = 1/2 + (1/2)·(1/n)`, which tends to `1/2 + 0`.
  have hlim :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) + (1 / 2) * (1 / (n : ℝ)))
        Filter.atTop (nhds ((1 / 2 : ℝ) + (1 / 2) * 0)) :=
    Filter.Tendsto.add tendsto_const_nhds
      (Filter.Tendsto.const_mul _ tendsto_one_div_atTop_nhds_zero_nat)
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  -- After clearing denominators (n ≠ 0), both sides reduce to the same numerator.
  field_simp

end TelescopingProductOQ01
