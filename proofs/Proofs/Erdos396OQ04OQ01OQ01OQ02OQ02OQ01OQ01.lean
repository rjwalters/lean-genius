/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-02 → OQ-01 → OQ-01: the Wallis *integral* representation of the central binomial coefficient

The parent `Erdos396OQ04OQ01OQ01OQ02OQ02OQ01` (the telescoping Wallis product)
expresses the normalised central binomial coefficient as a finite **combinatorial**
product,

  `C(2n,n) / 4^n = ∏_{k<n} (2k+1)/(2k+2)`   (`centralBinom_div_eq_wallis_prod`),

the truncation `(2n−1)!!/(2n)!!` of Wallis' product.  That identity lives entirely
in `ℚ`-arithmetic of the recurrence; it never touches an integral.

This file supplies the *analytic* twin.  Mathlib's Wallis machinery evaluates the
definite integrals of powers of `sin` over `[0, π]` in **exactly** the same closed
products:

  `∫₀^π sin²ⁿx dx = π · ∏_{k<n} (2k+1)/(2k+2)`        (`integral_sin_pow_even`),
  `∫₀^π sin²ⁿ⁺¹x dx = 2 · ∏_{k<n} (2k+2)/(2k+3)`      (`integral_sin_pow_odd`).

Composing the even formula with the parent's combinatorial product collapses the
product on both sides and yields the headline **integral representation**

  **`integral_sin_pow_even_eq_centralBinom`** :
      `∫₀^π sin²ⁿx dx = π · C(2n,n) / 4^n`,

equivalently the *combinatorial* number is an *analytic* quantity

  **`centralBinom_eq_integral`** : `C(2n,n) = (4^n / π) · ∫₀^π sin²ⁿx dx`.

For the odd powers a one-line telescope `∏_{k<n} (2k+1)/(2k+3) = 1/(2n+1)` turns
the `(2k+2)/(2k+3)` product into the reciprocal central binomial,

  **`wallis_odd_prod_eq`** : `∏_{k<n} (2k+2)/(2k+3) = 4^n / ((2n+1)·C(2n,n))`,
  **`integral_sin_pow_odd_eq_centralBinom`** :
      `∫₀^π sin²ⁿ⁺¹x dx = 2·4^n / ((2n+1)·C(2n,n))`.

Multiplying the even and odd integrals makes the central binomial coefficient
**cancel completely**, leaving a quantity free of all combinatorics:

  **`integral_even_mul_odd_eq`** :
      `(∫₀^π sin²ⁿx)·(∫₀^π sin²ⁿ⁺¹x) = 2π / (2n+1)`.

Dividing them instead exposes the **square** of the normalised central binomial
sequence, the object whose `1/√(πn)` asymptotic the sibling files pin down:

  **`integral_ratio_eq`** :
      `(∫₀^π sin²ⁿx)/(∫₀^π sin²ⁿ⁺¹x) = (π/2)·(2n+1)·(C(2n,n)/4^n)²`.

Since Wallis' theorem forces this ratio to `1`, the identity is the analytic origin
of `C(2n,n)/4^n ∼ 1/√(πn)`.  No Stirling estimate is used; the central binomial
recurrence (via the imported parent) is the only combinatorial input.

Reference: https://erdosproblems.com/396
-/

import Mathlib
import Proofs.Erdos396OQ04OQ01OQ01OQ02OQ02OQ01

open Nat Finset Real MeasureTheory intervalIntegral

namespace Erdos396OQ04OQ01OQ01OQ02OQ02OQ01OQ01

/-! ## The odd-index telescoping product

The combinatorial input for the *odd* powers is the elementary telescope
`(1/3)·(3/5)·(5/7)···((2n−1)/(2n+1)) = 1/(2n+1)`. -/

/-- **Odd telescope.** `∏_{k<n} (2k+1)/(2k+3) = 1/(2n+1)`. -/
theorem prod_odd_telescope (n : ℕ) :
    ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 3) = 1 / (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-! ## The even powers: the integral representation -/

/-- **Headline — the Wallis integral representation of the central binomial coefficient.**
    The definite integral of `sin²ⁿ` over `[0, π]` equals `π · C(2n,n)/4^n`.  This is
    the analytic counterpart of the parent's combinatorial product
    `C(2n,n)/4^n = ∏ (2k+1)/(2k+2)`. -/
theorem integral_sin_pow_even_eq_centralBinom (n : ℕ) :
    (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n)) = π * (centralBinom n : ℝ) / 4 ^ n := by
  rw [integral_sin_pow_even, ← Erdos396OQ01OQ01OQ02OQ02OQ01.centralBinom_div_eq_wallis_prod]
  ring

/-- **The central binomial coefficient as an integral.** Inverting the headline:
    the purely combinatorial number `C(2n,n)` is recovered analytically as
    `(4^n/π) · ∫₀^π sin²ⁿ`. -/
theorem centralBinom_eq_integral (n : ℕ) :
    (centralBinom n : ℝ) = 4 ^ n / π * ∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n) := by
  rw [integral_sin_pow_even_eq_centralBinom]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-! ## The odd powers: the reciprocal central binomial -/

/-- **The odd Wallis product in closed form.** Combining the parent's even product
    with the odd telescope: `∏_{k<n} (2k+2)/(2k+3) = 4^n / ((2n+1)·C(2n,n))`. -/
theorem wallis_odd_prod_eq (n : ℕ) :
    (∏ i ∈ Finset.range n, (2 * (i : ℝ) + 2) / (2 * (i : ℝ) + 3))
      = 4 ^ n / ((2 * (n : ℝ) + 1) * centralBinom n) := by
  set A := ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2) with hA_def
  set B := ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 2) / (2 * (i : ℝ) + 3) with hB_def
  have hA : A = (centralBinom n : ℝ) / 4 ^ n :=
    (Erdos396OQ01OQ01OQ02OQ02OQ01.centralBinom_div_eq_wallis_prod n).symm
  -- `A · B` collapses factorwise to the odd telescope `∏ (2k+1)/(2k+3)`.
  have hAB : A * B = ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 3) := by
    rw [hA_def, hB_def, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have h2 : (2 * (i : ℝ) + 2) ≠ 0 := by positivity
    field_simp
  -- so `A · B · (2n+1) = 1`.
  have hABt : A * B * (2 * (n : ℝ) + 1) = 1 := by
    rw [hAB, prod_odd_telescope]
    have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  -- and `C = A · 4^n`.
  have hC : (centralBinom n : ℝ) = A * 4 ^ n := by
    rw [hA]; field_simp
  have hden : (2 * (n : ℝ) + 1) * (centralBinom n : ℝ) ≠ 0 := by
    refine mul_ne_zero (by positivity) ?_
    exact_mod_cast Nat.centralBinom_ne_zero n
  rw [eq_div_iff hden, hC]
  linear_combination (4 : ℝ) ^ n * hABt

/-- The integral of `sin²ⁿ⁺¹` over `[0, π]` is `2·4^n / ((2n+1)·C(2n,n))`. -/
theorem integral_sin_pow_odd_eq_centralBinom (n : ℕ) :
    (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n + 1))
      = 2 * 4 ^ n / ((2 * (n : ℝ) + 1) * centralBinom n) := by
  rw [integral_sin_pow_odd, wallis_odd_prod_eq]
  ring

/-! ## Consequences: the central binomial coefficient cancels -/

/-- **Even times odd.** The product of the two consecutive Wallis integrals is
    `2π/(2n+1)` — the central binomial coefficient cancels completely. -/
theorem integral_even_mul_odd_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n)) * (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n + 1))
      = 2 * π / (2 * (n : ℝ) + 1) := by
  rw [integral_sin_pow_even_eq_centralBinom, integral_sin_pow_odd_eq_centralBinom]
  have hCne : (centralBinom n : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
  have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- **Even over odd.** Dividing the two integrals isolates the *square* of the
    normalised central binomial sequence `C(2n,n)/4^n` — the object whose
    `1/√(πn)` asymptotic the sibling files establish.  Wallis' theorem (this ratio
    tends to `1`) is therefore the analytic source of that asymptotic. -/
theorem integral_ratio_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n)) / (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n + 1))
      = π / 2 * (2 * (n : ℝ) + 1) * ((centralBinom n : ℝ) / 4 ^ n) ^ 2 := by
  rw [integral_sin_pow_even_eq_centralBinom, integral_sin_pow_odd_eq_centralBinom]
  have hCne : (centralBinom n : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
  have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

end Erdos396OQ04OQ01OQ01OQ02OQ02OQ01OQ01
