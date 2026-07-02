import Mathlib

/-
# Raabe Multiplication Formula for Bernoulli Polynomials at m = 3, 4

## Open Question (hermite-sawtooth-identity-oq-01-oq-03)

The parent entry `HermiteSawtoothIdentityOQ01` proves the Raabe multiplication theorem

    `∑_{k=0}^{n-1} Bₘ(x + k/n) = n^{1-m} · Bₘ(n x)`

for the low orders `m = 0, 1, 2` by an elementary, generating-function-free route:
evaluate `Bₘ` to its explicit polynomial and close the sum with the Gauss and
sum-of-squares power-sum formulas.  Its stated open question asks how far this
elementary route reaches:

> *Extend the elementary power-sum route to m = 3, 4 (each a fixed Faulhaber
> identity), charting how far the generating-function-free method reaches before
> the algebra becomes unwieldy.*

This file answers it, proving Raabe at `m = 3` (coefficient `n^{1-3} = n⁻²`) and
`m = 4` (coefficient `n^{1-4} = n⁻³`).  The two new power-sum ingredients are

* `∑_{k<n} k³ = (n(n-1)/2)²`                            (Nicomachus),
* `∑_{k<n} k⁴ = n(n-1)(2n-1)(3n²-3n-1)/30`             (the degree-4 Faulhaber sum).

Verdict on the open question: the elementary route extends cleanly to `m = 3, 4`.
Each order needs exactly the power sums up to `∑ kᵐ⁻¹`, and the closing step is a
single `field_simp; ring`; the only growth is the (mechanical) polynomial
expansion of `Bₘ(x + k/n)` into a `k`-polynomial.  No new ideas are required — the
method is bounded only by the availability of the Faulhaber power sums, so it
reaches every fixed `m` (though the coefficients grow), never becoming genuinely
unwieldy, only longer.

Everything is over ℚ, fully machine-checked, `0`-axiom.  Mathlib provides the
Bernoulli polynomials and `sum_bernoulli` but not the multiplication theorem.
-/

open Polynomial Finset

namespace HermiteSawtoothIdentityOQ01OQ03

/-! ### Explicit evaluations of `B₃` and `B₄` -/

/-- Bernoulli number `b₃ = 0` (odd `> 1`), routed through `bernoulli'`. -/
theorem bernoulli_three_val : (bernoulli 3 : ℚ) = 0 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_three]

/-- Bernoulli number `b₄ = -1/30`, routed through `bernoulli'`. -/
theorem bernoulli_four_val : (bernoulli 4 : ℚ) = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

/-- `B₃(x) = x³ - (3/2)x² + (1/2)x`. -/
theorem bernoulli_eval_three' (x : ℚ) :
    (Polynomial.bernoulli 3).eval x = x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_three_val]; ring

/-- `B₄(x) = x⁴ - 2x³ + x² - 1/30`. -/
theorem bernoulli_eval_four' (x : ℚ) :
    (Polynomial.bernoulli 4).eval x = x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_three_val,
    bernoulli_four_val, Nat.choose]; ring

/-! ### Power-sum lemmas over ℚ (Faulhaber, degrees 1–4) -/

/-- Gauss sum over ℚ: `∑_{k<n} k = n(n-1)/2`. -/
theorem sum_range_id_rat (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Sum of squares over ℚ: `∑_{k<n} k² = n(n-1)(2n-1)/6`. -/
theorem sum_range_sq_rat (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) ^ 2 = (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Sum of cubes over ℚ (Nicomachus): `∑_{k<n} k³ = (n(n-1)/2)²`. -/
theorem sum_range_cube_rat (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) ^ 3 = ((n : ℚ) * ((n : ℚ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Sum of fourth powers over ℚ: `∑_{k<n} k⁴ = n(n-1)(2n-1)(3n²-3n-1)/30`. -/
theorem sum_range_quart_rat (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) ^ 4
      = (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1)
          * (3 * (n : ℚ) ^ 2 - 3 * (n : ℚ) - 1) / 30 := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-! ### The Raabe multiplication formula at `m = 3, 4` -/

/-- **Raabe, `m = 3`.**  `∑_{k<n} B₃(x + k/n) = (1/n²) · B₃(n x)` (since
`n^{1-3} = n⁻²`), for `n ≥ 1`.  Reduces to the power sums `∑k, ∑k², ∑k³`. -/
theorem raabe_three (x : ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (Polynomial.bernoulli 3).eval (x + (k : ℚ) / (n : ℚ))
      = (1 / (n : ℚ) ^ 2) * (Polynomial.bernoulli 3).eval ((n : ℚ) * x) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [bernoulli_eval_three']
  have hexp : ∀ k : ℕ,
      (x + (k : ℚ) / (n : ℚ)) ^ 3 - 3 / 2 * (x + (k : ℚ) / (n : ℚ)) ^ 2
          + 1 / 2 * (x + (k : ℚ) / (n : ℚ))
        = (x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x)
          + (3 * x ^ 2 - 3 * x + 1 / 2) / (n : ℚ) * (k : ℚ)
          + (3 * x - 3 / 2) / (n : ℚ) ^ 2 * (k : ℚ) ^ 2
          + (1 / (n : ℚ) ^ 3) * (k : ℚ) ^ 3 := by
    intro k; field_simp; ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_range_id_rat, sum_range_sq_rat, sum_range_cube_rat]
  field_simp
  ring

/-- **Raabe, `m = 4`.**  `∑_{k<n} B₄(x + k/n) = (1/n³) · B₄(n x)` (since
`n^{1-4} = n⁻³`), for `n ≥ 1`.  Reduces to the power sums `∑k, ∑k², ∑k³, ∑k⁴`. -/
theorem raabe_four (x : ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (Polynomial.bernoulli 4).eval (x + (k : ℚ) / (n : ℚ))
      = (1 / (n : ℚ) ^ 3) * (Polynomial.bernoulli 4).eval ((n : ℚ) * x) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [bernoulli_eval_four']
  have hexp : ∀ k : ℕ,
      (x + (k : ℚ) / (n : ℚ)) ^ 4 - 2 * (x + (k : ℚ) / (n : ℚ)) ^ 3
          + (x + (k : ℚ) / (n : ℚ)) ^ 2 - 1 / 30
        = (x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30)
          + (4 * x ^ 3 - 6 * x ^ 2 + 2 * x) / (n : ℚ) * (k : ℚ)
          + (6 * x ^ 2 - 6 * x + 1) / (n : ℚ) ^ 2 * (k : ℚ) ^ 2
          + (4 * x - 2) / (n : ℚ) ^ 3 * (k : ℚ) ^ 3
          + (1 / (n : ℚ) ^ 4) * (k : ℚ) ^ 4 := by
    intro k; field_simp; ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_range_id_rat, sum_range_sq_rat, sum_range_cube_rat, sum_range_quart_rat]
  field_simp
  ring

/-! ### Sanity checks -/

/-- Raabe `m = 3` at `x = 0`, `n = 2`:  `∑_{k<2} B₃(k/2) = (1/4)·B₃(0)`.
Both sides equal `0`. -/
example : ∑ k ∈ range 2, (Polynomial.bernoulli 3).eval ((k : ℚ) / 2)
    = (1 / (2 : ℚ) ^ 2) * (Polynomial.bernoulli 3).eval 0 := by
  have h := raabe_three 0 2 (by norm_num)
  simpa using h

/-- Raabe `m = 4` at `x = 0`, `n = 2`:  `∑_{k<2} B₄(k/2) = (1/8)·B₄(0)`.
Both sides equal `-1/240`. -/
example : ∑ k ∈ range 2, (Polynomial.bernoulli 4).eval ((k : ℚ) / 2)
    = (1 / (2 : ℚ) ^ 3) * (Polynomial.bernoulli 4).eval 0 := by
  have h := raabe_four 0 2 (by norm_num)
  simpa using h

end HermiteSawtoothIdentityOQ01OQ03
