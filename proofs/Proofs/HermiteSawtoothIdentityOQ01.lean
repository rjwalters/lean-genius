import Mathlib

/-
# Raabe Multiplication Formula for Bernoulli Polynomials (low orders)

## Open Question (hermite-sawtooth-identity-oq-01)

The parent entry `HermiteSawtoothIdentity` proves the `m = 1` *fractional-part*
sawtooth identity `∑_{k<n} {x + k/n} = {n x} + (n-1)/2`.  Its Bernoulli-polynomial
form is the `m = 1` case of the **Raabe multiplication theorem**

    `∑_{k=0}^{n-1} Bₘ(x + k/n) = n^{1-m} · Bₘ(n x)`,

where `Bₘ` is the `m`-th Bernoulli polynomial (`Polynomial.bernoulli`).  The full
theorem (general `m`) is classically proved through the exponential generating
function `t e^{xt}/(e^t - 1)` — heavy machinery in a formal setting.

This file proves the theorem for the **low orders** `m = 0, 1, 2`, where `n^{1-m}`
is a concrete coefficient (`n`, `1`, `1/n`) and the identity reduces to an
elementary power-sum computation.  For each order we evaluate `Bₘ` to its
explicit polynomial and close the sum with the Gauss / square power-sum formulas

* `∑_{k<n} k     = n(n-1)/2`        (`sum_range_id_rat`),
* `∑_{k<n} k²    = n(n-1)(2n-1)/6`  (`sum_range_sq_rat`).

The `m = 1` case (`raabe_one`) is the Bernoulli-polynomial twin of the parent
sawtooth identity, now with `n^{1-1} = 1`.

Everything is over ℚ, fully machine-checked, `0`-axiom.  Mathlib provides the
Bernoulli polynomials and `sum_bernoulli` but not the multiplication theorem.
-/

open Polynomial Finset

namespace HermiteSawtoothIdentityOQ01

/-! ### Explicit evaluations of the low Bernoulli polynomials -/

/-- `B₀(x) = 1`. -/
theorem bernoulli_eval_zero' (x : ℚ) : (Polynomial.bernoulli 0).eval x = 1 := by
  simp [Polynomial.bernoulli]

/-- `B₁(x) = x - 1/2`. -/
theorem bernoulli_eval_one' (x : ℚ) : (Polynomial.bernoulli 1).eval x = x - 1 / 2 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ]; ring

/-- `B₂(x) = x² - x + 1/6`. -/
theorem bernoulli_eval_two' (x : ℚ) :
    (Polynomial.bernoulli 2).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ]; ring

/-! ### Power-sum lemmas over ℚ -/

/-- Gauss sum over ℚ: `∑_{k<n} k = n(n-1)/2`. -/
theorem sum_range_id_rat (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- Sum of squares over ℚ: `∑_{k<n} k² = n(n-1)(2n-1)/6`. -/
theorem sum_range_sq_rat (n : ℕ) :
    ∑ k ∈ range n, (k : ℚ) ^ 2 = (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-! ### The Raabe multiplication formula at `m = 0, 1, 2` -/

/-- **Raabe, `m = 0`.**  `∑_{k<n} B₀(x + k/n) = n · B₀(n x)`, i.e. `n^{1-0} = n`.
Both sides are `n`. -/
theorem raabe_zero (x : ℚ) (n : ℕ) :
    ∑ k ∈ range n, (Polynomial.bernoulli 0).eval (x + (k : ℚ) / (n : ℚ))
      = (n : ℚ) * (Polynomial.bernoulli 0).eval ((n : ℚ) * x) := by
  simp only [bernoulli_eval_zero']
  simp

/-- **Raabe, `m = 1`.**  `∑_{k<n} B₁(x + k/n) = B₁(n x)` (since `n^{1-1} = 1`).
The Bernoulli-polynomial form of the parent sawtooth identity. -/
theorem raabe_one (x : ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (Polynomial.bernoulli 1).eval (x + (k : ℚ) / (n : ℚ))
      = (Polynomial.bernoulli 1).eval ((n : ℚ) * x) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [bernoulli_eval_one', Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.sum_div, sum_range_id_rat]
  field_simp
  ring

/-- **Raabe, `m = 2`.**  `∑_{k<n} B₂(x + k/n) = (1/n) · B₂(n x)` (since
`n^{1-2} = n⁻¹`), for `n ≥ 1`. -/
theorem raabe_two (x : ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (Polynomial.bernoulli 2).eval (x + (k : ℚ) / (n : ℚ))
      = (1 / (n : ℚ)) * (Polynomial.bernoulli 2).eval ((n : ℚ) * x) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [bernoulli_eval_two']
  -- expand each square and split the sum into the three power sums
  have hexp : ∀ k : ℕ, (x + (k : ℚ) / (n : ℚ)) ^ 2 - (x + (k : ℚ) / (n : ℚ)) + 1 / 6
      = x ^ 2 - x + 1 / 6 + (2 * x - 1) / (n : ℚ) * (k : ℚ) + (1 / (n : ℚ) ^ 2) * (k : ℚ) ^ 2 := by
    intro k
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun k _ => hexp k)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_range_id_rat, sum_range_sq_rat]
  field_simp
  ring

end HermiteSawtoothIdentityOQ01
