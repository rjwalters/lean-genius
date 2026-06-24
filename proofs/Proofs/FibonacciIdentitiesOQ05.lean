import Mathlib

/-!
# The Fibonacci staircase: partial sums of consecutive products

Mathlib's `Nat.fib` library records the pointwise product identities — the
recurrence `Nat.fib_add_two`, Cassini (`Int.fib_succ_mul_fib_pred_sub_fib_sq`),
Catalan, the addition formula — and the sibling gallery entry
`FibonacciIdentities` adds the **sum-of-squares** identity
`F₀² + ⋯ + Fₙ² = Fₙ·Fₙ₊₁`. What is missing is the *product* analogue: the
partial sum of **consecutive products** `Fₖ·Fₖ₊₁`.

The closed form is parity-governed. Writing `S(m) = Σ_{k=0}^{m} Fₖ·Fₖ₊₁`
(the `k = 0` term `F₀·F₁ = 0` is harmless, so this equals the classical
`F₁F₂ + ⋯ + Fₘ·Fₘ₊₁`):

* `S(m) = Fₘ₊₁² − 1` when `m` is **even**;
* `S(m) = Fₘ₊₁²` when `m` is **odd**.

The two cases differ by the alternating Cassini sign, and that is exactly the
engine of the proof. The clean way to package both at once is

    2·S(m) = 2·Fₘ₊₁² − (1 + (−1)ᵐ),                       (`two_mul_fib_sum_consec_prod`)

a single integer identity proved by one induction whose only arithmetic input
is the Cassini determinant `Fₘ₊₁² − Fₘ·Fₘ₊₂ = (−1)ᵐ` (`fib_det`). The unified
`if`-form `fib_sum_consec_prod` and the two natural-number corollaries
`fib_sum_consec_prod_even` / `fib_sum_consec_prod_odd` follow by a parity split.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ05

open Finset

/-- **Cassini determinant (reduced form).** For every `n`,
`Fₙ₊₁² − Fₙ·Fₙ₊₂ = (−1)ⁿ`. This is Cassini's identity arranged so the
alternating sign sits alone on the right; it is the single arithmetic fact that
drives the staircase sum. Proved by induction with only the recurrence
`Nat.fib_add_two`. -/
theorem fib_det (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => norm_num [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ k ih =>
    have e2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := k)
    have e3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + Nat.fib (k + 2) := by
      exact_mod_cast Nat.fib_add_two (n := k + 1)
    show (Nat.fib (k + 2) : ℤ) ^ 2 - (Nat.fib (k + 1) : ℤ) * Nat.fib (k + 3) = (-1) ^ (k + 1)
    rw [e2] at ih
    rw [e3, e2, pow_succ]
    linear_combination (-1 : ℤ) * ih

/-- **The staircase engine.** Over `ℤ`, doubling clears the parity defect:

    2·(F₀·F₁ + F₁·F₂ + ⋯ + Fₘ·Fₘ₊₁) = 2·Fₘ₊₁² − (1 + (−1)ᵐ).

One induction; the successor step is `linear_combination 2 · fib_det k`. -/
theorem two_mul_fib_sum_consec_prod (m : ℕ) :
    2 * (∑ i ∈ Finset.range (m + 1), (Nat.fib i : ℤ) * Nat.fib (i + 1))
      = 2 * (Nat.fib (m + 1) : ℤ) ^ 2 - (1 + (-1) ^ m) := by
  induction m with
  | zero => norm_num [Finset.sum_range_one, Nat.fib_zero, Nat.fib_one]
  | succ k ih =>
    have r2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := k)
    have r1 : (Nat.fib (k + 1 + 1) : ℤ) = (Nat.fib k : ℤ) + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := k)
    -- Cassini, with `F_{k+2}` already expanded into `F_k + F_{k+1}`.
    have hdet : (Nat.fib (k + 1) : ℤ) ^ 2
        - (Nat.fib k : ℤ) * ((Nat.fib k : ℤ) + Nat.fib (k + 1)) = (-1) ^ k := by
      have h := fib_det k; rwa [r2] at h
    rw [Finset.sum_range_succ, mul_add, ih, r1]
    linear_combination 2 * hdet

/-- **Closed form (unified `if`-form).**

    F₀·F₁ + F₁·F₂ + ⋯ + Fₘ·Fₘ₊₁ = Fₘ₊₁² − (1 if `m` even, else 0).

Equivalently `Fₘ₊₁²` for odd `m` and `Fₘ₊₁² − 1` for even `m`. -/
theorem fib_sum_consec_prod (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (Nat.fib i : ℤ) * Nat.fib (i + 1))
      = (Nat.fib (m + 1) : ℤ) ^ 2 - (if Even m then 1 else 0) := by
  have h := two_mul_fib_sum_consec_prod m
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow] at h
    rw [if_pos he]; linarith
  · rw [ho.neg_one_pow] at h
    rw [if_neg (Nat.not_even_iff_odd.mpr ho)]; linarith

/-- **Odd case (over `ℕ`).** For odd `m`, the staircase sum is a perfect
square: `F₁·F₂ + ⋯ + Fₘ·Fₘ₊₁ = Fₘ₊₁²`. -/
theorem fib_sum_consec_prod_odd (m : ℕ) (hm : Odd m) :
    ∑ i ∈ Finset.range (m + 1), Nat.fib i * Nat.fib (i + 1) = Nat.fib (m + 1) ^ 2 := by
  have h := fib_sum_consec_prod m
  rw [if_neg (Nat.not_even_iff_odd.mpr hm), sub_zero] at h
  exact_mod_cast h

/-- **Even case (over `ℕ`).** For even `m`, the staircase sum is one short of a
perfect square: `(F₁·F₂ + ⋯ + Fₘ·Fₘ₊₁) + 1 = Fₘ₊₁²`. -/
theorem fib_sum_consec_prod_even (m : ℕ) (hm : Even m) :
    (∑ i ∈ Finset.range (m + 1), Nat.fib i * Nat.fib (i + 1)) + 1 = Nat.fib (m + 1) ^ 2 := by
  have h := fib_sum_consec_prod m
  rw [if_pos hm] at h
  have key : (↑(∑ i ∈ Finset.range (m + 1), Nat.fib i * Nat.fib (i + 1)) : ℤ) + 1
      = (Nat.fib (m + 1) : ℤ) ^ 2 := by push_cast; linarith
  exact_mod_cast key

/-! ## Concrete values (the first few staircase sums) -/

-- m = 3 (odd): F₁F₂ + F₂F₃ + F₃F₄ = 1 + 2 + 6 = 9 = F₄² = 3².
example : ∑ i ∈ Finset.range 4, Nat.fib i * Nat.fib (i + 1) = 9 := by decide

-- m = 4 (even): + F₄F₅ = 9 + 15 = 24 = F₅² − 1 = 25 − 1.
example : ∑ i ∈ Finset.range 5, Nat.fib i * Nat.fib (i + 1) = 24 := by decide

-- m = 5 (odd): + F₅F₆ = 24 + 40 = 64 = F₆² = 8².
example : ∑ i ∈ Finset.range 6, Nat.fib i * Nat.fib (i + 1) = 64 := by decide

end FibonacciIdentitiesOQ05
