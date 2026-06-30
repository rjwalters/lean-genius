import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Tactic

/-!
# Derangements: the factorial-times-truncated-exponential closed form

## What This Proves

The number of derangements `numDerangements n` (permutations of an `n`-element set
with no fixed point — Mathlib's `numDerangements`) satisfies the classical closed
form, stated here over an **arbitrary characteristic-zero field** `𝕜`:

$$ D_n \;=\; n!\,\sum_{k=0}^{n} \frac{(-1)^k}{k!}. $$

The bracketed sum is the order-`n` truncation of the exponential series of `e^{-1}`,
so the identity says `D_n = n! · (\text{partial sum of } e^{-1})`.

## Why this is not already in Mathlib

Mathlib stores three *integer*/analytic facts about `numDerangements`:

* `numDerangements_sum` — an **ascending-factorial** integer sum
  `(D_n : ℤ) = ∑_{k} (-1)^k · ascFactorial (k+1) (n-k)`;
* `numDerangements_succ` — the integer recurrence `D_{n+1} = (n+1)·D_n - (-1)^n`;
* `numDerangements_tendsto_inv_e` — the asymptotic `D_n / n! → e^{-1}`.

The exact rational/field identity `D_n = n!·∑_{k≤n} (-1)^k/k!` appears only as an
*internal* `suffices` step buried inside the proof of `numDerangements_tendsto_inv_e`
(over `ℝ`); it is never exposed as a reusable lemma, and never over a general field.
This file states and proves it directly, by a single induction on the clean integer
recurrence `numDerangements_succ`, and specializes it to `ℚ` and `ℝ`.

## Approach

`numDerangements_succ` gives, after casting into `𝕜`,
`D_{n+1} = (n+1)·D_n - (-1)^n`.  Splitting off the last term of the sum with
`Finset.sum_range_succ` and using `(n+1)! = (n+1)·n!`, the inductive step is an
algebraic identity closed by `field_simp`/`ring`; characteristic zero is exactly
what makes the factorials invertible.

## Status
- [x] Complete proof (0 sorries, 0 axioms beyond Mathlib's foundations)
-/

namespace DerangementsOQ04

open Finset

/-- The order-`n` truncation of the exponential series of `e^{-1}`, in a field `𝕜`:
`truncExpNegOne 𝕜 n = ∑_{k=0}^{n-1} (-1)^k / k!`. We use the `range n` (not `range (n+1)`)
convention so that `truncExpNegOne 𝕜 (n+1)` is the sum through the `(-1)^n/n!` term. -/
def truncExpNegOne (𝕜 : Type*) [Field 𝕜] (n : ℕ) : 𝕜 :=
  ∑ k ∈ range n, (-1 : 𝕜) ^ k / (k.factorial : 𝕜)

/-- **Closed form for derangements over a characteristic-zero field.**

`(D_n : 𝕜) = n! · ∑_{k=0}^{n} (-1)^k / k!`, the factorial times the truncated
exponential series of `e^{-1}`. -/
theorem numDerangements_closed_form
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (n : ℕ) :
    (numDerangements n : 𝕜)
      = (n.factorial : 𝕜) * ∑ k ∈ range (n + 1), (-1 : 𝕜) ^ k / (k.factorial : 𝕜) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- factorial split  (n+1)! = (n+1)·n!  inside 𝕜
    have hfac : ((n + 1).factorial : 𝕜) = (↑n + 1) * (n.factorial : 𝕜) := by
      rw [Nat.factorial_succ]; push_cast; ring
    -- (n+1)! ≠ 0  in a characteristic-zero field
    have hne : ((n + 1).factorial : 𝕜) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + 1)
    -- the clean integer recurrence, cast into 𝕜
    have hrec : (numDerangements (n + 1) : 𝕜)
        = (↑n + 1) * (numDerangements n : 𝕜) - (-1) ^ n := by
      exact_mod_cast numDerangements_succ n
    -- peel off the last summand and reduce to an algebraic identity
    rw [Finset.sum_range_succ, hrec, ih, mul_add]
    field_simp
    rw [hfac]
    ring

/-- The truncated-exponential phrasing of the same identity:
`(D_n : 𝕜) = n! · truncExpNegOne 𝕜 (n+1)`. -/
theorem numDerangements_eq_factorial_mul_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (n : ℕ) :
    (numDerangements n : 𝕜) = (n.factorial : 𝕜) * truncExpNegOne 𝕜 (n + 1) := by
  rw [truncExpNegOne, numDerangements_closed_form]

/-- Closed form over the rationals. -/
theorem numDerangements_closed_form_rat (n : ℕ) :
    (numDerangements n : ℚ)
      = (n.factorial : ℚ) * ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / (k.factorial : ℚ) :=
  numDerangements_closed_form ℚ n

/-- Closed form over the reals. -/
theorem numDerangements_closed_form_real (n : ℕ) :
    (numDerangements n : ℝ)
      = (n.factorial : ℝ) * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k / (k.factorial : ℝ) :=
  numDerangements_closed_form ℝ n

/-- Dividing by `n!` recovers the partial sum of `e^{-1}` exactly:
`D_n / n! = ∑_{k=0}^{n} (-1)^k/k!`. This is the finite identity underlying
Mathlib's asymptotic `numDerangements_tendsto_inv_e`. -/
theorem numDerangements_div_factorial
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (n : ℕ) :
    (numDerangements n : 𝕜) / (n.factorial : 𝕜)
      = ∑ k ∈ range (n + 1), (-1 : 𝕜) ^ k / (k.factorial : 𝕜) := by
  have hne : (n.factorial : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [numDerangements_closed_form, mul_comm, mul_div_assoc, div_self hne, mul_one]

/-- Sanity check against small values: `D_4 = 9` is reproduced by the closed form.
`9 = 4! · (1 - 1 + 1/2 - 1/6 + 1/24) = 24 · 3/8`. -/
example : (numDerangements 4 : ℚ)
    = (Nat.factorial 4 : ℚ) * ∑ k ∈ range 5, (-1 : ℚ) ^ k / (k.factorial : ℚ) :=
  numDerangements_closed_form_rat 4

end DerangementsOQ04
