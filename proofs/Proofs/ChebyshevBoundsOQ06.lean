import Mathlib

/-
# Two-sided central binomial coefficient bound

The central binomial coefficient `C(2n, n) = Nat.centralBinom n` satisfies the
elementary sandwich
$$ \frac{4^n}{2n+1} \;\le\; \binom{2n}{n} \;\le\; 4^n. $$

This is the workhorse estimate behind Chebyshev-type prime-counting bounds: the
upper bound feeds the bound on `θ(n)`, and the lower bound forces enough prime
factors into `C(2n, n)` to drive the lower estimate on `π(n)`.

This is a **routine assembly** of existing Mathlib primitives into a single named
two-sided estimate (with quotient and real-valued forms), to serve as an axiom-free
building block for the axiomatized parent `chebyshev-bounds`. Neither bound is new:

* **Lower bound** `4 ^ n ≤ (2n + 1) · centralBinom n`: this *is* Mathlib's
  `Nat.four_pow_le_two_mul_add_one_mul_central_binom` (proved there from
  `(1+1)^(2n) = Σ C(2n, m)` with the middle term largest); we just record it in
  `centralBinom` notation.

* **Upper bound** `centralBinom n ≤ 4 ^ n`: a one-line corollary of
  `Nat.choose_le_two_pow` (`C(m, k) ≤ 2 ^ m`) at row `m = 2n`, giving
  `C(2n, n) ≤ 2 ^ (2n) = 4 ^ n`. (Mathlib records the analogous `choose_middle_le_pow`
  for the *odd* row `C(2n+1, n) ≤ 4 ^ n`, but not this even-row form.)

The packaging value is the unified `centralBinom_sandwich`, the literal quotient form
`4 ^ n / (2n + 1) ≤ C(2n, n)` (truncated `ℕ`-division), and the real-valued sandwich.

No axioms, no `sorry`, no `native_decide`.
-/

namespace ChebyshevBoundsOQ06

open Nat

/-- **Upper bound.** The central binomial coefficient is at most `4 ^ n`.
`C(2n, n) ≤ 2 ^ (2n) = 4 ^ n`, since any entry of row `2n` of Pascal's triangle
is bounded by the row sum `2 ^ (2n)`. -/
theorem centralBinom_le_four_pow (n : ℕ) : centralBinom n ≤ 4 ^ n := by
  have h : (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow (2 * n) n
  calc centralBinom n = (2 * n).choose n := Nat.centralBinom_eq_two_mul_choose n
    _ ≤ 2 ^ (2 * n) := h
    _ = 4 ^ n := by rw [pow_mul]; norm_num

/-- **Lower bound (product form).** `4 ^ n ≤ (2n + 1) · C(2n, n)` for every `n`.
This is Mathlib's `Nat.four_pow_le_two_mul_add_one_mul_central_binom`, restated with
`centralBinom n` in place of `(2 * n).choose n` (the two are definitionally equal).
Stated multiplicatively to avoid truncated division. -/
theorem four_pow_le_succ_two_mul_mul_centralBinom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * centralBinom n := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact Nat.four_pow_le_two_mul_add_one_mul_central_binom n

/-- **Lower bound (quotient form).** The literal statement `4 ^ n / (2n + 1) ≤ C(2n, n)`,
with truncated natural-number division. Immediate from the product form. -/
theorem four_pow_div_succ_two_mul_le_centralBinom (n : ℕ) :
    4 ^ n / (2 * n + 1) ≤ centralBinom n := by
  apply Nat.div_le_of_le_mul
  exact four_pow_le_succ_two_mul_mul_centralBinom n

/-- **The two-sided sandwich, product form.** Combines both bounds into the single
statement `4 ^ n ≤ (2n + 1) · C(2n, n)` and `C(2n, n) ≤ 4 ^ n`. -/
theorem centralBinom_sandwich (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * centralBinom n ∧ centralBinom n ≤ 4 ^ n :=
  ⟨four_pow_le_succ_two_mul_mul_centralBinom n, centralBinom_le_four_pow n⟩

/-- **The two-sided sandwich, real-valued quotient form.**
`(4 ^ n) / (2n + 1) ≤ C(2n, n) ≤ 4 ^ n` as an inequality of real numbers, so the
division is the genuine quotient rather than its `ℕ`-truncation. -/
theorem centralBinom_real_sandwich (n : ℕ) :
    (4 : ℝ) ^ n / (2 * n + 1) ≤ (centralBinom n : ℝ) ∧
      (centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h := four_pow_le_succ_two_mul_mul_centralBinom n
    have hcast : ((4 ^ n : ℕ) : ℝ) ≤ (((2 * n + 1) * centralBinom n : ℕ) : ℝ) :=
      Nat.cast_le.mpr h
    push_cast at hcast
    linarith
  · have h := centralBinom_le_four_pow n
    have hcast : ((centralBinom n : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := Nat.cast_le.mpr h
    push_cast at hcast
    linarith

end ChebyshevBoundsOQ06
