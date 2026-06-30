/-
  Sharp Bound: (1 + 1/n)^n < e for All n ≥ 1

  OQ-03-OQ-02-OQ-03-OQ-01 derived from the exponential limit / monotonicity chain.

  **Main theorem**: For every n ≥ 1, the strict bound
      (1 + 1/n)^n < e
  holds. This sharpens the parent's (1+1/n)^n < 3 bound and complements both the
  limit (1+1/n)^n → e and the strict monotonicity result (parent OQ-03-OQ-02-OQ-03):
  the increasing sequence (1+1/n)^n approaches e strictly from below.

  **Proof strategy** (elementary, one-line core):
  1. For x > 0 and n ≥ 1, since x/n ≠ 0 we have the strict tangent bound
        1 + x/n < exp(x/n)      [Real.add_one_lt_exp]
  2. Both sides are positive; raising to the n-th power preserves strict order:
        (1 + x/n)^n < (exp(x/n))^n = exp(n · (x/n)) = exp(x).
  3. Specialize x = 1 to get (1 + 1/n)^n < exp 1 = e.

  We also record the elementary lower companion 2 ≤ (1+1/n)^n (Bernoulli), giving
  the two-sided bound 2 ≤ (1+1/n)^n < e for all n ≥ 1.

  **Key references**:
  - Parent: BinomialTheoremOQ03OQ02OQ03 (strict monotonicity of (1+1/n)^n)
  - Grandparent: BinomialTheoremOQ03OQ02 (limit (1+1/n)^n → e)
  - Classic: Rudin, Principles of Mathematical Analysis, Chapter 3

  **Axiom count**: 0
  **Sorry count**: 0
-/
import Mathlib

open Real

namespace SharpEulerBound

/-- General strict bound: for `x > 0` and `n ≥ 1`,
    `(1 + x/n)^n < exp x`.

    Core of the argument: `x/n ≠ 0`, so the strict tangent-line inequality
    `1 + x/n < exp(x/n)` holds; raising both (positive) sides to the `n`-th power
    and using `(exp (x/n))^n = exp (n · (x/n)) = exp x` gives the claim. -/
theorem add_div_pow_lt_exp (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    (1 + x / n) ^ n < Real.exp x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxn_ne : x / n ≠ 0 := div_ne_zero hx.ne' hn0.ne'
  -- Strict tangent bound 1 + x/n < exp(x/n).
  have hbase : 1 + x / n < Real.exp (x / n) := by
    have h := Real.add_one_lt_exp hxn_ne
    linarith
  have hbase_nonneg : (0 : ℝ) ≤ 1 + x / n := by positivity
  -- Raise to the n-th power (strict order preserved on nonnegatives).
  have hpow : (1 + x / n) ^ n < (Real.exp (x / n)) ^ n :=
    pow_lt_pow_left₀ hbase hbase_nonneg (by omega)
  -- (exp(x/n))^n = exp(n · (x/n)) = exp x.
  rw [← Real.exp_nat_mul] at hpow
  have hcancel : (n : ℝ) * (x / n) = x := by field_simp
  rwa [hcancel] at hpow

/-- **Main result**: `(1 + 1/n)^n < e` for all `n ≥ 1`. -/
theorem add_inv_pow_lt_e (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ n < Real.exp 1 := by
  simpa using add_div_pow_lt_exp 1 one_pos n hn

/-- Lower companion (Bernoulli): `2 ≤ (1 + 1/n)^n` for all `n ≥ 1`. -/
theorem two_le_add_inv_pow (n : ℕ) (hn : 1 ≤ n) :
    2 ≤ (1 + 1 / (n : ℝ)) ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hge : (-2 : ℝ) ≤ 1 / n := by
    have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have h := one_add_mul_le_pow hge n
  have hcancel : 1 + (n : ℝ) * (1 / n) = 2 := by
    rw [mul_one_div, div_self hn0.ne']; norm_num
  rw [hcancel] at h
  linarith

/-- Two-sided bound: `2 ≤ (1 + 1/n)^n < e` for all `n ≥ 1`.
    Together with the parent's strict monotonicity, the sequence increases
    strictly toward `e` while staying in `[2, e)`. -/
theorem add_inv_pow_bounds (n : ℕ) (hn : 1 ≤ n) :
    2 ≤ (1 + 1 / (n : ℝ)) ^ n ∧ (1 + 1 / (n : ℝ)) ^ n < Real.exp 1 :=
  ⟨two_le_add_inv_pow n hn, add_inv_pow_lt_e n hn⟩

end SharpEulerBound
