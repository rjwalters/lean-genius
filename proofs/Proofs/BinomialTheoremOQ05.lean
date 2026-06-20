/-
# Bernoulli's Inequality: `1 + n·a ≤ (1 + a)ⁿ`

**Open Question (binomial-theorem-oq-05).** The binomial theorem expands
`(1 + a)ⁿ = ∑ₖ C(n,k) aᵏ` as a sum of `n + 1` nonnegative-degree terms. Keeping
only the first two terms `1 + n·a` gives the *first-order lower bound* on a
binomial power — **Bernoulli's inequality**:

  `1 + n·a ≤ (1 + a)ⁿ`  for every real `a ≥ -2` and `n : ℕ`.

It is the workhorse linear estimate behind growth of geometric powers, the
divergence of `(1 + a)ⁿ` for `a > 0`, the AM–GM inequality, and the convergence
of `(1 + x/n)ⁿ → eˣ`.

**What this file proves.**
- `bernoulli` — the inequality for `a ≥ -2` (Mathlib's `one_add_mul_le_pow`).
- `bernoulli_nonneg` — the classical textbook form for `a ≥ 0`.
- `bernoulli_strict` — the **strict** inequality `1 + n·a < (1 + a)ⁿ` for `a > 0`
  and `n ≥ 2`, proved here by induction (Mathlib has no integer-power strict
  version; only an `rpow` analogue).
- `bernoulli_pow` — the `aⁿ` reformulation `1 + n·(a − 1) ≤ aⁿ` for `a ≥ -1`.
- `one_add_pow_tendsto_atTop` — `(1 + a)ⁿ → ∞` for `a > 0`, the qualitative
  consequence, together with the explicit linear rate from `bernoulli`.
- Numeric witnesses.

All results are fully verified: 0 sorries, 0 axioms.

The base estimate `bernoulli` is a thin wrapper over Mathlib's
`one_add_mul_le_pow`; the strict inequality and the packaging of the divergence
statement with an explicit rate are the original content.
-/
import Mathlib

namespace BinomialTheoremOQ05

/-- **Bernoulli's inequality.** For any real `a ≥ -2` and any `n : ℕ`,
`1 + n·a ≤ (1 + a)ⁿ`. This is the first-order truncation of the binomial
expansion of `(1 + a)ⁿ`. -/
theorem bernoulli {a : ℝ} (ha : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow ha n

/-- The classical textbook form: for `a ≥ 0` the hypothesis `a ≥ -2` is automatic. -/
theorem bernoulli_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow (by linarith) n

/-- **Strict Bernoulli inequality.** For `a > 0` and `n ≥ 2`, the inequality is
strict: `1 + n·a < (1 + a)ⁿ`. The gap is the discarded quadratic term `C(n,2) a²`
of the binomial expansion, which is positive once `n ≥ 2` and `a > 0`.

Mathlib provides only an `rpow` strict version (`one_add_mul_self_lt_rpow_one_add`);
this `ℕ`-power statement is proved here directly by induction. -/
theorem bernoulli_strict {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) :
    1 + n * a < (1 + a) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      -- `(1 + a)² = 1 + 2a + a²` and `a² > 0`.
      have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h2, sq]
      nlinarith [mul_pos ha ha]
  | succ m hm ih =>
      have h1a : (0 : ℝ) < 1 + a := by linarith
      -- `(1 + a)^(m+1) = (1 + a) · (1 + a)^m > (1 + a) · (1 + m·a)`.
      have step : (1 + a) * (1 + (m : ℝ) * a) < (1 + a) * (1 + a) ^ m :=
        mul_lt_mul_of_pos_left ih h1a
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [pow_succ']
      push_cast
      -- `(1 + a)·(1 + m·a) = 1 + (m+1)·a + m·a² ≥ 1 + (m+1)·a`.
      nlinarith [step, mul_nonneg hmnn (mul_pos ha ha).le]

/-- **Bernoulli's inequality, `aⁿ` form.** For `a ≥ -1`, `1 + n·(a − 1) ≤ aⁿ`.
The tangent line to `t ↦ tⁿ` at `t = 1` lies below the curve. -/
theorem bernoulli_pow {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : 1 + n * (a - 1) ≤ a ^ n :=
  one_add_mul_sub_le_pow ha n

/-- Powers of a base `≥ 1` grow at least linearly: `aⁿ ≥ 1 + n·(a − 1)`. -/
theorem pow_ge_linear_of_one_le {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    1 + n * (a - 1) ≤ a ^ n :=
  one_add_mul_sub_le_pow (by linarith) n

/-- **Divergence of geometric powers.** For `a > 0`, `(1 + a)ⁿ → ∞`.
Bernoulli's inequality makes this quantitative: `(1 + a)ⁿ ≥ 1 + n·a`, an
explicit linear lower bound that already forces divergence. -/
theorem one_add_pow_tendsto_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun n : ℕ => (1 + a) ^ n) Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by linarith)

/-- The explicit linear lower bound underlying the divergence above. -/
theorem one_add_pow_ge_one_add_nmul {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    1 + n * a ≤ (1 + a) ^ n :=
  bernoulli_nonneg ha n

/-! ## Numeric witnesses -/

/-- `(3/2)¹⁰ ≥ 1 + 10·(1/2) = 6` — Bernoulli supplies a lower bound without
evaluating the tenth power directly (the true value is `≈ 57.67`). -/
example : (1 : ℝ) + 10 * (1 / 2) ≤ (1 + 1 / 2) ^ 10 :=
  bernoulli (by norm_num) 10

/-- Strictness in action: `(1 + 1)⁵ = 32 > 1 + 5·1 = 6`. -/
example : (1 : ℝ) + 5 * 1 < (1 + 1) ^ 5 :=
  bernoulli_strict (by norm_num) (by norm_num)

/-- The lower bound also holds for `a` slightly above `-2`, e.g. `a = -3/2`:
`1 + 4·(−3/2) = −5 ≤ (−1/2)⁴ = 1/16`. -/
example : (1 : ℝ) + 4 * (-3 / 2) ≤ (1 + (-3 / 2)) ^ 4 :=
  bernoulli (by norm_num) 4

end BinomialTheoremOQ05
