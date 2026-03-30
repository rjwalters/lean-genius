/-
# Erdős Problem #1053: Growth Rate of k-Perfect Numbers

A number n is k-perfect if σ(n) = k·n, where σ is the sum-of-divisors function.
Must k = o(log log n) for k-perfect numbers?

## Background
- k=1: only n=1
- k=2: perfect numbers (6, 28, 496, 8128, ...)
- k=3: triperfect (120, 672, 523776, ...)
- Largest known k: k=11

## Key Question
If σ(n) = k·n, must k grow slower than log log n?
Equivalently, is σ(n)/n = o(log log n)?

## Related
Guy suggested finitely many k-perfect numbers for each k ≥ 3.

## Status: OPEN
Guy's Problem B2.

Reference: https://erdosproblems.com/1053
-/

import Mathlib

/- ## Core Definitions -/

-- euler_even_perfect: unused axiom removed (never referenced by any theorem)
theorem triperfect_examples :
    IsKPerfect 120 3 ∧ IsKPerfect 672 3 ∧ IsKPerfect 523776 3 := by
  native_decide

-- largest_known_k: unused axiom removed (never referenced by any theorem)
-- erdos_1053_conjecture: unused axiom removed (never referenced by any theorem)
-- gronwall_bound: unused axiom removed (never referenced by any theorem)
axiom robin_inequality_conditional (n : ℕ) (hn : n ≥ 5041) :
    -- Assuming RH
    (sigma n : ℝ) < Real.exp 0.5772 * (n : ℝ) * Real.log (Real.log (n : ℝ))

/- ## Guy's Finiteness Conjecture -/

-- guy_finiteness_conjecture: unused axiom removed (never referenced by any theorem)
theorem robin_gives_O_bound (n k : ℕ) (hn : n ≥ 5041)
    (hkp : IsKPerfect n k) :
    (k : ℝ) < Real.exp 0.5772 * Real.log (Real.log (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hrobin := robin_inequality_conditional n hn
  -- Cast σ(n) = k * n to ℝ
  have hσ_cast : (sigma n : ℝ) = (k : ℝ) * (n : ℝ) := by exact_mod_cast hkp.2
  -- k = σ(n) / n
  have hk_eq : (k : ℝ) = (sigma n : ℝ) / (n : ℝ) := by
    rw [hσ_cast]; field_simp
  -- σ(n)/n < exp(γ) * n * log(log n) / n = exp(γ) * log(log n)
  rw [hk_eq, div_lt_iff₀ hn_pos]
  have : Real.exp 0.5772 * Real.log (Real.log (n : ℝ)) * (n : ℝ) =
      Real.exp 0.5772 * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring
  linarith
