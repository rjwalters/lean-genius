/-
# Chebyshev's θ function is bounded by n · log 4

Chebyshev's first function is
  θ(n) = ∑_{p ≤ n, p prime} log p .
The exponential of θ(n) is exactly the primorial `n# = ∏_{p ≤ n} p`, so
  θ(n) = log(n#).
Mathlib packages the central-binomial sandwich argument as
`primorial_le_4_pow : n# ≤ 4ⁿ`.  Taking logarithms and using monotonicity of
`log` on the positive reals turns that bound into the sharp Chebyshev estimate
  θ(n) ≤ n · log 4 = 2 n · log 2 .

This is the upper half of the classical Chebyshev bounds on θ, obtained here
directly from the primorial bound (whose proof is the Erdős central-binomial
sandwich `n# ∣ m# · C(m+n, m)`).

Reference: parent gallery entry "Two-Sided Central Binomial Bound
4ⁿ/(2n+1) ≤ C(2n,n) ≤ 4ⁿ" (chebyshev-bounds-oq-06).
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace ChebyshevThetaBound

/-- Chebyshev's first function `θ(n) = ∑_{p ≤ n, p prime} log p`, as a real number. -/
noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
  ∑ p ∈ range (n + 1) with p.Prime, Real.log p

/-- `θ(n)` is the logarithm of the primorial `n#`: exponentiating the Chebyshev
sum recovers the product of primes up to `n`. -/
theorem chebyshevTheta_eq_log_primorial (n : ℕ) :
    chebyshevTheta n = Real.log (primorial n) := by
  rw [chebyshevTheta, primorial, Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (mem_filter.1 hp).2.pos.ne'

/-- Every summand `log p` (with `p` prime, hence `p ≥ 2`) is nonnegative, so
`θ(n) ≥ 0`. -/
theorem chebyshevTheta_nonneg (n : ℕ) : 0 ≤ chebyshevTheta n := by
  apply Finset.sum_nonneg
  intro p hp
  exact Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le)

/-- `θ` is monotone: adjoining more primes only adds nonnegative terms. -/
theorem chebyshevTheta_mono {m n : ℕ} (h : m ≤ n) :
    chebyshevTheta m ≤ chebyshevTheta n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx.1) (by omega)), hx.2⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le)

/-- **Chebyshev upper bound.** `θ(n) ≤ n · log 4`, obtained by taking logarithms
in the primorial bound `n# ≤ 4ⁿ` (the central-binomial sandwich). -/
theorem chebyshevTheta_le (n : ℕ) : chebyshevTheta n ≤ n * Real.log 4 := by
  rw [chebyshevTheta_eq_log_primorial]
  calc
    Real.log (primorial n) ≤ Real.log ((4 : ℝ) ^ n) := by
      apply Real.log_le_log (by exact_mod_cast primorial_pos n)
      exact_mod_cast primorial_le_4_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]

/-- Restated with `log 4 = 2 · log 2`: `θ(n) ≤ 2 n · log 2`. -/
theorem chebyshevTheta_le_two_mul (n : ℕ) :
    chebyshevTheta n ≤ 2 * n * Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  calc
    chebyshevTheta n ≤ n * Real.log 4 := chebyshevTheta_le n
    _ = 2 * n * Real.log 2 := by rw [h4]; ring

end ChebyshevThetaBound
