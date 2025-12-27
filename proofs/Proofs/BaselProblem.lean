import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# The Basel Problem: ∑ 1/n² = π²/6

## What This Proves
The sum of reciprocals of squares converges to π²/6:

  ∑_{n=1}^∞ 1/n² = π²/6

This is the famous Basel Problem, named after the Swiss city where the Bernoulli
family lived. It was first posed by Pietro Mengoli in 1650 and solved by
Leonhard Euler in 1734, launching his illustrious career.

This is Wiedijk's 100 Theorems #14.

## Approach
- **Foundation (from Mathlib):** We use `hasSum_zeta_two` from
  `Mathlib.NumberTheory.ZetaValues` which proves the Basel identity using
  the theory of Bernoulli polynomials and Fourier analysis.
- **Convergence:** The series converges as a p-series with p = 2 > 1.
- **Historical Context:** Euler's original proof used a clever factorization
  of sin(x)/x, while modern proofs use Fourier series or complex analysis.

## Historical Note
The Basel Problem stumped mathematicians for nearly a century. Euler's solution
in 1734 made him famous throughout Europe at age 27. He later generalized this
to find ζ(2k) for all positive integers k, showing they are rational multiples
of π^(2k).

The result connects to:
- The Riemann zeta function: ζ(2) = π²/6
- Parseval's theorem in Fourier analysis
- The Weierstrass factorization of sin(x)

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical documentation
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `hasSum_zeta_two` : The Basel identity ∑ 1/n² = π²/6
- `Real.summable_nat_rpow_inv` : p-series convergence for p > 1
- `hasSum_zeta_nat` : General formula for ζ(2k)

Original formalization for Lean Genius.
-/

namespace BaselProblem

open Finset BigOperators Filter Topology Real

/-! ## The Main Theorem: Basel Identity

Euler's famous result that the sum of reciprocal squares equals π²/6. -/

/-- **The Basel Problem (Wiedijk #14)**

The infinite sum ∑_{n=1}^∞ 1/n² = π²/6.

This is Euler's celebrated solution to the Basel Problem from 1734.
The proof in Mathlib uses the theory of Bernoulli polynomials and
their connection to zeta values through Fourier analysis. -/
theorem basel_hasSum : HasSum (fun n : ℕ => 1 / (n : ℝ)^2) (π^2 / 6) := by
  exact hasSum_zeta_two

/-- The tsum version: ∑' n, 1/n² = π²/6 -/
theorem basel_tsum : ∑' n : ℕ, (1 : ℝ) / n^2 = π^2 / 6 :=
  basel_hasSum.tsum_eq

/-! ## Series Convergence

The series converges because it's a p-series with p = 2 > 1. -/

/-- The series 1/n² is summable (convergent). -/
theorem summable_one_div_sq : Summable (fun n : ℕ => (1 : ℝ) / n^2) := by
  have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
  convert h using 1
  ext n
  simp [rpow_natCast, div_eq_mul_inv]

/-- Alternative formulation using n⁻² -/
theorem summable_nat_sq_inv : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) := by
  convert summable_one_div_sq using 1
  ext n
  simp [div_eq_mul_inv]

/-! ## Basic Properties

Some simple facts about the series and its value. -/

/-- Each term 1/n² is positive for n > 0. -/
theorem one_div_sq_pos (n : ℕ) (hn : n ≠ 0) : (0 : ℝ) < 1 / n^2 := by
  positivity

/-- Each term 1/n² is nonnegative. -/
theorem one_div_sq_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 / n^2 := by
  positivity

/-- The value π²/6 is positive. -/
theorem basel_value_pos : π^2 / 6 > 0 := by positivity

/-! ## Historical Context: Euler's Original Approach

Euler's 1734 proof used the Weierstrass factorization of sin(x)/x:

  sin(x)/x = (1 - x²/π²)(1 - x²/4π²)(1 - x²/9π²)...

Expanding and comparing the coefficient of x² gives:
  -1/6 = -(1/π² + 1/4π² + 1/9π² + ...)

Therefore:
  1/π² + 1/4π² + 1/9π² + ... = 1/6
  ∑ 1/n² = π²/6

This "proof" was initially not rigorous by modern standards, but Euler's
intuition was correct. The result was later proved rigorously using
complex analysis and Fourier series. -/

/-! ## Connection to Other Zeta Values

Euler also found ζ(4) = π⁴/90, ζ(6) = π⁶/945, and more generally that
ζ(2k) is a rational multiple of π^(2k) involving Bernoulli numbers. -/

/-- ζ(4) = π⁴/90 -/
theorem zeta_four_hasSum : HasSum (fun n : ℕ => 1 / (n : ℝ)^4) (π^4 / 90) := by
  exact hasSum_zeta_four

/-- The general pattern: ζ(2k) involves Bernoulli numbers.

For even positive integers 2k, we have:
  ζ(2k) = (-1)^(k+1) · 2^(2k-1) · π^(2k) · B_{2k} / (2k)!

where B_{2k} is the 2k-th Bernoulli number. -/
theorem zeta_general (k : ℕ) (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ)^(2*k))
      ((-1)^(k+1) * 2^(2*k-1) * π^(2*k) * bernoulli (2*k) / (2*k).factorial) := by
  exact hasSum_zeta_nat hk

/-! ## Numerical Approximation

The value π²/6 ≈ 1.6449340668...

Partial sums converge relatively quickly:
- ∑_{n=1}^{10} 1/n² ≈ 1.5498
- ∑_{n=1}^{100} 1/n² ≈ 1.6350
- ∑_{n=1}^{1000} 1/n² ≈ 1.6439
-/

/-- The first partial sum: 1/1² = 1 -/
example : ∑ n ∈ Finset.range 2, (1 : ℝ) / n^2 = 1 := by
  simp [Finset.sum_range_succ]

/-- The series starts with 0 + 1 + 1/4 + ... (0 for n=0) -/
example : (fun n : ℕ => (1 : ℝ) / n^2) 0 = 0 := by simp
example : (fun n : ℕ => (1 : ℝ) / n^2) 1 = 1 := by simp
example : (fun n : ℕ => (1 : ℝ) / n^2) 2 = 1/4 := by norm_num

end BaselProblem
