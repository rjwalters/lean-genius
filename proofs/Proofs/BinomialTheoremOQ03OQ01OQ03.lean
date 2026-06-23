/-
# The Vandermonde Convolution for Falling Factorials (OQ-03-OQ-01-OQ-03)

Research Question (follow-up to OQ-03-OQ-01 "Combinatorial Moments of the
Binomial Coefficients" and its sibling OQ-03-OQ-01-OQ-01, the general
falling-factorial moment).  The moment entries treat the falling factorial
`k^(r) = k(k-1)⋯(k-r+1) = Nat.descFactorial k r` as the natural weight against
the binomial coefficients.  The falling factorial has another binomial-flavoured
property — an *addition law* in its base.  Does the falling factorial obey a
Vandermonde-type convolution, the umbral analogue of the binomial theorem?

Answer.  Yes.  The falling factorial is a sequence *of binomial type*:

    (x + y)^(n) = Σ_{k=0}^{n} C(n,k) · x^(k) · y^(n-k)        (for all x, y, n : ℕ)

This is the **Vandermonde convolution for falling factorials** (the umbral, or
"Newton", binomial theorem).  Dividing both sides by `n!` collapses it to the
ordinary Chu–Vandermonde identity for binomial coefficients
`C(x+y, n) = Σ_k C(x,k)·C(y,n-k)`; the falling-factorial form is the
polynomial-level refinement that keeps the factorials uncancelled.  Mathlib has
the binomial Vandermonde (`Nat.add_choose_eq`, in antidiagonal form) but not its
falling-factorial lift, nor even the range form of Chu–Vandermonde.

The proof is the reduction just sketched, run in reverse.  Each falling factorial
is `m^(j) = j!·C(m,j)` (`Nat.descFactorial_eq_factorial_mul_choose`), so a single
summand carries the factor `C(n,k)·k!·(n-k)! = n!`
(`Nat.choose_mul_factorial_mul_factorial`, valid because `k ≤ n` throughout the
range).  Pulling that constant `n!` out of the sum leaves exactly
`n!·Σ_k C(x,k)·C(y,n-k) = n!·C(x+y,n) = (x+y)^(n)`, where the inner sum is
Chu–Vandermonde.  Everything stays in ℕ; the truncated subtraction in `n - k` is
harmless because `k` ranges only up to `n`.

Tags: combinatorics, binomial-coefficients, falling-factorial, Vandermonde,
Chu-Vandermonde, umbral-calculus, binomial-type, convolution
-/

import Mathlib

open Finset BigOperators

namespace BinomialTheoremOQ03OQ01OQ03

/-! ## Part I: Chu–Vandermonde in range form

Mathlib proves Vandermonde's identity as `Nat.add_choose_eq`, but only in
*antidiagonal* form `Σ_{(i,j) ∈ antidiagonal n} C(x,i)·C(y,j)`.  For an honest
"convolution over `range (n+1)`" we repackage it with
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`, which substitutes the unique
antidiagonal index `(k, n-k)`.  This range form is the engine of the main result
and is itself absent from Mathlib. -/

/-- **Chu–Vandermonde, range form.**  `C(x+y, n) = Σ_{k=0}^{n} C(x,k)·C(y,n-k)`.
The classical convolution of binomial coefficients, written as a sum over
`range (n+1)` rather than over the antidiagonal. -/
theorem add_choose_eq_sum_range (x y n : ℕ) :
    (x + y).choose n = ∑ k ∈ range (n + 1), x.choose k * y.choose (n - k) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-! ## Part II: The Vandermonde convolution for falling factorials -/

/-- **Vandermonde convolution for falling factorials.**  For all `x y n : ℕ`,
`(x + y)^(n) = Σ_{k=0}^{n} C(n,k) · x^(k) · y^(n-k)`, where `m^(j) =
Nat.descFactorial m j` is the falling factorial.  This is the umbral binomial
theorem: the falling factorial is a sequence of binomial type.

The proof rewrites every falling factorial as `m^(j) = j!·C(m,j)`, so each
summand acquires the constant factor `C(n,k)·k!·(n-k)! = n!`; pulling it out
reduces the statement to the binomial Chu–Vandermonde identity
(`add_choose_eq_sum_range`).  Holds unconditionally over ℕ — the truncated
subtraction in `n - k` is harmless since `k ≤ n` over the whole range. -/
theorem add_descFactorial_eq_sum (x y n : ℕ) :
    (x + y).descFactorial n
      = ∑ k ∈ range (n + 1), n.choose k * (x.descFactorial k * y.descFactorial (n - k)) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, add_choose_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    ← Nat.choose_mul_factorial_mul_factorial hk]
  ring

/-! ## Part III: Corollaries -/

/-- **Diagonal case `x = y`.**  `(2x)^(n) = Σ_{k=0}^{n} C(n,k) · x^(k) · x^(n-k)`.
The self-convolution of the falling factorial — the umbral analogue of the
duplication `(2x)ⁿ = Σ C(n,k) xᵏ xⁿ⁻ᵏ`. -/
theorem two_mul_descFactorial_eq_sum (x n : ℕ) :
    (2 * x).descFactorial n
      = ∑ k ∈ range (n + 1), n.choose k * (x.descFactorial k * x.descFactorial (n - k)) := by
  have h := add_descFactorial_eq_sum x x n
  rwa [two_mul]

/-- **The convolution is symmetric.**  Reindexing `k ↦ n-k` swaps the roles of
`x` and `y` in the falling-factorial Vandermonde, matching the symmetry
`(x+y)^(n) = (y+x)^(n)`.  Stated as the equality of the two convolutions. -/
theorem descFactorial_sum_comm (x y n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * (x.descFactorial k * y.descFactorial (n - k))
      = ∑ k ∈ range (n + 1), n.choose k * (y.descFactorial k * x.descFactorial (n - k)) := by
  rw [← add_descFactorial_eq_sum, ← add_descFactorial_eq_sum, Nat.add_comm]

/-- **Recovering the ordinary binomial theorem on the diagonal.**  Specialising
the binomial coefficient form: the zeroth case `n = 0` is `1`, and the first case
`n = 1` is the linear addition law `(x+y)^(1) = x + y`. -/
theorem descFactorial_one_add (x y : ℕ) :
    (x + y).descFactorial 1 = x.descFactorial 1 + y.descFactorial 1 := by
  simp

/-! ## Part IV: Sanity checks

Concrete instances verified by kernel `decide` (no `native_decide`, so these add
no axioms).  `Nat.descFactorial` is computable, so each side reduces to a literal. -/

-- (3+4)^(2) = 7·6 = 42 = Σ_{k=0}^{2} C(2,k)·3^(k)·4^(2-k)
example :
    (3 + 4).descFactorial 2
      = ∑ k ∈ range 3, (2).choose k * ((3 : ℕ).descFactorial k * (4 : ℕ).descFactorial (2 - k)) := by
  decide

-- order 3, mixed bases
example :
    (5 + 2).descFactorial 3
      = ∑ k ∈ range 4, (3).choose k * ((5 : ℕ).descFactorial k * (2 : ℕ).descFactorial (3 - k)) := by
  decide

-- diagonal duplication (2·4)^(3) = 8·7·6 = 336
example :
    (2 * 4).descFactorial 3
      = ∑ k ∈ range 4, (3).choose k * ((4 : ℕ).descFactorial k * (4 : ℕ).descFactorial (3 - k)) := by
  decide

-- a base smaller than the order, exercising truncated subtraction: 1^(3) = 0
example :
    (1 + 1).descFactorial 3
      = ∑ k ∈ range 4, (3).choose k * ((1 : ℕ).descFactorial k * (1 : ℕ).descFactorial (3 - k)) := by
  decide

-- Chu–Vandermonde range form: C(7,3) = 35
example : (3 + 4).choose 3 = ∑ k ∈ range 4, (3 : ℕ).choose k * (4 : ℕ).choose (3 - k) := by
  decide

end BinomialTheoremOQ03OQ01OQ03
