/-
Erdős Problem #267: Irrationality of Fibonacci Reciprocal Sums

Let F_n be the Fibonacci sequence. If n_1 < n_2 < ... is a sequence with
n_{k+1}/n_k ≥ c > 1, must Σ 1/F_{n_k} be irrational?

**Status**: PARTIALLY SOLVED
- Main conjecture: OPEN
- Σ 1/F_{2^n} irrational: PROVED (Good 1974, Bicknell-Hoggatt 1976)
- Σ 1/F_n irrational: PROVED (André-Jeannin 1989)

References:
- https://erdosproblems.com/267
- Good, I.J., "A reciprocal series of Fibonacci numbers", Fibonacci Quart. (1974)
- Bicknell & Hoggatt, "A reciprocal series of Fibonacci numbers with subscripts 2^n k",
  Fibonacci Quart. (1976)
- André-Jeannin, R., "Irrationalité de la somme des inverses de certaines suites
  récurrentes", C. R. Acad. Sci. Paris Sér. I Math. (1989)
-/

import Mathlib

open BigOperators Nat Real

namespace Erdos267

/-!
## Background

The Fibonacci sequence is defined by:
- F_1 = F_2 = 1
- F_{n+1} = F_n + F_{n-1}

The sequence begins: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, ...

The Fibonacci numbers grow exponentially with ratio approaching the golden ratio
φ = (1 + √5)/2 ≈ 1.618. More precisely, F_n ≈ φ^n / √5.

This rapid growth ensures that Σ 1/F_n converges absolutely.
-/

/-!
## Fibonacci Numbers

Mathlib provides `Nat.fib n` which computes F_n.
Note: Mathlib uses F_0 = 0, F_1 = 1, so our F_n corresponds to `Nat.fib n`.
-/

/-- F_1 = 1 -/
theorem fib_one : Nat.fib 1 = 1 := rfl

/-- F_2 = 1 -/
theorem fib_two : Nat.fib 2 = 1 := rfl

/-- F_3 = 2 -/
theorem fib_three : Nat.fib 3 = 2 := rfl

/-- F_4 = 3 -/
theorem fib_four : Nat.fib 4 = 3 := rfl

/-- F_5 = 5 -/
theorem fib_five : Nat.fib 5 = 5 := rfl

/-- F_6 = 8 -/
theorem fib_six : Nat.fib 6 = 8 := rfl

/-- F_10 = 55 -/
theorem fib_ten : Nat.fib 10 = 55 := rfl

/-- F_12 = 144 -/
theorem fib_twelve : Nat.fib 12 = 144 := rfl

/-!
## Fibonacci Growth

The Fibonacci sequence grows exponentially. The ratio F_{n+1}/F_n approaches
the golden ratio φ = (1 + √5)/2 ≈ 1.618.

For large n: F_n ≈ φ^n / √5 where φ = (1 + √5)/2.
-/

/-- The golden ratio φ = (1 + √5)/2 -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- φ > 1 (needed for convergence arguments) -/
theorem goldenRatio_gt_one : goldenRatio > 1 := by
  unfold goldenRatio
  have h : Real.sqrt 5 > 1 := by
    rw [Real.one_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  linarith

/-- Fibonacci numbers are positive for n ≥ 1 -/
theorem fib_pos (n : ℕ) (hn : n ≥ 1) : Nat.fib n > 0 := Nat.fib_pos hn

/-!
## Series Convergence

The series Σ 1/F_n converges because F_n grows exponentially.
Since F_n ≈ φ^n / √5 with φ > 1, we have 1/F_n ≈ √5 / φ^n,
and the geometric series Σ 1/φ^n converges.
-/

/-- The reciprocal Fibonacci series converges -/
axiom fibonacci_reciprocal_summable :
  Summable (fun n : ℕ => if n = 0 then 0 else (1 : ℝ) / Nat.fib n)

/-!
## Solved Cases

While the main conjecture remains open, specific cases have been proved.
-/

/-- **Good (1974), Bicknell-Hoggatt (1976)**:
    The sum Σ 1/F_{2^n} is irrational.

    This was the first special case proved. The exponential growth of indices
    (2^n) ensures the subsequence is very sparse, yet irrationality holds. -/
axiom good_bicknell_hoggatt :
  Irrational (∑' n : ℕ, (1 : ℝ) / Nat.fib (2 ^ n))

/-- **André-Jeannin (1989)**:
    The full sum Σ 1/F_n is irrational.

    This resolved the question for the complete Fibonacci reciprocal series.
    The proof uses techniques from transcendence theory and continued fractions. -/
axiom andre_jeannin :
  Irrational (∑' n : ℕ, if n = 0 then 0 else (1 : ℝ) / Nat.fib n)

/-!
## The Main Conjecture (OPEN)

Erdős asked: if we take a subsequence n_1 < n_2 < ... where the ratio
n_{k+1}/n_k is bounded away from 1 (i.e., ≥ c > 1), must the sum of
reciprocals Σ 1/F_{n_k} be irrational?

This is a generalization asking: how sparse can a subsequence be while
still guaranteeing irrationality?
-/

/-- A sequence n : ℕ → ℕ has ratio bounded below by c if n_{k+1}/n_k ≥ c for all k.
    This means the sequence grows at least geometrically. -/
def HasRatioBoundedBelow (n : ℕ → ℕ) (c : ℚ) : Prop :=
  ∀ k : ℕ, c ≤ (n (k + 1) : ℚ) / (n k : ℚ)

/-- **Erdős Problem #267 (OPEN)**:

    If n_1 < n_2 < ... is strictly increasing with n_{k+1}/n_k ≥ c > 1,
    must Σ 1/F_{n_k} be irrational?

    This conjecture asks whether geometric growth of indices is sufficient
    to guarantee irrationality of the Fibonacci reciprocal sum.

    The known cases:
    - c = 2 (indices 2^n): PROVED by Good, Bicknell-Hoggatt
    - c = 1 (all indices): PROVED by André-Jeannin (stronger!)

    The general case for arbitrary c > 1 remains OPEN. -/
def Erdos267Conjecture : Prop :=
  ∀ (n : ℕ → ℕ) (c : ℚ),
    c > 1 →
    StrictMono n →
    HasRatioBoundedBelow n c →
    Irrational (∑' k : ℕ, (1 : ℝ) / Nat.fib (n k))

/-- The conjecture is either true or false (law of excluded middle). -/
theorem erdos_267_open : Erdos267Conjecture ∨ ¬Erdos267Conjecture :=
  Classical.em Erdos267Conjecture

/-!
## Weaker Variant (OPEN)

Erdős also asked whether it might be sufficient for n_k/k → ∞.
This is a weaker growth condition than the ratio bound.
-/

/-- A sequence satisfies n_k/k → ∞ if the indices grow superlinearly. -/
def HasSuperlinearGrowth (n : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun k => (n k : ℝ) / (k : ℝ)) Filter.atTop Filter.atTop

/-- **Weaker variant (OPEN)**: Is superlinear growth sufficient?

    This is potentially easier than the main conjecture since superlinear
    growth is weaker than geometric growth. -/
def Erdos267WeakerVariant : Prop :=
  ∀ (n : ℕ → ℕ),
    StrictMono n →
    HasSuperlinearGrowth n →
    Irrational (∑' k : ℕ, (1 : ℝ) / Nat.fib (n k))

/-!
## Numerical Observations

The sum Σ 1/F_n ≈ 3.359885666...

First few terms:
- 1/F_1 = 1/1 = 1
- 1/F_2 = 1/1 = 1
- 1/F_3 = 1/2 = 0.5
- 1/F_4 = 1/3 ≈ 0.333
- 1/F_5 = 1/5 = 0.2
- 1/F_6 = 1/8 = 0.125
- ...

The series converges quickly due to exponential growth of F_n.
-/

/-- The sum Σ 1/F_{2^n} starts: 1/1 + 1/1 + 1/3 + 1/21 + 1/987 + ... -/
theorem pow_two_series_first_terms :
    Nat.fib (2^0) = 1 ∧ Nat.fib (2^1) = 1 ∧ Nat.fib (2^2) = 3 ∧
    Nat.fib (2^3) = 21 ∧ Nat.fib (2^4) = 987 := by
  constructor; rfl
  constructor; rfl
  constructor; rfl
  constructor; native_decide
  native_decide

/-!
## Related Problems

This problem connects to a broader theme in Erdős's work on irrationality:
- Problem #250: Σ σ(n)/2^n (solved by Nesterenko)
- Problem #259: Σ μ(n)² n/2^n (solved by Chen-Ruzsa)

All ask: when do "natural" series sum to irrational numbers?

The Fibonacci case is special because:
1. Fibonacci numbers have rich algebraic structure (golden ratio, Zeckendorf)
2. The reciprocal sum relates to continued fractions
3. The Lucas-Lehmer sequence provides related identities
-/

end Erdos267
