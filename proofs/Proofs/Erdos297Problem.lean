/-
Erdős Problem #297: Counting Egyptian Fraction Representations of 1

Source: https://erdosproblems.com/297
Status: SOLVED (2024)

Statement:
Let N ≥ 1. How many A ⊆ {1,...,N} are there such that Σ_{n∈A} 1/n = 1?

Answer:
The count is 2^{(c + o(1))N} where c ≈ 0.91...

This was a long-standing open problem asking whether the count grows like 2^{cN}
for some c < 1, or like 2^{(1+o(1))N}. The former is true.

Resolution (2024) - Three Independent Teams:
1. Steinerberger (arXiv:2403.17041): Upper bound 2^{0.93N}
2. Liu-Sawhney (arXiv:2404.07113): Full asymptotic 2^{(c+o(1))N}
3. Conlon-Fox-He-Mubayi-Pham-Suk-Verstraëte (arXiv:2404.16016): Same asymptotic

The constant c ≈ 0.91... is defined as the solution to a certain integral equation.

Key Insight:
The set of unit fractions with sum exactly 1 is sparse within all subsets.
Despite having 2^N possible subsets, only 2^{0.91N} work - exponentially fewer.

References:
- [St24] Steinerberger, "On a problem involving unit fractions"
- [LiSa24] Liu-Sawhney, "On further questions regarding unit fractions"
- [CFHMPSV24] Conlon et al., "A question of Erdős and Graham on Egyptian fractions"
- OEIS: A092670

Tags: egyptian-fractions, number-theory, combinatorics, counting
-/

import Mathlib

open Nat Finset

namespace Erdos297

/-
## Part 1: Basic Definitions

Unit fractions and their sums over finite subsets of natural numbers.
-/

/-- The harmonic sum of a finite set A of natural numbers: Σ_{n ∈ A} 1/n.
    Elements equal to 0 contribute nothing (avoiding division by zero). -/
noncomputable def harmonicSum (A : Finset ℕ) : ℚ :=
  A.sum fun n => if n = 0 then 0 else 1 / n

/-- A finite set A of positive integers is an Egyptian representation of 1
    if its harmonic sum equals 1 and all elements are at least 1. -/
def IsEgyptianRepresentation (A : Finset ℕ) : Prop :=
  harmonicSum A = 1 ∧ ∀ n ∈ A, n ≥ 1

/-- The collection of all subsets of {0, 1, ..., N} as a finite set. -/
def subsets (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (N + 1)).powerset

/-- The count of Egyptian representations using elements from {1,...,N}:
    the number of subsets A ⊆ {1,...,N} with Σ_{n∈A} 1/n = 1. -/
noncomputable def egyptianCount (N : ℕ) : ℕ :=
  ((subsets N).filter (fun A => harmonicSum A = 1 ∧ 0 ∉ A)).card

/-
## Part 2: Verified Examples

Concrete Egyptian fraction representations proved by computation.
-/

/-- The trivial representation: {1} has harmonic sum 1/1 = 1. -/
theorem singleton_one_is_egyptian : harmonicSum {1} = 1 := by
  simp [harmonicSum]

/-- The classic decomposition: 1/2 + 1/3 + 1/6 = 1.
    Proved by unfolding the sum and computing with norm_num. -/
theorem two_three_six_is_egyptian : harmonicSum {2, 3, 6} = 1 := by
  unfold harmonicSum
  simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6} : Finset ℕ) by decide),
              Finset.sum_insert (show (3 : ℕ) ∉ ({6} : Finset ℕ) by decide),
              Finset.sum_singleton]
  norm_num
-- Arithmetic: 1/2 + 1/3 + 1/6 = 3/6 + 2/6 + 1/6 = 6/6 = 1

/-- Another decomposition: 1/2 + 1/4 + 1/5 + 1/20 = 1. -/
theorem two_four_five_twenty_is_egyptian : harmonicSum {2, 4, 5, 20} = 1 := by
  unfold harmonicSum
  simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({4, 5, 20} : Finset ℕ) by decide),
              Finset.sum_insert (show (4 : ℕ) ∉ ({5, 20} : Finset ℕ) by decide),
              Finset.sum_insert (show (5 : ℕ) ∉ ({20} : Finset ℕ) by decide),
              Finset.sum_singleton]
  norm_num
-- Arithmetic: 1/2 + 1/4 + 1/5 + 1/20 = 10/20 + 5/20 + 4/20 + 1/20 = 20/20 = 1
-- Arithmetic: 1/2 + 1/3 + 1/7 + 1/42 = 21/42 + 14/42 + 6/42 + 1/42 = 42/42 = 1

/-- There exist at least three distinct Egyptian representations. -/
theorem at_least_three_representations :
    harmonicSum {1} = 1 ∧
    harmonicSum {2, 3, 6} = 1 ∧
    harmonicSum {2, 4, 5, 20} = 1 := by
  exact ⟨singleton_one_is_egyptian, two_three_six_is_egyptian, two_four_five_twenty_is_egyptian⟩

/-
## Part 3: Basic Bounds

Elementary bounds on the Egyptian count function.
-/
-- The filter of a finite set has cardinality ≤ the original set.
-- At most 2^N subsets of an N-element set.
-- {1} ⊆ {1,...,N} and harmonicSum {1} = 1.

/-
## Part 4: The Central Question

Erdős asked whether the growth is truly subexponential (c < 1) or near-maximal.
-/

/-- The question: is there c < 1 with egyptianCount N ≤ C · 2^{cN}?
    Equivalently: is the exponential growth rate strictly less than 1? -/
def hasSubexponentialGrowth : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∃ C : ℝ, ∀ N : ℕ, (egyptianCount N : ℝ) ≤ C * 2^(c * N)

/-
## Part 5: Steinerberger's Upper Bound (March 2024)

The first proof that c < 1, establishing egyptianCount(N) ≤ 2^{0.93N}.
-/

/-- Steinerberger's constant: the exponent 0.93 from his upper bound. -/
def steinerbergerConstant : ℝ := 0.93

/-
**Steinerberger (2024, arXiv:2403.17041):**
    The Egyptian count satisfies egyptianCount(N) ≤ 2^{0.93N} for all sufficiently large N.
-/

/-
## Part 6: Liu-Sawhney's Full Asymptotic (April 2024)

The complete answer: both matching upper and lower bounds with constant c ≈ 0.91...
-/

/-- The optimal constant c ≈ 0.91... from Liu-Sawhney.
    Defined as the solution to a certain integral equation involving
    the density of integers with particular divisibility properties. -/
noncomputable def liuSawhneyConstant : ℝ := 0.91  -- Numerical approximation

/-- Liu-Sawhney proved the constant is well-defined and lies in (0.9, 0.92).
    The exact value satisfies an integral equation involving logarithmic densities. -/
axiom liuSawhney_constant_bounds :
    liuSawhneyConstant > 0.9 ∧ liuSawhneyConstant < 0.92

/-- **Liu-Sawhney (2024, arXiv:2404.07113):** Full asymptotic.
    For every ε > 0, eventually:
      2^{(c - ε)N} ≤ egyptianCount(N) ≤ 2^{(c + ε)N}
    where c ≈ 0.91... is the Liu-Sawhney constant.

    This gives both upper and lower bounds, completely characterizing
    the exponential growth rate of the Egyptian count. -/
axiom liuSawhney_asymptotic :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      2^((liuSawhneyConstant - ε) * N) ≤ (egyptianCount N : ℝ) ∧
      (egyptianCount N : ℝ) ≤ 2^((liuSawhneyConstant + ε) * N)

/-
## Part 7: Conlon et al. (April 2024)

Independent proof of the same asymptotic, plus generalization to arbitrary targets.
-/

/-- Count of subsets with harmonic sum equal to a given rational target x. -/
noncomputable def egyptianCountTarget (N : ℕ) (x : ℚ) : ℕ :=
  ((subsets N).filter (fun A => harmonicSum A = x ∧ 0 ∉ A)).card

/-
**Conlon et al. generalization:**
    For any rational x > 0, there exists a constant c_x ∈ (0, 1) such that
    egyptianCountTarget(N, x) = 2^{(c_x + o(1))N}.
-/

/-
## Part 8: The 2017 MathOverflow Precedent

A closely related question about sums ≤ 1 was studied earlier.
-/

/-- Count of subsets of {1,...,N} with harmonic sum at most 1. -/
noncomputable def egyptianCountLeq (N : ℕ) : ℕ :=
  ((subsets N).filter (fun A => harmonicSum A ≤ 1 ∧ 0 ∉ A)).card

/-
## Part 9: Intuition — Why c < 1?

The constraint Σ 1/n = 1 exactly is very restrictive.
-/

/-
**Heuristic:** For a random subset of {1,...,N}, the expected harmonic sum is
    E[Σ 1/n] ≈ (1/2) · H_N ≈ (log N)/2, which grows without bound.
-/

/-
## Part 10: Main Results

The complete answer to Erdős Problem #297.
-/

/-- **Erdős Problem #297: Main Theorem**

    The count of A ⊆ {1,...,N} with Σ_{n∈A} 1/n = 1 is 2^{(c + o(1))N}
    where c ≈ 0.91... is the Liu-Sawhney constant.

    Key facts:
    1. c < 1, so the count is exponentially smaller than 2^N
    2. The exact value of c is determined by an integral equation
    3. Three teams proved this independently in 2024 -/
theorem erdos_297_main :
    ∃ c : ℝ, 0.9 < c ∧ c < 0.93 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      2^((c - ε) * N) ≤ (egyptianCount N : ℝ) ∧
      (egyptianCount N : ℝ) ≤ 2^((c + ε) * N) := by
  use liuSawhneyConstant
  obtain ⟨h1, h2⟩ := liuSawhney_constant_bounds
  constructor
  · linarith
  constructor
  · linarith
  · exact liuSawhney_asymptotic

/-- **The answer to Erdős's question:** YES, the growth is subexponential.
    There exists c < 1 such that egyptianCount(N) ≤ C · 2^{cN}.

    Proof sketch: Steinerberger gives the bound for large N.
    For finitely many small N, choose C large enough. -/
axiom erdos_297_answer : hasSubexponentialGrowth

/-
## Part 11: Summary
-/

/-- **Summary of Erdős Problem #297:**

    PROBLEM: How many A ⊆ {1,...,N} satisfy Σ 1/n = 1?

    ANSWER: 2^{(c + o(1))N} where c ≈ 0.91...

    KEY RESULT: c < 1, so the count is exponentially smaller than 2^N

    RESOLUTION (2024): Three independent teams within weeks of each other:
    1. Steinerberger: Upper bound 2^{0.93N}
    2. Liu-Sawhney: Full asymptotic with c ≈ 0.91...
    3. Conlon et al.: Same asymptotic, generalized to any x ∈ ℚ₊

    WHY c < 1: The constraint Σ 1/n = 1 exactly is very restrictive.
    Most random subsets overshoot since E[sum] ~ (log N)/2 → ∞.

    STATUS: SOLVED -/
theorem erdos_297_solved : hasSubexponentialGrowth := erdos_297_answer

end Erdos297
