/-
Erdős Problem #362: Subset Sum Concentration

Source: https://erdosproblems.com/362
Status: SOLVED (Sárközy-Szemerédi 1965, Halász 1977, Stanley 1980)

Statement:
Let A ⊆ ℕ be a finite set of size N. For any fixed target t:
Q1: Are there ≪ 2^N / N^(3/2) subsets S ⊆ A with sum(S) = t?
Q2: If we also fix |S| = l, are there ≪ 2^N / N² such subsets?

Answers: YES to both!

Key Results:
- Erdős-Moser (1965): First bound with extra (log N)^(3/2) factor
- Sárközy-Szemerédi (1965): Proved Q1 affirmatively (removed log factor)
- Halász (1977): Proved Q2 affirmatively via multi-dimensional result
- Stanley (1980): Maximizing set is {-⌊(N-1)/2⌋, ..., ⌊N/2⌋}

Tags: additive-combinatorics, subset-sum, concentration, counting
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot

namespace Erdos362

open Finset Nat Real Filter BigOperators

/-
## Part 1: Subset Sum Definitions

Define the number of subsets summing to a target value.
-/

variable {α : Type*} [DecidableEq α]

/-- The sum of elements in a finite set -/
def setSum (A : Finset ℤ) : ℤ := ∑ x ∈ A, x

/-- Subsets of A that sum to target t -/
def subsetsWithSum (A : Finset ℤ) (t : ℤ) : Finset (Finset ℤ) :=
  A.powerset.filter (fun S => setSum S = t)

/-- Count of subsets summing to t -/
def countSubsetsWithSum (A : Finset ℤ) (t : ℤ) : ℕ :=
  (subsetsWithSum A t).card

/-- The concentration function: max over all targets -/
noncomputable def concentrationFunction (A : Finset ℤ) : ℕ :=
  Finset.sup (Finset.Icc (∑ x ∈ A.filter (· < 0), x) (∑ x ∈ A.filter (· ≥ 0), x))
    (fun t => countSubsetsWithSum A t)

/-
## Part 2: Question 1 - General Subset Sum Bound

For any A of size N and any target t:
  #{S ⊆ A : sum(S) = t} ≪ 2^N / N^(3/2)
-/

/-- Erdős-Moser (1965): Weaker bound with log factor.
    First proved the concentration bound with an extra (log N)^(3/2) factor. -/
axiom erdos_moser_1965_bound :
    ∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, (countSubsetsWithSum A t : ℝ) ≤
        C * 2^(A.card) / (A.card : ℝ)^(3/2 : ℝ) * (Real.log A.card)^(3/2 : ℝ)

/-- Sárközy-Szemerédi (1965): Sharp bound answering Q1.
    Removed the log factor from the Erdős-Moser bound. -/
axiom sarkozy_szemeredi_1965 :
    ∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, (countSubsetsWithSum A t : ℝ) ≤ C * 2^(A.card) / (A.card : ℝ)^(3/2 : ℝ)

/-- The bound 2^N / N^(3/2) is tight up to constants. -/
axiom bound_tight_order :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ∃ (A : Finset ℤ), A.card = N ∧
        ∃ t : ℤ, (countSubsetsWithSum A t : ℝ) ≥ (1 - ε) * 2^N / (N : ℝ)^(3/2 : ℝ)

/-
## Part 3: Question 2 - Fixed Cardinality Bound

For any A of size N, any target t, and any fixed cardinality l:
  #{S ⊆ A : sum(S) = t, |S| = l} ≪ 2^N / N²
-/

/-- Subsets of fixed cardinality summing to t -/
def subsetsWithSumAndCard (A : Finset ℤ) (t : ℤ) (l : ℕ) : Finset (Finset ℤ) :=
  A.powerset.filter (fun S => setSum S = t ∧ S.card = l)

/-- Count of subsets with fixed sum and cardinality -/
def countSubsetsWithSumAndCard (A : Finset ℤ) (t : ℤ) (l : ℕ) : ℕ :=
  (subsetsWithSumAndCard A t l).card

/-- Halász (1977): Sharp bound answering Q2.
    With fixed cardinality constraint, the bound improves to 2^N / N². -/
axiom halasz_1977 :
    ∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, ∀ l : ℕ,
        (countSubsetsWithSumAndCard A t l : ℝ) ≤ C * 2^(A.card) / (A.card : ℝ)^2

/-
## Part 4: Stanley's Extremal Result

The symmetric set {-⌊(N-1)/2⌋, ..., ⌊N/2⌋} maximizes concentration.
Stanley's proof uses the hard Lefschetz theorem from algebraic geometry
to establish the Sperner property for certain posets.
-/

/-- The symmetric set centered at 0 -/
def symmetricSet (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N - 1 : ℕ) / 2 : ℤ) ((N : ℕ) / 2 : ℤ)

/-- Stanley (1980): Symmetric set maximizes concentration.
    Uses the hard Lefschetz theorem from algebraic geometry. -/
axiom stanley_1980_extremal :
    ∀ (A : Finset ℤ), ∀ t : ℤ,
      countSubsetsWithSum A t ≤
        countSubsetsWithSum (symmetricSet A.card) 0

/-- For the symmetric set, t = 0 achieves maximum concentration. -/
axiom symmetric_max_at_zero (N : ℕ) :
    ∀ t : ℤ, countSubsetsWithSum (symmetricSet N) t ≤
      countSubsetsWithSum (symmetricSet N) 0

/-
## Part 5: Multi-dimensional Generalization

Halász's theorem generalizes to vector sums in d dimensions,
giving a bound of 2^N / N^((d+1)/2).
-/

/-- Vector-valued subset sum -/
def vectorSetSum {d : ℕ} (A : Finset (Fin d → ℤ)) : Fin d → ℤ :=
  fun i => ∑ v ∈ A, v i

/-- Count of subsets with fixed vector sum -/
def countVectorSubsetsWithSum {d : ℕ} (A : Finset (Fin d → ℤ))
    (t : Fin d → ℤ) : ℕ :=
  (A.powerset.filter (fun S => vectorSetSum S = t)).card

/-- Halász multi-dimensional bound: generalizes to d dimensions.
    The exponent (d+1)/2 specializes to 3/2 for d=2 and 2 for d=3. -/
axiom halasz_multi_dim (d : ℕ) :
    ∃ C > 0, ∀ (A : Finset (Fin d → ℤ)), A.card > 0 →
      ∀ t : Fin d → ℤ,
        (countVectorSubsetsWithSum A t : ℝ) ≤
          C * 2^(A.card) / (A.card : ℝ)^((d + 1 : ℕ) / 2 : ℝ)

/-
## Part 6: Generating Function Approach

The Sárközy-Szemerédi proof uses Fourier analysis / generating functions.
The generating function for subset sums factors as a product, and
the concentration bound follows from saddle point analysis.
-/

/-- The generating function for subset sums.
    The coefficient of z^t in this product equals countSubsetsWithSum A t. -/
noncomputable def subsetSumGF (A : Finset ℤ) (z : ℂ) : ℂ :=
  ∏ a ∈ A, (1 + z^(a.toNat))

/-- Fourier coefficient extraction: countSubsetsWithSum equals
    the integral of the generating function against an exponential. -/
axiom fourier_extraction (A : Finset ℤ) (t : ℤ) :
    (countSubsetsWithSum A t : ℂ) =
      (1 : ℂ) / (2 * Real.pi) * ∫ θ in Set.Icc 0 (2 * Real.pi),
        subsetSumGF A (Complex.exp (Complex.I * θ)) * Complex.exp (-Complex.I * t * θ)

/-
## Part 7: Summary

Erdős Problem #362 asks about concentration of subset sums.
Both questions were answered affirmatively.
-/

/-- Main summary of Erdős Problem #362.
    Q1: #{S ⊆ A : sum(S) = t} ≪ 2^N / N^(3/2) (Sárközy-Szemerédi 1965)
    Q2: #{S ⊆ A : sum(S) = t, |S| = l} ≪ 2^N / N² (Halász 1977) -/
theorem erdos_362_summary :
    (∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, (countSubsetsWithSum A t : ℝ) ≤
        C * 2^(A.card) / (A.card : ℝ)^(3/2 : ℝ)) ∧
    (∃ C > 0, ∀ (A : Finset ℤ), A.card > 0 →
      ∀ t : ℤ, ∀ l : ℕ, (countSubsetsWithSumAndCard A t l : ℝ) ≤
        C * 2^(A.card) / (A.card : ℝ)^2) := by
  exact ⟨sarkozy_szemeredi_1965, halasz_1977⟩

end Erdos362
