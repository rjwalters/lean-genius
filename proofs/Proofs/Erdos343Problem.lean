/-
Erdős Problem #343: Subcompleteness of Dense Multisets

Source: https://erdosproblems.com/343
Status: SOLVED (Szemerédi-Vu 2006)

Statement:
If A ⊆ ℕ is a multiset with |A ∩ {1,...,N}| ≫ N for all N, must A be subcomplete?
That is, must the sumset P(A) = {∑_{n∈B} n : B ⊆ A finite} contain an infinite
arithmetic progression?

Answer: YES

Historical Context:
- Folkman (1966): Proved subcompleteness holds if |A ∩ {1,...,N}| ≫ N^{1+ε} for some ε > 0
- Folkman (1966): Showed for all ε > 0 there exist multisets with density ~N^{1-ε} that
  are NOT subcomplete, showing the linear threshold is critical
- Szemerédi-Vu (2006): Proved the original question - linear density suffices

Key insight: This is about the arithmetic structure of sumsets of dense sequences.
The threshold at linear density is sharp.

Reference: Erdős-Graham [ErGr80, p.54], Folkman [Fo66], Szemerédi-Vu [SzVu06]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Finset BigOperators

namespace Erdos343

/-
## Part 1: Multisets and Density

A set A ⊆ ℕ has positive lower density if |A ∩ {1,...,N}| ≫ N.
This means the counting function grows at least linearly.
-/

/-- The counting function: how many elements of A are ≤ N -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (· ∈ A) |>.card

/-- A has positive lower density if |A ∩ {1,...,N}| ≥ cN for some c > 0 and all large N -/
def hasPositiveLowerDensity (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, (countingFunction A N : ℝ) ≥ c * N

/-- Stronger: A has density α if |A ∩ {1,...,N}| ~ αN -/
def hasDensity (A : Set ℕ) (α : ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((countingFunction A N : ℝ) / N) - α| < ε

/-
## Part 2: Sumsets and Subcompleteness

The sumset P(A) consists of all finite subset sums of A.
A is subcomplete if P(A) contains an infinite arithmetic progression.
-/

/-- The sumset P(A) = {sum of finite subsets of A} -/
def sumset (A : Finset ℕ) : Set ℕ :=
  { n : ℕ | ∃ B : Finset ℕ, B ⊆ A ∧ n = ∑ x ∈ B, x }

/-- For infinite A, we need a different definition -/
def sumsetInfinite (A : Set ℕ) : Set ℕ :=
  { n : ℕ | ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ A ∧ n = ∑ x ∈ B, x }

/-- An arithmetic progression {a + kd : k ∈ ℕ} -/
def arithmeticProgression (a d : ℕ) : Set ℕ :=
  { n : ℕ | ∃ k : ℕ, n = a + k * d }

/-- A set contains an infinite arithmetic progression -/
def containsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ arithmeticProgression a d ⊆ S

/-- A set A is subcomplete if P(A) contains an infinite AP -/
def isSubcomplete (A : Set ℕ) : Prop :=
  containsInfiniteAP (sumsetInfinite A)

/-
## Part 3: Folkman's Results (1966)

Folkman established both directions around the linear density threshold.
-/

/-- Folkman (1966): Superlinear density implies subcompleteness.
    If |A ∩ {1,...,N}| ≫ N^{1+ε} for some ε > 0, then A is subcomplete. -/
axiom folkman_superlinear :
  ∀ ε > 0, ∀ A : Set ℕ,
    (∃ c > 0, ∀ N : ℕ, (countingFunction A N : ℝ) ≥ c * N^(1 + ε)) →
    isSubcomplete A

/-- Folkman (1966): Sublinear density does NOT imply subcompleteness.
    For any ε > 0, there exists a multiset with density ~N^{1-ε} that is not subcomplete.
    This shows the linear threshold is critical: anything below linear can fail. -/
axiom folkman_counterexample :
  ∀ ε > 0, ∃ A : Set ℕ,
    (∃ c > 0, ∀ N : ℕ, (countingFunction A N : ℝ) ≥ c * N^(1 - ε)) ∧
    ¬isSubcomplete A

/-
## Part 4: Szemerédi-Vu Theorem (2006)

The main result resolving Erdős Problem #343: linear density suffices.
The proof uses deep results from additive combinatorics including
Freiman-type structure theorems and sumset estimates.
-/

/-- Szemerédi-Vu (2006): Linear density suffices for subcompleteness.
    This is the main theorem answering Problem #343 in the affirmative. -/
axiom szemeredi_vu_2006 :
  ∀ A : Set ℕ, hasPositiveLowerDensity A → isSubcomplete A

/-- The main result answering Problem #343 -/
theorem erdos_343_solved :
    ∀ A : Set ℕ, hasPositiveLowerDensity A → isSubcomplete A :=
  szemeredi_vu_2006

/-
## Part 5: Sharpness of the Linear Threshold

Combining Folkman's counterexample with Szemerédi-Vu shows that
linear density is exactly the critical boundary.
-/

/-- Folkman's counterexample shows the linear threshold is optimal:
    for any ε > 0, density N^{1-ε} does not guarantee subcompleteness. -/
theorem linear_threshold_is_sharp :
    ∀ ε > 0, ∃ A : Set ℕ,
      (∃ c > 0, ∀ N : ℕ, (countingFunction A N : ℝ) ≥ c * N^(1 - ε)) ∧
      ¬isSubcomplete A :=
  folkman_counterexample

/-
## Part 6: Summary

Erdős Problem #343 is SOLVED.
Linear density is the exact threshold for subcompleteness.
-/

/-- **Erdős Problem #343: SOLVED**

QUESTION: If A ⊆ ℕ is a multiset with |A ∩ {1,...,N}| ≫ N for all N,
must A be subcomplete (sumset contains infinite AP)?

ANSWER: YES (Szemerédi-Vu 2006)

SHARPNESS: Folkman showed this threshold is optimal - for any ε > 0,
there exist multisets with density ~N^{1-ε} that are NOT subcomplete.

The linear density threshold is the critical boundary. -/
theorem erdos_343_answer :
    ∀ A : Set ℕ, hasPositiveLowerDensity A → isSubcomplete A :=
  szemeredi_vu_2006

end Erdos343
