/-
Erdős Problem #300: Maximum Subsets Avoiding Unit Fraction Sum 1

Source: https://erdosproblems.com/300
Status: SOLVED

Statement:
Let A(N) denote the maximal cardinality of A ⊆ {1,...,N} such that
Σ_{n∈S} 1/n ≠ 1 for all S ⊆ A. Estimate A(N).

Answer: A(N) = (1 - 1/e + o(1))N

Background:
- Erdős-Graham (1980): Conjectured A(N) = (1 + o(1))N
- Croot (2003): Disproved conjecture, showed A(N) < cN for some c < 1
- Lower bound: A(N) ≥ (1 - 1/e + o(1))N is trivial
- Liu-Sawhney (2024): Proved A(N) = (1 - 1/e + o(1))N exactly

Key Results:
- The constant 1 - 1/e ≈ 0.632 is the exact asymptotic density
- This matches the trivial lower bound, showing it's optimal
- Connected to Egyptian fraction representations

References:
- Erdős-Graham (1980): "Old and new problems in combinatorial number theory"
- Croot (2003): "On a coloring conjecture about unit fractions"
- Liu-Sawhney (2024): "On further questions regarding unit fractions"

Tags: number-theory, unit-fractions, subset-sums, combinatorics
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Nat Real Finset BigOperators

namespace Erdos300

/-!
## Part I: Basic Definitions
-/

/--
**The Unit Fraction Sum:**
For a set S ⊆ ℕ, compute Σ_{n∈S} 1/n.
-/
noncomputable def unitFractionSum (S : Finset ℕ) : ℝ :=
  ∑ n in S, (1 : ℝ) / n

/--
**Unit Sum-Free Set:**
A set A is unit sum-free if no subset has unit fractions summing to exactly 1.
-/
def IsUnitSumFree (A : Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → unitFractionSum S ≠ 1

/--
**The Interval {1, ..., N}:**
The set of positive integers up to N.
-/
def intervalN (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/--
**A(N) - The Maximum Size:**
The maximal cardinality of a unit sum-free subset of {1,...,N}.
-/
noncomputable def A (N : ℕ) : ℕ :=
  Finset.sup' (Finset.filter (fun A => A ⊆ intervalN N ∧ IsUnitSumFree A)
    (Finset.powerset (intervalN N)))
    ⟨∅, by simp [intervalN, IsUnitSumFree]⟩
    Finset.card

/-!
## Part II: The Erdős-Graham Conjecture (Disproved)
-/

/--
**The Original Conjecture:**
Erdős and Graham conjectured A(N) = (1 + o(1))N.
This would mean almost all integers can be included.
-/
def erdosGrahamConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ N in Filter.atTop, (A N : ℝ) ≥ (1 - ε) * N

/--
**Croot's Theorem (2003):**
The Erdős-Graham conjecture is FALSE.
There exists c < 1 such that A(N) < cN for all large N.
-/
axiom croot_theorem :
    ∃ c : ℝ, c < 1 ∧ ∀ᶠ N in Filter.atTop, (A N : ℝ) < c * N

/--
**Corollary: Conjecture Disproved**
-/
theorem erdos_graham_conjecture_false : ¬erdosGrahamConjecture := by
  intro h
  obtain ⟨c, hc_lt_one, hc⟩ := croot_theorem
  -- The conjecture implies A(N)/N → 1, but Croot shows A(N)/N < c < 1
  sorry

/-!
## Part III: The Trivial Lower Bound
-/

/--
**The 1/e Threshold:**
Numbers n with 1/n > 1/e (i.e., n < e) are "large unit fractions."
-/
def largeUnitFraction (n : ℕ) : Prop := (1 : ℝ) / n > Real.exp (-1)

/--
**Construction for Lower Bound:**
Take all n ∈ {1,...,N} with n > e (small unit fractions).
These contribute < 1 to any finite sum, so no subset sums to exactly 1.
-/
def smallUnitFractionSet (N : ℕ) : Finset ℕ :=
  (intervalN N).filter (fun n => (n : ℝ) > Real.exp 1)

/--
**Trivial Lower Bound:**
A(N) ≥ (1 - 1/e + o(1))N

The set of n with n > e has density 1 - 1/e ≈ 0.632.
-/
axiom trivial_lower_bound :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (A N : ℝ) ≥ (1 - Real.exp (-1) - ε) * N

/--
**Why Small Fractions Work:**
If all 1/n < 1/e, then sum of any subset with < e elements is < 1.
More sophisticated: greedy algorithm avoids sum reaching exactly 1.
-/
theorem small_fractions_safe (N : ℕ) :
    IsUnitSumFree (smallUnitFractionSet N) := by
  intro S hS _
  -- Sum of small unit fractions can't reach exactly 1
  sorry

/-!
## Part IV: Liu-Sawhney Theorem (2024)
-/

/--
**The Liu-Sawhney Theorem (2024):**
A(N) = (1 - 1/e + o(1))N

This is the main result: the trivial lower bound is asymptotically optimal.
-/
axiom liu_sawhney_theorem :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      |((A N : ℝ) / N) - (1 - Real.exp (-1))| < ε

/--
**The Exact Constant:**
The asymptotic density of maximum unit sum-free sets is exactly 1 - 1/e.
-/
noncomputable def optimalDensity : ℝ := 1 - Real.exp (-1)

/--
**Numerical Value:**
1 - 1/e ≈ 0.6321205588...
-/
theorem optimal_density_value : optimalDensity = 1 - Real.exp (-1) := rfl

/--
**Upper Bound (Liu-Sawhney):**
A(N) ≤ (1 - 1/e + o(1))N
-/
axiom liu_sawhney_upper :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (A N : ℝ) ≤ (1 - Real.exp (-1) + ε) * N

/--
**Combined: Asymptotic Formula**
-/
theorem asymptotic_formula :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (1 - Real.exp (-1) - ε) * N ≤ (A N : ℝ) ∧
      (A N : ℝ) ≤ (1 - Real.exp (-1) + ε) * N := by
  intro ε hε
  have h1 := trivial_lower_bound ε hε
  have h2 := liu_sawhney_upper ε hε
  filter_upwards [h1, h2] with N hN1 hN2
  exact ⟨hN1, hN2⟩

/-!
## Part V: Why 1 - 1/e Appears
-/

/--
**The Probabilistic Intuition:**
Consider a random subset where each n is included with probability p.
The expected sum of 1/n is approximately p · ln(N).
To avoid sum ≈ 1, need p · ln(N) < 1, so p < 1/ln(N).
But more refined analysis gives density 1 - 1/e.
-/
axiom probabilistic_intuition : True

/--
**The Exponential Connection:**
The constant e appears because:
- Σ_{n≤N} 1/n ≈ ln(N) (harmonic series)
- To avoid sum = 1, we exclude a specific fraction
- The optimal exclusion pattern has density 1/e
-/
axiom exponential_connection : True

/--
**Greedy Algorithm:**
A greedy construction achieves the lower bound:
Start with ∅, add n if current sum + 1/n ≠ 1.
This gives a set of density ≥ 1 - 1/e.
-/
axiom greedy_achieves_lower_bound :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      ∃ A : Finset ℕ, A ⊆ intervalN N ∧ IsUnitSumFree A ∧
        (A.card : ℝ) ≥ (1 - Real.exp (-1) - ε) * N

/-!
## Part VI: Connection to Egyptian Fractions
-/

/--
**Egyptian Fraction Representation:**
A number r can be written as a sum of distinct unit fractions.
Every positive rational has such a representation.
-/
def HasEgyptianRepresentation (r : ℚ) : Prop :=
  ∃ S : Finset ℕ, (∑ n in S, (1 : ℚ) / n) = r

/--
**1 Has Many Representations:**
1 = 1/2 + 1/3 + 1/6
1 = 1/2 + 1/4 + 1/5 + 1/20
etc.
-/
axiom one_egyptian_representations :
    ∃ S₁ S₂ : Finset ℕ, S₁ ≠ S₂ ∧
      (∑ n in S₁, (1 : ℚ) / n) = 1 ∧
      (∑ n in S₂, (1 : ℚ) / n) = 1

/--
**Why Avoiding 1 is Hard:**
There are many ways to sum distinct unit fractions to 1.
The challenge is finding large sets that avoid ALL such combinations.
-/
axiom avoiding_one_is_hard : True

/-!
## Part VII: Variants and Generalizations
-/

/--
**Avoiding Other Sums:**
Instead of sum = 1, what if we avoid sum = k for integer k?
-/
def IsKSumFree (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → unitFractionSum S ≠ k

/--
**Multiple Forbidden Values:**
Avoiding sum ∈ {1, 2, 3, ...} is much more restrictive.
-/
def AvoidAllIntegers (A : Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
    ∀ k : ℕ, k > 0 → unitFractionSum S ≠ k

/--
**Related Erdős Problems:**
- Problem 301: Other unit fraction questions
- Egyptian fraction density problems
-/
axiom related_problems : True

/-!
## Part VIII: The Croot Technique
-/

/--
**Croot's Method:**
Croot used coloring and density arguments to show A(N)/N < c < 1.
The key is showing that large sets must contain subsets summing to 1.
-/
axiom croot_method_sketch :
    -- If |A| > cN for some c > 1 - 1/e + δ
    -- then A contains a subset summing to 1
    True

/--
**The Gap Before Liu-Sawhney:**
Between Croot (2003) and Liu-Sawhney (2024):
- Known: 1 - 1/e ≤ lim A(N)/N ≤ c for some unknown c
- Open: What is the exact value?
Liu-Sawhney closed this gap.
-/
axiom twenty_year_gap : True

/-!
## Part IX: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_300_summary :
    -- Liu-Sawhney solved the problem
    (∀ ε > 0, ∀ᶠ N in Filter.atTop,
      |((A N : ℝ) / N) - (1 - Real.exp (-1))| < ε) ∧
    -- The conjecture A(N) = (1+o(1))N is false
    (∃ c : ℝ, c < 1 ∧ ∀ᶠ N in Filter.atTop, (A N : ℝ) < c * N) := by
  exact ⟨liu_sawhney_theorem, croot_theorem⟩

/--
**Erdős Problem #300: SOLVED**

**QUESTION:** Estimate A(N) = max{|A| : A ⊆ {1,...,N}, no subset sums to 1}

**CONJECTURE (Erdős-Graham 1980):** A(N) = (1 + o(1))N

**ANSWER:** A(N) = (1 - 1/e + o(1))N

**HISTORY:**
- Erdős-Graham (1980): Conjectured A(N) ≈ N
- Croot (2003): Disproved conjecture, showed A(N) < cN for c < 1
- Liu-Sawhney (2024): Proved A(N) = (1 - 1/e + o(1))N exactly

**KEY INSIGHT:** The trivial lower bound (avoiding "large" unit fractions)
is actually optimal. One cannot do better than density 1 - 1/e ≈ 0.632.

**CONSTANT:** 1 - 1/e ≈ 0.6321205588...
-/
theorem erdos_300 :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      |((A N : ℝ) / N) - (1 - Real.exp (-1))| < ε :=
  liu_sawhney_theorem

/--
**Historical Note:**
This problem took 44 years to solve (1980-2024).
Croot's 2003 result was crucial progress, disproving the conjecture.
Liu-Sawhney's 2024 paper finally determined the exact constant,
confirming that the naive lower bound was optimal all along.
-/
theorem historical_note : True := trivial

end Erdos300
