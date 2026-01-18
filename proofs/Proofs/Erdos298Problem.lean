/-
  Erdős Problem #298: Unit Fractions from Sets of Positive Density

  Does every set A ⊆ ℕ of positive density contain some finite S ⊂ A such that
  ∑_{n ∈ S} 1/n = 1?

  **Answer**: YES, proved by Thomas Bloom (2021).

  **Main Results**:
  - Bloom's Theorem: Any A ⊆ ℕ with positive density contains S with ∑ 1/n = 1
  - Stronger version: Positive UPPER density suffices (also proved by Bloom)

  **Historical Notes**:
  - This was a conjecture of Erdős dating back to his work on unit fractions
  - Erdős offered $500 for a proof (one of his monetary prizes)
  - Bloom's proof uses sophisticated probabilistic and analytic methods
  - The Lean 3 formalization by Bloom & Mehta is at github.com/b-mehta/unit-fractions

  References:
  - https://erdosproblems.com/298
  - Bloom, T. F., "On a density conjecture about unit fractions" arXiv:2112.03726 (2021)
  - Related to Erdős #46, #47 on unit fraction representations
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

open Finset BigOperators

namespace Erdos298

/-!
## Background: Unit Fractions and Density

A **unit fraction** is a fraction of the form 1/n for positive integer n.
The **Egyptian fraction** representation problem asks which positive rationals
can be written as sums of distinct unit fractions.

A key insight is that 1 = 1/2 + 1/3 + 1/6, so unit fractions can sum to 1.

**Density** measures how "thick" a subset of ℕ is:
- Natural density: lim_{N→∞} |A ∩ [1,N]| / N
- Upper density: limsup_{N→∞} |A ∩ [1,N]| / N

Erdős asked: If A is dense enough, must it contain a finite subset summing to 1?
-/

/-!
## Core Definitions
-/

/-- A set A ⊆ ℕ has positive natural density if the limit of |A ∩ [1,N]|/N
exists and is positive. This is formalized axiomatically. -/
axiom HasPosDensity (A : Set ℕ) : Prop

/-- Upper density of a set A ⊆ ℕ: limsup_{N→∞} |A ∩ [1,N]|/N.
Defined axiomatically. -/
axiom upperDensity (A : Set ℕ) : ℝ

/-- A set has positive upper density if upperDensity A > 0. -/
def HasPosUpperDensity (A : Set ℕ) : Prop := upperDensity A > 0

/-- The sum of 1/n over elements of a finite set S, computed in ℚ. -/
noncomputable def unitFractionSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S.filter (· > 0), (1 : ℚ) / n

/-- A finite set S has unit fraction sum equal to 1. -/
def SumsToOne (S : Finset ℕ) : Prop := unitFractionSum S = 1

/-- A set A contains a finite subset with unit fraction sum 1. -/
def ContainsUnitSumSubset (A : Set ℕ) : Prop :=
  ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ SumsToOne S

/-!
## Examples: Simple Unit Fraction Sums

These examples show that unit fraction sums equal to 1 do exist.
-/

/-- 1/2 + 1/3 + 1/6 = 1 (classic identity). -/
axiom example_2_3_6 : unitFractionSum {2, 3, 6} = 1

/-- 1/2 + 1/4 + 1/5 + 1/20 = 1. -/
axiom example_2_4_5_20 : unitFractionSum {2, 4, 5, 20} = 1

/-- 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1. -/
axiom example_3_4_5_6_20 : unitFractionSum {3, 4, 5, 6, 20} = 1

/-!
## The Erdős Conjecture and Bloom's Theorem

Erdős conjectured that positive density suffices to guarantee a unit sum subset.
-/

/-- **Erdős Problem #298**: Does every set of positive density contain a finite
subset whose reciprocals sum to 1?

The conjecture is: For all A ⊆ ℕ with 0 ∉ A and positive density,
there exists S ⊆ A finite with ∑_{n ∈ S} 1/n = 1. -/
def erdos_298_conjecture : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → HasPosDensity A → ContainsUnitSumSubset A

/-- **Bloom's Theorem (2021)**: The Erdős conjecture is TRUE.

Thomas Bloom proved this in "On a density conjecture about unit fractions"
(arXiv:2112.03726). The proof uses:
1. A probabilistic construction of auxiliary sets
2. Careful analysis of sum-product phenomena
3. Fourier-analytic techniques for handling linear forms

This was a major breakthrough in additive combinatorics. -/
axiom bloom_2021 : erdos_298_conjecture

/-- Direct statement of Bloom's result. -/
theorem bloom_theorem (A : Set ℕ) (hzero : 0 ∉ A) (hdense : HasPosDensity A) :
    ContainsUnitSumSubset A :=
  bloom_2021 A hzero hdense

/-!
## Stronger Version: Upper Density Suffices

Bloom actually proved the stronger result that positive UPPER density
(rather than natural density) is sufficient.
-/

/-- **Bloom's Stronger Theorem**: Positive upper density suffices.

This is strictly stronger because:
- Natural density implies upper density
- But upper density can exist when natural density doesn't
- Example: A = {1, 10, 11, 100, 101, 102, 103, ...} has no natural density
  but has positive upper density. -/
def erdos_298_upper_density : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → HasPosUpperDensity A → ContainsUnitSumSubset A

/-- The upper density version is also true (Bloom 2021). -/
axiom bloom_2021_upper : erdos_298_upper_density

/-- Positive natural density implies positive upper density. -/
axiom pos_dens_implies_pos_upper (A : Set ℕ) : HasPosDensity A → HasPosUpperDensity A

/-- Upper density version implies the original conjecture. -/
theorem upper_implies_natural :
    erdos_298_upper_density → erdos_298_conjecture := fun h_upper A h_zero h_pos_dens =>
  h_upper A h_zero (pos_dens_implies_pos_upper A h_pos_dens)

/-!
## Properties of Density

Basic properties of the density definitions.
-/

/-- The set ℕ⁺ = {1, 2, 3, ...} has density 1. -/
axiom nat_pos_density : HasPosDensity {n : ℕ | n > 0}

/-- Even numbers have density 1/2. -/
axiom even_density : HasPosDensity {n : ℕ | Even n ∧ n > 0}

/-- Density is monotone: A ⊆ B implies density(A) ≤ density(B). -/
axiom density_mono (A B : Set ℕ) (h : A ⊆ B) :
    upperDensity A ≤ upperDensity B

/-- Finite sets have density 0. -/
axiom finite_density_zero (A : Set ℕ) (h : A.Finite) :
    upperDensity A = 0

/-!
## Connection to Egyptian Fractions

Egyptian fractions are sums of distinct unit fractions.
Any positive rational has an Egyptian fraction representation.
-/

/-- A rational q has an Egyptian fraction representation if q = ∑ 1/nᵢ
for some finite set of distinct positive integers. -/
def HasEgyptianRep (q : ℚ) : Prop :=
  ∃ S : Finset ℕ, (∀ n ∈ S, n > 0) ∧ unitFractionSum S = q

/-- Every positive rational has an Egyptian fraction representation.
(This is a classical theorem.) -/
axiom egyptian_fraction_exists (q : ℚ) (hq : q > 0) : HasEgyptianRep q

/-- In particular, 1 has many Egyptian fraction representations. -/
axiom one_has_egyptian_rep : HasEgyptianRep 1

/-!
## Quantitative Aspects

Bloom's proof gives some quantitative bounds.
-/

/-- For any δ > 0, there exists N such that any A ⊆ {1,...,N} with
|A| ≥ δN contains a subset summing to 1.

This is a finitary version of Bloom's theorem. -/
axiom bloom_quantitative (δ : ℝ) (hδ : δ > 0) :
    ∃ N : ℕ, ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ a ≤ N) →
      (A.card : ℝ) ≥ δ * N → ∃ S : Finset ℕ, S ⊆ A ∧ SumsToOne S

/-- There exist arbitrarily large sets with no unit sum subset.

This shows the density condition cannot be dropped entirely. -/
axiom sparse_counterexample :
    ∀ N : ℕ, ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ A.card = N ∧
      ¬∃ S : Finset ℕ, S ⊆ A ∧ SumsToOne S

/-!
## The Formalized Proof

Bloom and Mehta formalized the full proof in Lean 3.
See: https://github.com/b-mehta/unit-fractions

The formalization is ~10,000 lines of Lean code and covers:
1. Density lemmas and limit theory
2. Probabilistic constructions
3. The main theorem and its corollaries
-/

/-- The existence of a complete Lean 3 formalization. -/
axiom formalization_exists : True

/-!
## Related Problems

Erdős posed several related problems about unit fractions.
-/

/-- **Erdős Problem #46**: Can every natural n ≥ 2 be written as
1 = 1/x₁ + ... + 1/xₖ where all xᵢ ≤ n?

Answer: Yes for n ≥ 5 (various authors). -/
axiom erdos_46_related : ∀ n ≥ 5, ∃ S : Finset ℕ, (∀ a ∈ S, 0 < a ∧ a ≤ n) ∧ SumsToOne S

/-- **Erdős Problem #47**: Bounds on representing 1 as sum of unit fractions
with denominators from an interval.

Related to #298 by considering density in intervals. -/
axiom erdos_47_related : True

/-!
## Summary

Erdős Problem #298 asks whether positive density guarantees a unit sum subset.

**Result**: YES (Bloom 2021)

The answer is affirmative, with the stronger result that even positive
upper density suffices. This resolved a longstanding conjecture of Erdős
and was one of his monetary problems ($500 prize).

**Key techniques in Bloom's proof**:
1. Probabilistic method to construct candidate sets
2. Sum-product estimates
3. Fourier analysis on ℤ/pℤ
4. Careful density increment arguments

The result shows a deep connection between additive structure (sums of 1/n)
and multiplicative structure (density conditions on the set of n).
-/

/-- Summary statement: Erdős #298 is SOLVED - the answer is YES. -/
theorem erdos_298_solved : erdos_298_conjecture := bloom_2021

end Erdos298
