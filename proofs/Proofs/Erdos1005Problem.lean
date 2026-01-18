/-
Erdős Problem #1005: Farey Fractions and Similar Ordering

Let a₁/b₁, a₂/b₂, ... be the Farey fractions of order n ≥ 4.
Let f(n) be the largest integer such that if 1 ≤ k < l ≤ k + f(n)
then a_k/b_k and a_l/b_l are "similarly ordered": (a_k - a_l)(b_k - b_l) ≥ 0.

Estimate f(n). Is there a constant c > 0 such that f(n) = (c + o(1))n?

**Status**: OPEN
**Known**: (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1) (van Doorn 2025)

Reference: https://erdosproblems.com/1005
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

open Finset

namespace Erdos1005

/-!
## Farey Fractions

The Farey sequence F_n consists of all reduced fractions a/b
with 0 ≤ a ≤ b ≤ n and gcd(a,b) = 1, in increasing order.
-/

/-- A Farey fraction is a pair (a, b) with gcd(a, b) = 1 and 0 ≤ a ≤ b. -/
structure FareyFraction where
  num : ℕ
  denom : ℕ
  denom_pos : denom > 0
  num_le_denom : num ≤ denom
  coprime : Nat.Coprime num denom

/-- The Farey sequence of order n: all Farey fractions with denominator ≤ n. -/
def fareySequence (n : ℕ) : Finset FareyFraction :=
  sorry  -- Complex construction of ordered Farey fractions

/-- The number of Farey fractions of order n. -/
def fareyCount (n : ℕ) : ℕ := (fareySequence n).card

/-- Farey count is asymptotically 3n²/π². -/
axiom farey_count_asymptotic (n : ℕ) :
  ∃ C : ℝ, |fareyCount n - 3 * n^2 / Real.pi^2| ≤ C * n * Real.log n

/-!
## Similarly Ordered Fractions

Two fractions a/b and c/d are similarly ordered if (a-c)(b-d) ≥ 0.
This means: either both numerator and denominator increase together,
or both decrease together.
-/

/-- Two Farey fractions are similarly ordered if (a-c)(b-d) ≥ 0. -/
def similarlyOrdered (f g : FareyFraction) : Prop :=
  (f.num : ℤ) - g.num ≥ 0 ∧ (f.denom : ℤ) - g.denom ≥ 0 ∨
  (f.num : ℤ) - g.num ≤ 0 ∧ (f.denom : ℤ) - g.denom ≤ 0

/-- Similarly ordered is symmetric. -/
lemma similarlyOrdered_symm (f g : FareyFraction) :
    similarlyOrdered f g ↔ similarlyOrdered g f := by
  sorry

/-- Similarly ordered is reflexive. -/
lemma similarlyOrdered_refl (f : FareyFraction) : similarlyOrdered f f := by
  left
  constructor <;> linarith

/-!
## Consecutive Similarly Ordered Runs

A run of consecutive Farey fractions is similarly ordered if every
pair in the run satisfies the similarly ordered property.
-/

/-- The Farey sequence as a list (for indexing). -/
def fareyList (n : ℕ) : List FareyFraction :=
  sorry  -- Ordered list of Farey fractions

/-- A run of length k starting at index i is similarly ordered. -/
def isSimOrdered (n : ℕ) (i k : ℕ) : Prop :=
  ∀ j₁ j₂, i ≤ j₁ → j₁ < j₂ → j₂ ≤ i + k →
    ∀ f₁ f₂, (fareyList n).get? j₁ = some f₁ →
             (fareyList n).get? j₂ = some f₂ →
             similarlyOrdered f₁ f₂

/-!
## The Function f(n)

f(n) is the largest length of a consecutive similarly ordered run.
-/

/-- f(n) = max length of consecutive similarly ordered Farey fractions. -/
noncomputable def mayerErdosF (n : ℕ) : ℕ :=
  Nat.find (⟨0, by simp⟩ : ∃ k, ∀ i, ¬isSimOrdered n i (k + 1))
  -- Largest k such that some run of length k is similarly ordered

/-!
## Historical Results

The study of f(n) began with Mayer (1942) and Erdős (1943).
-/

/-- Mayer (1942): f(n) → ∞ as n → ∞. -/
axiom mayer_theorem : Filter.Tendsto mayerErdosF Filter.atTop Filter.atTop

/-- Erdős (1943): f(n) grows at least linearly in n. -/
axiom erdos_1943_linear : ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (mayerErdosF n : ℝ) ≥ c * n

/-!
## Modern Bounds (van Doorn 2025)

van Doorn established the best known bounds for f(n).
-/

/-- van Doorn (2025): Lower bound f(n) ≥ (1/12 - o(1))n. -/
axiom vanDoorn_lower_bound :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, (mayerErdosF n : ℝ) ≥ (1/12 - ε) * n

/-- van Doorn (2025): Upper bound f(n) ≤ n/4 + O(1). -/
axiom vanDoorn_upper_bound :
  ∃ C : ℝ, ∀ n : ℕ, (mayerErdosF n : ℝ) ≤ n / 4 + C

/-- Combined: (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1). -/
theorem vanDoorn_bounds :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, (mayerErdosF n : ℝ) ≥ (1/12 - ε) * n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (mayerErdosF n : ℝ) ≤ n / 4 + C) :=
  ⟨vanDoorn_lower_bound, vanDoorn_upper_bound⟩

/-!
## The Main Conjecture (OPEN)

The central question is whether f(n) has a precise asymptotic.
-/

/-- OPEN: Does there exist c > 0 with f(n) = (c + o(1))n? -/
def hasAsymptoticConstant : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N,
    |(mayerErdosF n : ℝ) / n - c| < ε

/-- van Doorn's conjecture: c = 1/4 is optimal. -/
def vanDoornConjecture : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |(mayerErdosF n : ℝ) / n - 1/4| < ε

/-- The main question: Does f(n) have an asymptotic constant? -/
def erdos_1005_question : Prop := hasAsymptoticConstant

-- The problem is OPEN - we cannot prove or disprove this
-- axiom erdos_1005_holds : erdos_1005_question

/-!
## Mediant Property of Farey Fractions

Farey fractions have special properties that constrain similar ordering.
-/

/-- The mediant of two fractions a/b and c/d is (a+c)/(b+d). -/
def mediant (f g : FareyFraction) : ℚ :=
  (f.num + g.num) / (f.denom + g.denom)

/-- Adjacent Farey fractions satisfy |ad - bc| = 1. -/
axiom farey_adjacent_property (n : ℕ) (i : ℕ) :
  ∀ f g, (fareyList n).get? i = some f →
         (fareyList n).get? (i + 1) = some g →
         (f.num : ℤ) * g.denom - f.denom * g.num = 1 ∨
         (f.num : ℤ) * g.denom - f.denom * g.num = -1

/-!
## Geometric Interpretation

Similarly ordered fractions correspond to points in the Stern-Brocot
tree that lie on monotone paths.
-/

/-- A fraction corresponds to a point (a, b) in ℤ². -/
def toPoint (f : FareyFraction) : ℤ × ℤ := (f.num, f.denom)

/-- Similarly ordered = monotone in both coordinates. -/
theorem similarlyOrdered_iff_monotone (f g : FareyFraction) :
    similarlyOrdered f g ↔
    (toPoint f).1 ≤ (toPoint g).1 ∧ (toPoint f).2 ≤ (toPoint g).2 ∨
    (toPoint f).1 ≥ (toPoint g).1 ∧ (toPoint f).2 ≥ (toPoint g).2 := by
  sorry

/-!
## Why the Gap Between 1/12 and 1/4?

The gap between lower and upper bounds suggests complex structure
in how Farey fractions are ordered.
-/

/-- The ratio of bounds is 3:1. -/
theorem bounds_ratio : (1 : ℝ) / 4 / (1 / 12) = 3 := by norm_num

/-- Closing the gap requires understanding local structure of Farey sequence. -/
theorem gap_significance :
    (1 : ℝ) / 4 - 1 / 12 = 1 / 6 := by norm_num

/-!
## Summary

This file formalizes Erdős Problem #1005 on similarly ordered Farey fractions.

**Status**: OPEN

**The Question**: For Farey fractions of order n, let f(n) be the longest
run of consecutive similarly ordered fractions. Is there c > 0 with
f(n) = (c + o(1))n?

**Known Results**:
- Mayer (1942): f(n) → ∞
- Erdős (1943): f(n) ≫ n (linear growth)
- van Doorn (2025): (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1)

**Conjecture**: c = 1/4 (van Doorn)

**Open Problems**:
- Determine the exact asymptotic constant c
- Close the gap between 1/12 and 1/4
- Understand the structure of maximal similarly ordered runs
-/

end Erdos1005
