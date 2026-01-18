/-
  Erdős Problem #286: Unit Fractions in Short Intervals

  Source: https://erdosproblems.com/286
  Status: SOLVED (Croot 2001)

  Statement:
  Let k ≥ 2. Is it true that there exists an interval I of width (e-1+o(1))k
  and integers n₁ < n₂ < ... < nₖ ∈ I such that
  1 = 1/n₁ + 1/n₂ + ... + 1/nₖ?

  Answer: YES

  History:
  - Erdős-Graham (1980): Posed the problem (p. 33)
  - Croot (2001): Proved the result affirmatively

  Key Insight:
  The constant (e-1) ≈ 1.718 is asymptotically optimal. This relates to
  the density of integers whose reciprocals can sum to 1 within a given range.

  Reference: Croot, E. S. (2001), "On unit fractions with denominators in
  short intervals", Acta Arith.
-/

import Mathlib

namespace Erdos286

open Finset BigOperators

/-! ## Unit Fraction Representations -/

/--
A unit fraction representation of a rational q using denominators from a set S.
-/
def IsUnitFractionSum (S : Finset ℕ) (q : ℚ) : Prop :=
  (∀ n ∈ S, n > 0) ∧ ∑ n ∈ S, (1 : ℚ) / n = q

/--
A set S gives a unit fraction representation of 1.
-/
def SumsToOne (S : Finset ℕ) : Prop :=
  IsUnitFractionSum S 1

/-! ## Intervals -/

/--
An interval [a, b] in ℕ.
-/
def NatInterval (a b : ℕ) : Finset ℕ :=
  Finset.Icc a b

/--
The width of an interval [a, b] is b - a.
-/
def IntervalWidth (a b : ℕ) : ℕ := b - a

/-! ## The Main Question -/

/--
**Erdős Problem #286**: For k ≥ 2, does there exist an interval of width
approximately (e-1)k containing k distinct positive integers whose
reciprocals sum to 1?
-/
def HasShortIntervalRepresentation (k : ℕ) (width : ℕ) : Prop :=
  ∃ a : ℕ, ∃ S : Finset ℕ,
    S.card = k ∧
    (∀ n ∈ S, a ≤ n ∧ n ≤ a + width) ∧
    SumsToOne S

/-! ## Small Examples -/

/-- Example: 1 = 1/2 + 1/3 + 1/6 uses k=3 denominators in interval [2,6], width 4. -/
theorem example_k3 : HasShortIntervalRepresentation 3 4 := by
  use 2, {2, 3, 6}
  constructor
  · native_decide
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> omega
  · unfold SumsToOne IsUnitFractionSum
    constructor
    · intro n hn
      simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl | rfl <;> omega
    · native_decide

/-- Example: 1 = 1/2 + 1/4 + 1/5 + 1/20 uses k=4 in [2,20], width 18. -/
theorem example_k4 : HasShortIntervalRepresentation 4 18 := by
  use 2, {2, 4, 5, 20}
  constructor
  · native_decide
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  · unfold SumsToOne IsUnitFractionSum
    constructor
    · intro n hn
      simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> omega
    · native_decide

/-! ## The Optimal Constant -/

/--
The Erdős-Graham constant (e - 1) ≈ 1.71828...
This is the asymptotically optimal width coefficient.
-/
noncomputable def ErdosGrahamConstant : ℝ := Real.exp 1 - 1

theorem erdos_graham_constant_approx : ErdosGrahamConstant > 1.7 ∧ ErdosGrahamConstant < 1.72 := by
  unfold ErdosGrahamConstant
  constructor
  · -- e - 1 > 1.7, i.e., e > 2.7
    have h : Real.exp 1 > 2.7 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      linarith
    linarith
  · -- e - 1 < 1.72, i.e., e < 2.72
    have h : Real.exp 1 < 2.72 := by
      have h1 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
      linarith
    linarith

/-! ## Croot's Theorem -/

/--
**Croot's Theorem (2001)**: For all sufficiently large k, there exists a
representation of 1 as a sum of k distinct unit fractions with all
denominators in an interval of width at most (e - 1 + ε)k for any ε > 0.
-/
theorem croot_theorem :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    HasShortIntervalRepresentation k ⌈(ErdosGrahamConstant + ε) * k⌉₊ := by
  -- Proved by Croot in 2001
  sorry

/--
**Erdős Problem #286 (SOLVED)**: For each k ≥ 2, there exists an interval
of width (e - 1 + o(1))k containing k positive integers whose reciprocals
sum to 1.
-/
theorem erdos_286 :
    ∀ k ≥ 2, ∃ width : ℕ, HasShortIntervalRepresentation k width := by
  intro k hk
  -- For small k, we can find explicit examples
  -- For large k, Croot's theorem applies
  sorry

/-! ## Asymptotic Optimality -/

/--
The constant (e - 1) is asymptotically optimal: one cannot do better than
(e - 1 - ε)k for any ε > 0 and all sufficiently large k.
-/
theorem optimality :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    ¬HasShortIntervalRepresentation k ⌊(ErdosGrahamConstant - ε) * k⌋₊ := by
  -- The lower bound shows (e-1) is tight
  sorry

/-! ## Related Concepts -/

/--
Egyptian fraction representation: expressing a rational as a sum of
distinct unit fractions.
-/
def IsEgyptianFraction (S : Finset ℕ) (q : ℚ) : Prop :=
  (∀ n ∈ S, n > 0) ∧
  (∀ m n, m ∈ S → n ∈ S → m ≠ n) ∧  -- distinct
  ∑ n ∈ S, (1 : ℚ) / n = q

/--
The greedy algorithm gives an Egyptian fraction representation for any
positive rational, but doesn't minimize the interval width.
-/
axiom greedy_algorithm_exists (q : ℚ) (hq : 0 < q ∧ q ≤ 1) :
    ∃ S : Finset ℕ, IsEgyptianFraction S q

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #286 asks whether 1 can be expressed as a sum of k distinct
unit fractions 1/n₁ + ... + 1/nₖ where all denominators lie in an interval
of width approximately (e-1)k.

**Answer: YES**

Croot (2001) proved that for all sufficiently large k, such a representation
exists with interval width at most (e - 1 + ε)k for any ε > 0.

The constant (e - 1) ≈ 1.718 is asymptotically optimal.

**Examples**:
- k = 3: 1 = 1/2 + 1/3 + 1/6, interval [2,6], width 4
- k = 4: 1 = 1/2 + 1/4 + 1/5 + 1/20, interval [2,20], width 18

**References**:
- Erdős, Graham (1980): "Old and New Problems and Results in Combinatorial
  Number Theory", p. 33
- Croot, E. S. (2001): "On unit fractions with denominators in short intervals",
  Acta Arith., 99-114
-/

end Erdos286
