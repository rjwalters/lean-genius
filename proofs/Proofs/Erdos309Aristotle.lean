/-
  Aristotle targets for Erdős Problem #309
  Routine supporting lemmas for automated proof search.
  See Erdos309Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main asymptotic results (Yokota, Croot) or deep analytic bounds
  - Known results provable from Mathlib (cardinality, sums, basic arithmetic)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes: How many integers can be written as sums of
  distinct unit fractions with denominators from {1, ..., N}?
  Answer: F(N) = log N + gamma + O((log log N)^2 / log N).
-/
import Mathlib

namespace Erdos309Aristotle

open Finset BigOperators

/- ## Definitions (mirrored from Erdos309Problem.lean) -/

/-- Unit fraction 1/n for positive n. -/
noncomputable def unitFraction (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / n

/-- Sum of unit fractions over a finite set of denominators. -/
noncomputable def sumUnitFractions (S : Finset ℕ) : ℚ :=
  ∑ d ∈ S, unitFraction d

/-- The denominator range {1, 2, ..., N}. -/
def denominatorRange (N : ℕ) : Finset ℕ := Finset.range (N + 1) \ {0}

/-- The harmonic number H_N = sum of 1/n for n = 1 to N. -/
noncomputable def harmonicNumber (N : ℕ) : ℚ :=
  sumUnitFractions (denominatorRange N)

/-- An integer k is representable using denominators from {1,...,N}. -/
def IsRepresentable (N : ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ denominatorRange N ∧ sumUnitFractions S = k

/- ## Routine Lemmas -/

-- Cardinality
/-- The denominator range {1,...,N} has exactly N elements. -/
theorem denominatorRange_card (N : ℕ) (hN : N ≥ 1) :
    (denominatorRange N).card = N := by sorry

-- Membership
/-- Membership in denominatorRange: 1 ≤ n ∧ n ≤ N. -/
theorem mem_denominatorRange (N n : ℕ) :
    n ∈ denominatorRange N ↔ 1 ≤ n ∧ n ≤ N := by sorry

-- Unit fraction properties
/-- Unit fractions are positive for n ≥ 1. -/
theorem unitFraction_pos (n : ℕ) (hn : n ≥ 1) : unitFraction n > 0 := by sorry

/-- unitFraction 1 = 1. -/
theorem unitFraction_one : unitFraction 1 = 1 := by sorry

/-- unitFraction is decreasing: if m ≤ n then 1/n ≤ 1/m (for positive m). -/
theorem unitFraction_anti (m n : ℕ) (hm : m ≥ 1) (hmn : m ≤ n) :
    unitFraction n ≤ unitFraction m := by sorry

-- Sum properties
/-- The empty sum is 0. -/
theorem sumUnitFractions_empty : sumUnitFractions ∅ = 0 := by sorry

/-- Adding an element to the sum. -/
theorem sumUnitFractions_insert (S : Finset ℕ) (d : ℕ) (hd : d ∉ S) :
    sumUnitFractions (insert d S) = sumUnitFractions S + unitFraction d := by sorry

-- Harmonic number
/-- H_1 = 1. -/
theorem harmonicNumber_one : harmonicNumber 1 = 1 := by sorry

-- Representability
/-- 0 is always representable (empty set). -/
theorem zero_representable (N : ℕ) : IsRepresentable N 0 := by sorry

/-- 1 is representable for N ≥ 1 (using {1}). -/
theorem one_representable (N : ℕ) (hN : N ≥ 1) : IsRepresentable N 1 := by sorry

/-- The maximum representable integer is bounded by H_N. -/
theorem max_representable_le_harmonic (N k : ℕ) (hk : IsRepresentable N k) :
    (k : ℚ) ≤ harmonicNumber N := by sorry

end Erdos309Aristotle
