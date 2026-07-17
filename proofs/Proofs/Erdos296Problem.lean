/-
  Erdős Problem #296: Disjoint Unit Fraction Partitions

  Source: https://erdosproblems.com/296
  Status: SOLVED (Hunter-Sawhney via Bloom 2021)

  Statement:
  Let N ≥ 1 and let k(N) be maximal such that there exist k disjoint sets
  A₁, ..., Aₖ ⊆ {1, ..., N} with Σ_{n ∈ Aᵢ} 1/n = 1 for all i.

  Estimate k(N). Is it true that k(N) = o(log N)?

  Background:
  This problem asks: how many disjoint "Egyptian fraction representations of 1"
  can we pack into {1, ..., N}? Each set Aᵢ must have its reciprocals sum to
  exactly 1 (like 1/2 + 1/3 + 1/6 = 1), and the sets must be disjoint.

  The question was whether k(N) grows sublogarithmically in N, or whether
  it can achieve essentially logarithmic growth.

  Key Results:
  • Sunflower method: Can find at least N·exp(-O(√(log N))) disjoint sets
    with equal reciprocal sums
  • Hunter-Sawhney (via Bloom 2021): k(N) = (1 - o(1))·log N

  Resolution:
  The answer to Erdős's question is NO: k(N) is NOT o(log N).
  Instead, k(N) = (1 - o(1))·log N, meaning it grows essentially as fast
  as log N allows. The greedy algorithm combined with Bloom's Theorem 3
  achieves this bound.

  References:
  [ErGr80] Erdős, P. and Graham, R. "Old and New Problems in Combinatorial
           Number Theory" (1980)
  [Bl21] Bloom, T.F. "On a density conjecture about unit fractions"
         arXiv:2112.03726 (2021)

  Tags: number-theory, unit-fractions, egyptian-fractions, packing
-/

import Mathlib

open Finset BigOperators

/-
## Unit Fraction Sums

A set of positive integers whose reciprocals sum to exactly 1.
-/

/-- The reciprocal sum of a finite set of positive integers -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

/-- A set of positive integers is a "unit set" if its reciprocals sum to 1 -/
def isUnitSet (A : Finset ℕ) : Prop :=
  (∀ n ∈ A, n ≥ 1) ∧ reciprocalSum A = 1

/-- Example: {2, 3, 6} is a unit set since 1/2 + 1/3 + 1/6 = 1 -/
example : reciprocalSum {2, 3, 6} = 1 := by
  simp only [reciprocalSum, sum_insert, mem_insert, mem_singleton]
  norm_num

/-
## Disjoint Unit Set Packings

A collection of disjoint sets, each summing to 1.
-/

/-- A collection of sets is pairwise disjoint -/
def arePairwiseDisjoint (sets : List (Finset ℕ)) : Prop :=
  ∀ i j (hi : i < sets.length) (hj : j < sets.length), i ≠ j →
    Disjoint (sets.get ⟨i, hi⟩) (sets.get ⟨j, hj⟩)

/-- A valid packing: disjoint unit sets within {1, ..., N} -/
structure UnitSetPacking (N : ℕ) where
  sets : List (Finset ℕ)
  all_unit : ∀ i (h : i < sets.length), isUnitSet (sets.get ⟨i, h⟩)
  all_in_range : ∀ i (h : i < sets.length), ∀ n ∈ (sets.get ⟨i, h⟩), n ≤ N
  disjoint : arePairwiseDisjoint sets

/-- The size of a packing is the number of sets -/
def UnitSetPacking.size (p : UnitSetPacking N) : ℕ := p.sets.length

/-
## The Function k(N)

k(N) = maximum number of disjoint unit sets within {1, ..., N}.
-/

/-- k(N): maximum size of a unit set packing in {1, ..., N} -/
noncomputable def k (N : ℕ) : ℕ :=
  sSup { p.size | p : UnitSetPacking N }

/-
## Basic Bounds
-/

/-  k(N) ≥ 1 for N ≥ 6 (since {2,3,6} works) -/
/-  k(N) ≤ N (trivial upper bound: can't have more sets than elements) -/
/-
## Sunflower Lower Bound

Using the sunflower lemma, one can construct many disjoint sets with equal sums.
-/

/-  Sunflower bound: at least N·exp(-O(√(log N))) disjoint sets exist
    with equal reciprocal sums (not necessarily 1) -/
/-
## Main Result: k(N) = (1 - o(1))·log N

Hunter and Sawhney, using Bloom's Theorem 3, showed k(N) is essentially log N.
-/

/-- Hunter-Sawhney lower bound: k(N) ≥ (1 - ε)·log N for large N -/
axiom hunter_sawhney_lower (ε : ℝ) (hε : ε > 0) :
  ∃ N₀ : ℕ, ∀ N ≥ N₀, (k N : ℝ) ≥ (1 - ε) * Real.log N

/-  Upper bound: k(N) ≤ log N + O(1) -/
/-- Main theorem: k(N) = (1 - o(1))·log N
    Equivalently: k(N) / log N → 1 as N → ∞ -/
axiom erdos_296_main :
  Filter.Tendsto (fun N => (k N : ℝ) / Real.log N) Filter.atTop (nhds 1)

/-
## Answer to Erdős's Question

Erdős asked: Is k(N) = o(log N)? The answer is NO.
-/

/-- k(N) is NOT o(log N) -/
theorem k_not_sublogarithmic :
  ¬(Filter.Tendsto (fun N => (k N : ℝ) / Real.log N) Filter.atTop (nhds 0)) := by
  intro h
  -- k(N)/log N → 1 by erdos_296_main, so it can't also → 0
  have h1 := erdos_296_main
  -- Two different limits in a Hausdorff space is a contradiction
  have : (0 : ℝ) = 1 := tendsto_nhds_unique h h1
  norm_num at this

/-- Corollary: For any ε > 0, k(N) > ε·log N for infinitely many N -/
theorem k_infinitely_often_large (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
  ∀ N₀ : ℕ, ∃ N > N₀, (k N : ℝ) > ε * Real.log N := by
  intro N₀
  have ⟨N₁, hN₁⟩ := hunter_sawhney_lower ((1 - ε) / 2) (by linarith)
  refine ⟨max (max N₀ N₁ + 1) 2, by omega, ?_⟩
  have h := hN₁ (max (max N₀ N₁ + 1) 2) (by omega)
  have h2 : (2 : ℝ) ≤ ((max (max N₀ N₁ + 1) 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ max (max N₀ N₁ + 1) 2)
  have hlog : 0 < Real.log ((max (max N₀ N₁ + 1) 2 : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  calc ((k (max (max N₀ N₁ + 1) 2) : ℕ) : ℝ)
      ≥ (1 - (1 - ε) / 2) * Real.log ((max (max N₀ N₁ + 1) 2 : ℕ) : ℝ) := h
    _ = ((1 + ε) / 2) * Real.log ((max (max N₀ N₁ + 1) 2 : ℕ) : ℝ) := by ring
    _ > ε * Real.log ((max (max N₀ N₁ + 1) 2 : ℕ) : ℝ) :=
        mul_lt_mul_of_pos_right (by linarith) hlog

#check erdos_296_main
#check k_not_sublogarithmic
#check @hunter_sawhney_lower
