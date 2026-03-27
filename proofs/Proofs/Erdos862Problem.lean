/-
  Erdős Problem #862: Maximal Sidon Subsets

  Source: https://erdosproblems.com/862
  Status: SOLVED (Saxton-Thomason, 2015)

  Statement:
  Let A₁(N) be the number of maximal Sidon subsets of {1,...,N}.
  1. Is it true that A₁(N) < 2^{o(N^{1/2})}?
  2. Is it true that A₁(N) > 2^{N^c} for some constant c > 0?

  Answer: YES to the second question - A₁(N) ≥ 2^{(0.16+o(1))N^{1/2}}
  The first question is answered NO - the lower bound refutes it.

  A Sidon set (or B₂ sequence) is a set where all pairwise sums are distinct.
  A maximal Sidon set is one that cannot be extended while maintaining the
  Sidon property.

  Historical Background:
  - Cameron-Erdős (1992): Posed this problem
  - Saxton-Thomason (2015): Proved A(N) ≥ 2^{(1.16+o(1))√N} via containers
  - Since each maximal Sidon set contains ≤ 2^{(1+o(1))√N} Sidon subsets,
    we get A₁(N) ≥ 2^{(0.16+o(1))√N}

  References:
  - Cameron, P.J. and Erdős, P. (1992): Notes on sum-free and related sets
  - Saxton, D. and Thomason, A. (2015): Hypergraph containers, Invent. Math. 925-992

  Tags: combinatorics, sidon-sets, extremal-combinatorics, container-method
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Set Finset

namespace Erdos862

/- ## Part I: Sidon Sets - Basic Definitions -/

/-- A set S is a Sidon set (B₂ sequence) if all pairwise sums are distinct -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/-- The set {1, ..., N} -/
def Interval (N : ℕ) : Finset ℕ := Finset.range (N + 1) \ {0}

/-- A Sidon subset of {1, ..., N} -/
def SidonSubset (N : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Interval N ∧ IsSidonSet S

/- ## Part II: Maximal Sidon Sets -/

/-- A Sidon set is maximal if no element can be added while preserving Sidon property -/
def IsMaximalSidonSet (N : ℕ) (S : Finset ℕ) : Prop :=
  SidonSubset N S ∧
  ∀ x ∈ Interval N, x ∉ S → ¬IsSidonSet (insert x S)

/-- A₁(N) = number of maximal Sidon subsets of {1,...,N} -/
noncomputable def A₁ (N : ℕ) : ℕ :=
  (Finset.powerset (Interval N)).filter (fun S => IsMaximalSidonSet N S) |>.card

/-- A(N) = number of all Sidon subsets of {1,...,N} -/
noncomputable def A (N : ℕ) : ℕ :=
  (Finset.powerset (Interval N)).filter (fun S => SidonSubset N S) |>.card

/- ## Part III: Size of Largest Sidon Set -/

/-- f(N) = size of largest Sidon subset of {1,...,N} -/
noncomputable def f (N : ℕ) : ℕ :=
  Finset.sup ((Finset.powerset (Interval N)).filter (fun S => SidonSubset N S))
    Finset.card

/- ## Part IV: The Cameron-Erdős Questions -/

/-- Question 1: Is A₁(N) < 2^{o(N^{1/2})}? -/
def CameronErdosQuestion1 : Prop :=
  ∀ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (A₁ N : ℝ) < 2 ^ (c * Real.sqrt N)

/-- Question 2: Is A₁(N) > 2^{N^c} for some c > 0? -/
def CameronErdosQuestion2 : Prop :=
  ∃ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (A₁ N : ℝ) > 2 ^ (N : ℝ) ^ c

/- ## Part V: Saxton-Thomason Theorem (2015) -/

/- ## Part VI: The Main Result -/

/-- Main Theorem: A₁(N) ≥ 2^{(0.16+o(1))N^{1/2}} -/
axiom erdos_862_main :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (A₁ N : ℝ) ≥ 2 ^ ((0.16 - ε) * Real.sqrt N)

/-- Question 2 is answered positively: A₁(N) > 2^{N^c} for some c > 0 -/
axiom question2_positive : CameronErdosQuestion2

/-- The answer to Question 1 is NO: A₁(N) is not < 2^{o(√N)} -/
axiom question1_negative : ¬CameronErdosQuestion1

/- ## Part VII: Upper Bound -/

/- ## Part VIII: B_h Generalizations -/

/-- B_h sequences generalize Sidon sets -/
def IsBhSet (h : ℕ) (S : Finset ℕ) : Prop :=
  h ≥ 2 ∧ ∀ (multiset1 multiset2 : Finset ℕ),
    multiset1 ⊆ S → multiset2 ⊆ S →
    multiset1.card = h → multiset2.card = h →
    multiset1.sum = multiset2.sum → multiset1 = multiset2

/- ## Part IX: Summary -/

/-- Erdős Problem #862: Complete Summary

    Q1: Is A₁(N) < 2^{o(√N)}? Answer: NO.
    Q2: Is A₁(N) > 2^{N^c} for some c > 0? Answer: YES.
    Precise: A₁(N) ≥ 2^{(0.16+o(1))√N} (Saxton-Thomason 2015). -/
theorem erdos_862_summary :
    CameronErdosQuestion2 ∧
    ¬CameronErdosQuestion1 ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (A₁ N : ℝ) ≥ 2 ^ ((0.16 - ε) * Real.sqrt N)) :=
  ⟨question2_positive, question1_negative, erdos_862_main⟩

end Erdos862
