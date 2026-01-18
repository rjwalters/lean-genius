/-
Erdős Problem #1028: Discrepancy of Sign Functions

Let H(n) = min_f max_{X ⊆ {1,...,n}} |∑_{x≠y∈X} f(x,y)|, where f ranges over
all functions f: X² → {-1, 1}. Estimate H(n).

**Status**: SOLVED
**Answer**: H(n) = Θ(n^(3/2))

Reference: https://erdosproblems.com/1028
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open Finset

namespace Erdos1028

/-
## Sign Functions

A sign function assigns ±1 to each ordered pair.
-/

/-- A sign function on pairs. -/
abbrev SignFunction (n : ℕ) := Fin n → Fin n → Int

/-- A valid sign function maps to {-1, 1}. -/
def isValidSign (f : SignFunction n) : Prop :=
  ∀ x y : Fin n, f x y = 1 ∨ f x y = -1

/-- The set of valid sign functions. -/
def validSignFunctions (n : ℕ) : Set (SignFunction n) :=
  { f | isValidSign f }

/-
## Discrepancy

The discrepancy of a subset is the absolute value of the sum of f over pairs.
-/

/-- Sum of f(x,y) over distinct pairs in X. -/
def pairSum (f : SignFunction n) (X : Finset (Fin n)) : Int :=
  X.sum (fun x => X.sum (fun y => if x ≠ y then f x y else 0))

/-- The discrepancy of X under f. -/
def discrepancy (f : SignFunction n) (X : Finset (Fin n)) : ℕ :=
  (pairSum f X).natAbs

/-- Maximum discrepancy over all subsets. -/
noncomputable def maxDiscrepancy (f : SignFunction n) : ℕ :=
  sSup { discrepancy f X | X : Finset (Fin n) }

/-
## The Function H(n)

H(n) = min over valid f of max discrepancy.
-/

/-- H(n): minimum over sign functions of maximum discrepancy. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { maxDiscrepancy f | f ∈ validSignFunctions n }

/-- H(n) is well-defined (exists optimal f). -/
theorem H_spec (n : ℕ) (hn : n ≥ 1) :
    ∃ f : SignFunction n, isValidSign f ∧ maxDiscrepancy f = H n := by
  sorry

/-
## Erdős's Bounds (1963)

Erdős proved n/4 ≤ H(n) ≪ n^(3/2).
-/

/-- Erdős lower bound: H(n) ≥ n/4. -/
theorem erdos_lower (n : ℕ) (hn : n ≥ 4) :
    H n ≥ n / 4 := by
  sorry

/-- Erdős upper bound: H(n) ≤ C · n^(3/2). -/
axiom erdos_upper : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (H n : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ)

/-- Erdős's bounds combined. -/
theorem erdos_bounds : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * n ≤ H n ∧ (H n : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  obtain ⟨C, hC, N, hN⟩ := erdos_upper
  use 1/4, C, by norm_num, hC, max 4 N
  intro n hn
  constructor
  · have h4 : n ≥ 4 := le_of_max_le_left hn
    have := erdos_lower n h4
    calc (1/4 : ℝ) * n = n / 4 := by ring
      _ ≤ (n / 4 : ℕ) := by sorry
      _ ≤ H n := this
  · exact hN n (le_of_max_le_right hn)

/-
## Erdős-Spencer Improvement (1971)

They proved H(n) ≫ n^(3/2), matching the upper bound.
-/

/-- Erdős-Spencer (1971): H(n) ≥ c · n^(3/2). -/
axiom erdos_spencer_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (H n : ℝ) ≥ c * (n : ℝ) ^ (3/2 : ℝ)

/-- The Erdős-Spencer bound improves Erdős's linear lower bound. -/
theorem erdos_spencer_improves (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) ≤ (n : ℝ) ^ (3/2 : ℝ) := by
  sorry

/-
## The Main Result: H(n) = Θ(n^(3/2))

Combining bounds gives the exact order of magnitude.
-/

/-- H(n) = Θ(n^(3/2)). -/
theorem H_asymptotic : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * (n : ℝ) ^ (3/2 : ℝ) ≤ H n ∧ (H n : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  obtain ⟨c, hc, N₁, hN₁⟩ := erdos_spencer_lower
  obtain ⟨C, hC, N₂, hN₂⟩ := erdos_upper
  use c, C, hc, hC, max N₁ N₂
  intro n hn
  constructor
  · exact hN₁ n (le_of_max_le_left hn)
  · exact hN₂ n (le_of_max_le_right hn)

/-
## The Main Question Answered

The answer is H(n) = Θ(n^(3/2)).
-/

/-- The main question: estimate H(n). -/
def erdos_1028_question : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ h : ℕ → ℝ, ∃ N : ℕ, ∀ n ≥ N,
    c * h n ≤ H n ∧ (H n : ℝ) ≤ C * h n

/-- The answer: H(n) = Θ(n^(3/2)). -/
theorem erdos_1028_solved : erdos_1028_question := by
  obtain ⟨c, C, hc, hC, N, hN⟩ := H_asymptotic
  use c, C, hc, hC, fun n => (n : ℝ) ^ (3/2 : ℝ), N
  exact hN

/-
## Symmetric Functions

Often we consider symmetric f with f(x,y) = f(y,x).
-/

/-- A symmetric sign function. -/
def isSymmetric (f : SignFunction n) : Prop :=
  ∀ x y : Fin n, f x y = f y x

/-- For symmetric f, pairSum counts each pair twice. -/
theorem symmetric_pairSum (f : SignFunction n) (hf : isSymmetric f) (X : Finset (Fin n)) :
    pairSum f X = 2 * X.sum (fun x => (X.filter (· > x)).sum (fun y => f x y)) := by
  sorry

/-
## Graph Interpretation

f defines a signed complete graph on n vertices.
-/

/-- View f as edge signs on complete graph. -/
def asSignedGraph (f : SignFunction n) : Fin n → Fin n → Int :=
  fun x y => if x ≠ y then f x y else 0

/-- Discrepancy = imbalance of induced subgraph. -/
theorem discrepancy_as_imbalance (f : SignFunction n) (X : Finset (Fin n)) :
    discrepancy f X = (X.sum (fun x => X.sum (fun y => asSignedGraph f x y))).natAbs := by
  sorry

/-
## Probabilistic Intuition

Random sign functions achieve near-optimal discrepancy.
-/

/-- Expected discrepancy of a random subset under random f. -/
noncomputable def expectedDiscrepancy (n k : ℕ) : ℝ :=
  Real.sqrt (k * (k - 1) : ℝ)

/-- For subset of size k, expected discrepancy is O(k). -/
theorem expected_discrepancy_bound (n k : ℕ) (hk : k ≤ n) :
    expectedDiscrepancy n k ≤ k := by
  sorry

/-
## The Upper Bound Construction

Erdős's upper bound uses probabilistic method.
-/

/-- Random sign functions have max discrepancy O(n^(3/2)). -/
axiom random_upper (n : ℕ) (hn : n ≥ 1) :
  ∃ f : SignFunction n, isValidSign f ∧
    (maxDiscrepancy f : ℝ) ≤ 10 * (n : ℝ) ^ (3/2 : ℝ)

/-
## The Lower Bound Technique

Erdős-Spencer used entropy or counting arguments.
-/

/-- Any sign function has some subset with large discrepancy. -/
theorem large_discrepancy_exists (f : SignFunction n) (hf : isValidSign f) (hn : n ≥ 10) :
    ∃ X : Finset (Fin n), (discrepancy f X : ℝ) ≥ (n : ℝ) ^ (3/2 : ℝ) / 100 := by
  sorry

/-
## Special Cases

Small cases and explicit computations.
-/

/-- H(2) = 2 (trivial case). -/
theorem H_two : H 2 = 2 := by
  sorry

/-- H(3) = 4. -/
theorem H_three : H 3 = 4 := by
  sorry

/-
## Connection to Ramsey Theory

The problem connects to Ramsey-type questions.
-/

/-- Large homogeneous subsets have small discrepancy. -/
theorem homogeneous_small_discrepancy (f : SignFunction n) (X : Finset (Fin n))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x y = 1) :
    discrepancy f X = X.card * (X.card - 1) := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1028 on discrepancy of sign functions.

**Status**: SOLVED

**The Question**: Estimate H(n) = min_f max_X |∑_{x≠y∈X} f(x,y)|.

**The Answer**: H(n) = Θ(n^(3/2)).

**Key Results**:
- Erdős (1963): n/4 ≤ H(n) ≪ n^(3/2)
- Erdős-Spencer (1971): H(n) ≫ n^(3/2)

**Related Topics**:
- Discrepancy theory
- Signed graphs
- Ramsey theory
- Probabilistic method
-/

end Erdos1028
