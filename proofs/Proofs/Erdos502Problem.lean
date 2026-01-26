/-!
# Erdős Problem #502 — Two-Distance Sets in Euclidean Space

Given n, what is the maximum size f(n) of a set A ⊆ ℝⁿ such that the
pairwise distances |{|x - y| : x ≠ y ∈ A}| = 2?

**Status: SOLVED.**

Bannai–Bannai–Stanton (1983) proved f(n) ≤ C(n+2, 2).
A lower bound f(n) ≥ C(n+1, 2) comes from projections of binary vectors.
Petrov–Pohoata (2021) gave a simpler proof of the upper bound.

The problem was posed to Erdős by Coxeter.

Reference: https://erdosproblems.com/502
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Combinatorics.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A two-distance set in ℝⁿ: a finite set where exactly two
    distinct pairwise distances occur. -/
def IsTwoDistanceSet (n : ℕ) (A : Finset (Fin n → ℝ)) : Prop :=
  ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ 0 < d₂ ∧ d₁ ≠ d₂ ∧
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      (dist x y = d₁ ∨ dist x y = d₂)

/-- The maximum size of a two-distance set in ℝⁿ. -/
noncomputable def maxTwoDistSize (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ A : Finset (Fin n → ℝ), A.card = k ∧ IsTwoDistanceSet n A }

/-! ## The Binary Vector Construction -/

/-- Binary vector with exactly two coordinates equal to 1.
    These form a two-distance set of size C(n,2). -/
def binaryTwoVec (n : ℕ) (i j : Fin n) (h : i ≠ j) : Fin n → ℝ :=
  fun k => if k = i ∨ k = j then 1 else 0

/-- The two distances in the binary construction are √2 and 2. -/
axiom binary_two_distances (n : ℕ) (hn : 2 ≤ n)
    (i₁ j₁ i₂ j₂ : Fin n) (h₁ : i₁ ≠ j₁) (h₂ : i₂ ≠ j₂)
    (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    dist (binaryTwoVec n i₁ j₁ h₁) (binaryTwoVec n i₂ j₂ h₂) = Real.sqrt 2 ∨
    dist (binaryTwoVec n i₁ j₁ h₁) (binaryTwoVec n i₂ j₂ h₂) = 2

/-! ## Lower Bound -/

/-- Basic lower bound: f(n) ≥ C(n, 2) from binary vectors. -/
axiom lower_bound_basic (n : ℕ) (hn : 2 ≤ n) :
    n.choose 2 ≤ maxTwoDistSize n

/-- Improved lower bound via projection: f(n) ≥ C(n+1, 2). -/
axiom lower_bound_improved (n : ℕ) (hn : 2 ≤ n) :
    (n + 1).choose 2 ≤ maxTwoDistSize n

/-! ## Upper Bound — Bannai–Bannai–Stanton -/

/-- Bannai–Bannai–Stanton (1983): f(n) ≤ C(n+2, 2).
    Petrov–Pohoata (2021) gave a simpler proof.
    The argument uses the Gram matrix / polynomial method. -/
axiom upper_bound_bbs (n : ℕ) :
    maxTwoDistSize n ≤ (n + 2).choose 2

/-! ## Main Result -/

/-- Combined bounds: C(n+1,2) ≤ f(n) ≤ C(n+2,2). -/
theorem erdos_502_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n + 1).choose 2 ≤ maxTwoDistSize n ∧
    maxTwoDistSize n ≤ (n + 2).choose 2 :=
  ⟨lower_bound_improved n hn, upper_bound_bbs n⟩

/-! ## Small Cases -/

/-- In ℝ², the maximum two-distance set has size 5 (regular pentagon). -/
axiom two_dist_dim2 : maxTwoDistSize 2 = 5

/-- In ℝ³, the maximum two-distance set has size 6. -/
axiom two_dist_dim3 : maxTwoDistSize 3 = 6

/-! ## Coxeter's Original Question -/

/-- Coxeter asked Erdős whether f(n) is polynomial in n.
    The Bannai–Bannai–Stanton bound confirms f(n) = O(n²). -/
theorem coxeter_polynomial_growth (n : ℕ) :
    maxTwoDistSize n ≤ (n + 2).choose 2 :=
  upper_bound_bbs n

/-- Erdős initially claimed f(n) ≤ n^O(1) but found an error,
    only obtaining f(n) ≤ exp(n^{1-o(1)}). The BBS result vindicated
    his original belief. -/
axiom erdos_original_weaker_bound (n : ℕ) (hn : 1 ≤ n) :
    maxTwoDistSize n ≤ Nat.factorial n
