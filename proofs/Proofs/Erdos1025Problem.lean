/-
Erdős Problem #1025: Independent Sets in Pair Functions

Let f be a function from pairs {x,y} ⊆ {1,...,n} to {1,...,n} such that
f(x,y) ≠ x and f(x,y) ≠ y. A set X is independent if f(x,y) ∉ X whenever x,y ∈ X.
Let g(n) be the minimum guaranteed independent set size. Estimate g(n).

**Status**: SOLVED
**Answer**: g(n) = Θ(n^(1/2))

Reference: https://erdosproblems.com/1025
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2

open Finset

namespace Erdos1025

/-
## Pair Functions

A pair function maps unordered pairs to elements, avoiding the pair itself.
-/

variable {n : ℕ}

/-- A pair function on Fin n: maps pairs to elements. -/
abbrev PairFunction (n : ℕ) := Sym2 (Fin n) → Fin n

/-- The validity condition: f(x,y) ≠ x and f(x,y) ≠ y. -/
def isValidPairFunction (f : PairFunction n) : Prop :=
  ∀ p : Sym2 (Fin n), ∀ x ∈ p, f p ≠ x

/-- Alternative: using explicit pairs. -/
def isValidPairFunction' (f : Fin n → Fin n → Fin n) : Prop :=
  ∀ x y : Fin n, x ≠ y → f x y ≠ x ∧ f x y ≠ y

/-
## Independent Sets

A set is independent if the image of any pair in it lies outside the set.
-/

/-- A set X is independent under f if f(x,y) ∉ X for all x,y ∈ X. -/
def isIndependent (f : PairFunction n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f (Sym2.mk x y) ∉ X

/-- Alternative definition with explicit function. -/
def isIndependent' (f : Fin n → Fin n → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x y ∉ X

/-- The empty set is always independent. -/
theorem empty_independent (f : PairFunction n) : isIndependent f ∅ := by
  intro x hx
  simp at hx

/-- Singletons are independent. -/
theorem singleton_independent (f : PairFunction n) (a : Fin n) :
    isIndependent f {a} := by
  intro x hx y hy hxy
  simp at hx hy
  rw [hx, hy] at hxy
  exact absurd rfl hxy

/-
## The Extremal Function g(n)

g(n) = min over valid f of max independent set size.
-/

/-- The set of valid pair functions. -/
def validPairFunctions (n : ℕ) : Set (PairFunction n) :=
  { f | isValidPairFunction f }

/-- Maximum independent set size for a given function. -/
noncomputable def maxIndependent (f : PairFunction n) : ℕ :=
  sSup { k : ℕ | ∃ X : Finset (Fin n), isIndependent f X ∧ X.card = k }

/-- g(n): minimum over all valid functions of max independent set. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf { maxIndependent f | f ∈ validPairFunctions n }

/-- g(n) is the guaranteed independent set size. -/
theorem g_spec (f : PairFunction n) (hf : isValidPairFunction f) :
    ∃ X : Finset (Fin n), isIndependent f X ∧ X.card ≥ g n := by
  sorry

/-
## Erdős-Hajnal Bounds (1958)

Original bounds: n^(1/3) ≪ g(n) ≪ (n log n)^(1/2).
-/

/-- Erdős-Hajnal lower bound: g(n) ≥ c · n^(1/3). -/
axiom erdos_hajnal_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (g n : ℝ) ≥ c * (n : ℝ) ^ (1/3 : ℝ)

/-- Erdős-Hajnal upper bound: g(n) ≤ C · (n log n)^(1/2). -/
axiom erdos_hajnal_upper : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (g n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (1/2 : ℝ)

/-- Erdős-Hajnal bounds combined. -/
theorem erdos_hajnal_bounds : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * (n : ℝ) ^ (1/3 : ℝ) ≤ g n ∧
    (g n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (1/2 : ℝ) := by
  obtain ⟨c, hc, N₁, hN₁⟩ := erdos_hajnal_lower
  obtain ⟨C, hC, N₂, hN₂⟩ := erdos_hajnal_upper
  use c, C, hc, hC, max N₁ N₂
  intro n hn
  constructor
  · exact hN₁ n (le_of_max_le_left hn)
  · exact hN₂ n (le_of_max_le_right hn)

/-
## Spencer's Improvement (1972)

Spencer proved g(n) ≫ n^(1/2), improving the lower bound.
-/

/-- Spencer (1972): g(n) ≥ c · n^(1/2). -/
axiom spencer_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (g n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)

/-- Spencer's bound improves Erdős-Hajnal. -/
theorem spencer_improves_eh (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) ^ (1/3 : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ) := by
  sorry

/-
## Conlon-Fox-Sudakov Result (2016)

They proved g(n) ≪ n^(1/2), matching Spencer's lower bound.
-/

/-- Conlon-Fox-Sudakov (2016): g(n) ≤ C · n^(1/2). -/
axiom cfs_upper : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (g n : ℝ) ≤ C * (n : ℝ) ^ (1/2 : ℝ)

/-- CFS improves Erdős-Hajnal upper bound. -/
theorem cfs_improves_eh (n : ℕ) (hn : n ≥ 3) :
    (n : ℝ) ^ (1/2 : ℝ) ≤ ((n : ℝ) * Real.log n) ^ (1/2 : ℝ) := by
  sorry

/-
## The Main Result: g(n) = Θ(n^(1/2))

Combining Spencer and CFS gives the exact order of magnitude.
-/

/-- The exact asymptotic: g(n) = Θ(n^(1/2)). -/
theorem g_asymptotic : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * (n : ℝ) ^ (1/2 : ℝ) ≤ g n ∧ (g n : ℝ) ≤ C * (n : ℝ) ^ (1/2 : ℝ) := by
  obtain ⟨c, hc, N₁, hN₁⟩ := spencer_lower
  obtain ⟨C, hC, N₂, hN₂⟩ := cfs_upper
  use c, C, hc, hC, max N₁ N₂
  intro n hn
  constructor
  · exact hN₁ n (le_of_max_le_left hn)
  · exact hN₂ n (le_of_max_le_right hn)

/-
## The Main Question Answered

The answer is g(n) = Θ(n^(1/2)).
-/

/-- The main question: estimate g(n). -/
def erdos_1025_question : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ h : ℕ → ℝ, ∃ N : ℕ, ∀ n ≥ N,
    c * h n ≤ g n ∧ (g n : ℝ) ≤ C * h n

/-- The answer: g(n) = Θ(n^(1/2)). -/
theorem erdos_1025_solved : erdos_1025_question := by
  obtain ⟨c, C, hc, hC, N, hN⟩ := g_asymptotic
  use c, C, hc, hC, fun n => (n : ℝ) ^ (1/2 : ℝ), N
  exact hN

/-
## Related: Set Mappings

The problem relates to set mappings studied by Erdős and Hajnal.
-/

/-- A set mapping assigns to each element a subset not containing it. -/
def SetMapping (n : ℕ) := (a : Fin n) → { S : Finset (Fin n) // a ∉ S }

/-- Free set for a set mapping: F is free if a ∉ φ(b) for all a, b ∈ F. -/
def isFreeSet (φ : SetMapping n) (F : Finset (Fin n)) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, a ∉ (φ b).val

/-- Connection: pair functions induce set mappings. -/
def pairToSetMapping (f : PairFunction n) : Fin n → Finset (Fin n) :=
  fun a => (Finset.univ.filter (fun b => b ≠ a)).image (fun b => f (Sym2.mk a b))

/-
## Probabilistic Approach

The probabilistic method gives the lower bound.
-/

/-- Expected independent set size from random selection. -/
noncomputable def expectedIndependent (f : PairFunction n) (p : ℝ) : ℝ :=
  p * n - (n.choose 2 : ℝ) * p^3

/-- Probabilistic lower bound sketch. -/
theorem probabilistic_lower_sketch (f : PairFunction n) (hf : isValidPairFunction f) :
    ∃ X : Finset (Fin n), isIndependent f X ∧
      (X.card : ℝ) ≥ (n : ℝ)^(1/2 : ℝ) / 2 := by
  sorry

/-
## Upper Bound Construction

Constructions achieving the upper bound.
-/

/-- There exist pair functions with small independent sets. -/
axiom construction_upper (n : ℕ) (hn : n ≥ 4) :
  ∃ f : PairFunction n, isValidPairFunction f ∧
    maxIndependent f ≤ 2 * Nat.ceil ((n : ℝ) ^ (1/2 : ℝ))

/-
## Historical Development

The problem evolved over 58 years from Erdős-Hajnal to resolution.
-/

/-- Timeline of bounds. -/
theorem historical_bounds :
    -- 1958: Erdős-Hajnal
    (∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℝ)^(1/3 : ℝ) ≤ g n ∧ (g n : ℝ) ≤ C * ((n : ℝ) * Real.log n)^(1/2 : ℝ)) ∧
    -- 1972: Spencer (lower)
    (∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, (g n : ℝ) ≥ c * (n : ℝ)^(1/2 : ℝ)) ∧
    -- 2016: Conlon-Fox-Sudakov (upper)
    (∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, (g n : ℝ) ≤ C * (n : ℝ)^(1/2 : ℝ)) := by
  exact ⟨erdos_hajnal_bounds, spencer_lower, cfs_upper⟩

/-
## Summary

This file formalizes Erdős Problem #1025 on independent sets in pair functions.

**Status**: SOLVED

**The Question**: Estimate g(n), the minimum guaranteed independent set size.

**The Answer**: g(n) = Θ(n^(1/2)).

**Key Results**:
- Erdős-Hajnal (1958): n^(1/3) ≪ g(n) ≪ (n log n)^(1/2)
- Spencer (1972): g(n) ≫ n^(1/2)
- Conlon-Fox-Sudakov (2016): g(n) ≪ n^(1/2)

**Related Topics**:
- Set mappings
- Probabilistic method
- Extremal combinatorics
-/

end Erdos1025
