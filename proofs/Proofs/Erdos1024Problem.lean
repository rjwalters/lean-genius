/-
Erdős Problem #1024: Independent Sets in Linear Hypergraphs

Let f(n) be the minimum size of an independent set guaranteed in every
3-uniform linear hypergraph on n vertices. Estimate f(n).

**Status**: SOLVED (Phelps-Rödl 1986)
**Answer**: f(n) ≍ (n log n)^(1/2)

Reference: https://erdosproblems.com/1024
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace Erdos1024

/-
## Hypergraphs

A hypergraph is a collection of edges, where each edge is a set of vertices.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A hypergraph is a collection of edges (sets of vertices). -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- The vertex set of a hypergraph. -/
def vertices (H : Hypergraph V) : Finset V :=
  H.sup id

/-- A hypergraph is k-uniform if all edges have exactly k vertices. -/
def isKUniform (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H, e.card = k

/-- A 3-uniform hypergraph. -/
def is3Uniform (H : Hypergraph V) : Prop := isKUniform H 3

/-
## Linear Hypergraphs

A hypergraph is linear if any two edges share at most one vertex.
-/

/-- A hypergraph is linear if |A ∩ B| ≤ 1 for all distinct edges A, B. -/
def isLinear (H : Hypergraph V) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1

/-- A 3-uniform linear hypergraph (partial Steiner triple system). -/
def is3UniformLinear (H : Hypergraph V) : Prop :=
  is3Uniform H ∧ isLinear H

/-
## Independent Sets

An independent set contains no complete edge.
-/

/-- A set S is independent in H if no edge of H is contained in S. -/
def isIndependent (H : Hypergraph V) (S : Finset V) : Prop :=
  ∀ e ∈ H, ¬(e ⊆ S)

/-- The independence number: largest independent set. -/
noncomputable def independenceNumber (H : Hypergraph V) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset V, isIndependent H S ∧ S.card = k }

/-- Every hypergraph has an independent set (the empty set). -/
theorem exists_independent (H : Hypergraph V) : ∃ S : Finset V, isIndependent H S := by
  use ∅
  intro e _ he
  simp at he

/-
## The Extremal Function f(n)

f(n) = min over all 3-uniform linear hypergraphs H on n vertices of α(H).
-/

/-- The set of 3-uniform linear hypergraphs on Fin n. -/
def linearHypergraphs3 (n : ℕ) : Set (Hypergraph (Fin n)) :=
  { H | is3UniformLinear H }

/-- f(n): minimum independence number over all 3-uniform linear hypergraphs. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf { independenceNumber H | H ∈ linearHypergraphs3 n }

/-- f(n) is the guaranteed independent set size. -/
theorem f_spec (n : ℕ) (H : Hypergraph (Fin n)) (hH : is3UniformLinear H) :
    independenceNumber H ≥ f n := by
  sorry

/-
## Erdős's Bounds

Erdős proved: n^(1/2) ≪ f(n) ≪ n^(2/3).
-/

/-- Lower bound: f(n) ≥ c · n^(1/2) for some c > 0. -/
axiom erdos_lower_bound : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (f n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)

/-- Upper bound: f(n) ≤ C · n^(2/3) for some C. -/
axiom erdos_upper_bound : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (f n : ℝ) ≤ C * (n : ℝ) ^ (2/3 : ℝ)

/-- Erdős's bounds combined. -/
theorem erdos_bounds : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * (n : ℝ) ^ (1/2 : ℝ) ≤ f n ∧ (f n : ℝ) ≤ C * (n : ℝ) ^ (2/3 : ℝ) := by
  obtain ⟨c, hc, N₁, hN₁⟩ := erdos_lower_bound
  obtain ⟨C, hC, N₂, hN₂⟩ := erdos_upper_bound
  use c, C, hc, hC, max N₁ N₂
  intro n hn
  constructor
  · exact hN₁ n (le_of_max_le_left hn)
  · exact hN₂ n (le_of_max_le_right hn)

/-
## Phelps-Rödl Theorem (1986)

The exact asymptotic: f(n) ≍ (n log n)^(1/2).
-/

/-- The asymptotic function (n log n)^(1/2). -/
noncomputable def asymptoticBound (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.log n) ^ (1/2 : ℝ)

/-- Phelps-Rödl lower bound: f(n) ≥ c · (n log n)^(1/2). -/
axiom phelps_rodl_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (f n : ℝ) ≥ c * asymptoticBound n

/-- Phelps-Rödl upper bound: f(n) ≤ C · (n log n)^(1/2). -/
axiom phelps_rodl_upper : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (f n : ℝ) ≤ C * asymptoticBound n

/-- Phelps-Rödl (1986): f(n) ≍ (n log n)^(1/2). -/
theorem phelps_rodl : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * asymptoticBound n ≤ f n ∧ (f n : ℝ) ≤ C * asymptoticBound n := by
  obtain ⟨c, hc, N₁, hN₁⟩ := phelps_rodl_lower
  obtain ⟨C, hC, N₂, hN₂⟩ := phelps_rodl_upper
  use c, C, hc, hC, max N₁ N₂
  intro n hn
  constructor
  · exact hN₁ n (le_of_max_le_left hn)
  · exact hN₂ n (le_of_max_le_right hn)

/-
## The Main Question Answered

The answer is f(n) ≍ (n log n)^(1/2).
-/

/-- The main question: estimate f(n). -/
def erdos_1024_question : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ g : ℕ → ℝ, ∃ N : ℕ, ∀ n ≥ N,
    c * g n ≤ f n ∧ (f n : ℝ) ≤ C * g n

/-- The answer: f(n) ≍ (n log n)^(1/2). -/
theorem erdos_1024_solved : erdos_1024_question := by
  obtain ⟨c, C, hc, hC, N, hN⟩ := phelps_rodl
  use c, C, hc, hC, asymptoticBound, N
  exact hN

/-
## Steiner Triple Systems

A Steiner triple system is a 3-uniform linear hypergraph covering all pairs.
-/

/-- A Steiner triple system covers every pair exactly once. -/
def isSteinerTripleSystem (H : Hypergraph V) : Prop :=
  is3UniformLinear H ∧
  ∀ u v : V, u ≠ v → ∃! e ∈ H, u ∈ e ∧ v ∈ e

/-- Steiner triple systems exist for n ≡ 1, 3 (mod 6). -/
axiom steiner_existence (n : ℕ) :
  (n % 6 = 1 ∨ n % 6 = 3) →
  ∃ H : Hypergraph (Fin n), isSteinerTripleSystem H

/-- STS are the densest 3-uniform linear hypergraphs. -/
theorem sts_densest (n : ℕ) (H : Hypergraph (Fin n)) (hH : isSteinerTripleSystem H) :
    H.card = n * (n - 1) / 6 := by
  sorry

/-
## Probabilistic Lower Bound

Random independent sets give the lower bound.
-/

/-- Expected independent set size from random selection. -/
noncomputable def expectedIndependent (H : Hypergraph V) (p : ℝ) : ℝ :=
  p * Fintype.card V - (H.card : ℝ) * p^3

/-- Optimizing p gives the lower bound. -/
theorem probabilistic_lower (H : Hypergraph V) (hH : is3UniformLinear H)
    (hn : Fintype.card V = n) (hm : H.card = m) :
    independenceNumber H ≥ Nat.floor ((n : ℝ)^(2/3) / (3 * m^(1/3) + 1)) := by
  sorry

/-
## Upper Bound Construction

Constructions matching the lower bound.
-/

/-- There exist 3-uniform linear hypergraphs with small independence number. -/
axiom construction_upper (n : ℕ) (hn : n ≥ 10) :
  ∃ H : Hypergraph (Fin n), is3UniformLinear H ∧
    independenceNumber H ≤ 2 * Nat.ceil (asymptoticBound n)

/-
## Comparison of Bounds

The Phelps-Rödl bound is between Erdős's bounds.
-/

/-- (n log n)^(1/2) is between n^(1/2) and n^(2/3). -/
theorem bound_comparison (n : ℕ) (hn : n ≥ 3) :
    (n : ℝ)^(1/2 : ℝ) ≤ asymptoticBound n ∧
    asymptoticBound n ≤ (n : ℝ)^(2/3 : ℝ) := by
  sorry

/-- The log factor refines Erdős's gap. -/
theorem log_factor_refinement :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      asymptoticBound n ≤ (n : ℝ)^(1/2 + ε) ∧
      (n : ℝ)^(1/2 : ℝ) ≤ asymptoticBound n := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1024 on independent sets in linear hypergraphs.

**Status**: SOLVED (Phelps-Rödl 1986)

**The Question**: Estimate f(n), the minimum independence number of 3-uniform
linear hypergraphs on n vertices.

**The Answer**: f(n) ≍ (n log n)^(1/2).

**Key Results**:
- Erdős: n^(1/2) ≪ f(n) ≪ n^(2/3)
- Phelps-Rödl (1986): f(n) ≍ (n log n)^(1/2)
- The log factor closes Erdős's gap

**Related Topics**:
- Steiner triple systems (partial)
- Hypergraph independence number
- Probabilistic method
-/

end Erdos1024
