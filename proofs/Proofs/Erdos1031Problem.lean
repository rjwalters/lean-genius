/-
Erdős Problem #1031: Induced Regular Subgraphs in Non-Ramsey Graphs

If G is a graph on n vertices with no trivial (empty or complete) subgraph on
≥ 10 log n vertices, must G contain an induced non-trivial regular subgraph
on ≫ log n vertices?

**Status**: SOLVED (YES)
**Answer**: Prömel-Rödl (1999) proved the stronger result that such G contains
all graphs with O(log n) vertices as induced subgraphs.

Reference: https://erdosproblems.com/1031
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace Erdos1031

/-
## Simple Graphs

We work with simple graphs (no loops, undirected).
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The complete graph on a vertex set. -/
def completeGraph (S : Finset V) : SimpleGraph S :=
  ⊤

/-- The empty graph on a vertex set. -/
def emptyGraph (S : Finset V) : SimpleGraph S :=
  ⊥

/-
## Trivial Subgraphs

A trivial subgraph is either empty or complete.
-/

/-- An induced subgraph on S is trivial if it's empty or complete. -/
def isTrivialInduced (G : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬G.Adj x y) ∨
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)

/-- S is an independent set. -/
def isIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬G.Adj x y

/-- S is a clique. -/
def isClique (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y

/-- Trivial = independent or clique. -/
theorem trivial_iff_ind_or_clique (G : SimpleGraph V) (S : Finset V) :
    isTrivialInduced G S ↔ isIndependentSet G S ∨ isClique G S := by
  rfl

/-
## Regular Subgraphs

A graph is regular if all vertices have the same degree.
-/

/-- Degree of a vertex in the induced subgraph on S. -/
def inducedDegree (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun u => G.Adj v u)).card

/-- An induced subgraph is k-regular. -/
def isKRegularInduced (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∀ v ∈ S, inducedDegree G S v = k

/-- An induced subgraph is regular. -/
def isRegularInduced (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ k : ℕ, isKRegularInduced G S k

/-- A non-trivial regular subgraph (not 0-regular on ≥2 vertices, not complete). -/
def isNontrivialRegular (G : SimpleGraph V) (S : Finset V) : Prop :=
  isRegularInduced G S ∧ ¬isTrivialInduced G S

/-
## The Non-Ramsey Property

G has no large trivial subgraph.
-/

/-- G has no trivial subgraph of size ≥ k. -/
def noLargeTrivial (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≥ k → ¬isTrivialInduced G S

/-- The Ramsey bound: every graph has a trivial subgraph of size ≫ log n. -/
axiom ramsey_trivial_bound : ∃ c > 0, ∀ n : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V,
  ∃ S : Finset V, isTrivialInduced G S ∧ (S.card : ℝ) ≥ c * Real.log n

/-
## The Main Conjecture

Graphs with no large trivial subgraph contain induced regular subgraphs.
-/

/-- The original question: existence of non-trivial regular subgraph. -/
def erdos_1031_conjecture : Prop :=
  ∃ c > 0, ∀ n : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V,
  noLargeTrivial G (Nat.ceil (10 * Real.log n)) →
  ∃ S : Finset V, isNontrivialRegular G S ∧ (S.card : ℝ) ≥ c * Real.log n

/-
## Prömel-Rödl Theorem (1999)

Much stronger: such graphs are c log n - universal.
-/

/-- H is an induced subgraph of G on vertex set S. -/
def isInducedSubgraph (G : SimpleGraph V) (S : Finset V) (H : SimpleGraph S) : Prop :=
  ∀ x y : S, H.Adj x y ↔ G.Adj x.val y.val

/-- G contains H as an induced subgraph. -/
def containsInduced (G : SimpleGraph V) (H : SimpleGraph W) [Fintype W] : Prop :=
  ∃ S : Finset V, S.card = Fintype.card W ∧
  ∃ (f : W ≃ S), ∀ x y : W, H.Adj x y ↔ G.Adj (f x).val (f y).val

/-- G is k-universal: contains all graphs on k vertices as induced subgraphs. -/
def isKUniversal (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (W : Type*) [DecidableEq W] [Fintype W],
  Fintype.card W = k →
  ∀ H : SimpleGraph W, containsInduced G H

/-- Prömel-Rödl (1999): Non-Ramsey graphs are c log n - universal. -/
axiom promel_rodl : ∀ c > 0, ∃ c' > 0, ∃ N : ℕ, ∀ n ≥ N,
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V,
  noLargeTrivial G (Nat.ceil (c * Real.log n)) →
  isKUniversal G (Nat.floor (c' * Real.log n))

/-
## The Solution

The conjecture follows from Prömel-Rödl.
-/

/-- Any k ≥ 3 has a non-trivial k-regular graph. -/
axiom exists_nontrivial_regular (k : ℕ) (hk : k ≥ 3) :
  ∃ (W : Type*) [DecidableEq W] [Fintype W],
  ∃ H : SimpleGraph W, Fintype.card W ≤ 2 * k ∧
    (∀ v : W, H.degree v = k) ∧
    ¬(∀ x y : W, x ≠ y → H.Adj x y) ∧
    ¬(∀ x y : W, x ≠ y → ¬H.Adj x y)

/-- The conjecture is true. -/
theorem erdos_1031_solved : erdos_1031_conjecture := by
  sorry

/-- Simplified statement using Prömel-Rödl. -/
theorem erdos_1031_via_promel_rodl :
    ∀ c > 0, ∃ c' > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V,
    noLargeTrivial G (Nat.ceil (c * Real.log n)) →
    ∃ S : Finset V, isNontrivialRegular G S ∧ (S.card : ℝ) ≥ c' * Real.log n := by
  sorry

/-
## Connection to Ramsey Theory

Ramsey's theorem guarantees trivial subgraphs.
-/

/-- Ramsey number R(k,k). -/
noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  Nat.find (ramsey_exists k)
  where
  ramsey_exists (k : ℕ) : ∃ N : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V ≥ N →
    ∀ G : SimpleGraph V,
    ∃ S : Finset V, S.card = k ∧ isTrivialInduced G S := by
    sorry

/-- R(k,k) ≤ 4^k (crude bound). -/
axiom ramsey_upper_bound (k : ℕ) : ramseyNumber k ≤ 4^k

/-- R(k,k) ≥ 2^(k/2) (probabilistic lower bound). -/
axiom ramsey_lower_bound (k : ℕ) : ramseyNumber k ≥ 2^(k/2)

/-- Ramsey implies log n trivial subgraph. -/
theorem ramsey_log_trivial (n : ℕ) (hn : n ≥ 4) :
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V,
    ∃ S : Finset V, isTrivialInduced G S ∧ S.card ≥ Nat.log 4 n / 2 := by
  sorry

/-
## Non-Ramsey Graphs

Graphs avoiding large trivial subgraphs are "non-Ramsey".
-/

/-- A non-Ramsey graph has no trivial subgraph of size ≥ c log n. -/
def isNonRamsey (G : SimpleGraph V) (c : ℝ) : Prop :=
  noLargeTrivial G (Nat.ceil (c * Real.log (Fintype.card V)))

/-- Non-Ramsey graphs are rare but exist. -/
axiom nonRamsey_exist (c : ℝ) (hc : c > 0) :
  ∃ N : ℕ, ∀ n ≥ N,
  ∃ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n ∧
  ∃ G : SimpleGraph V, isNonRamsey G c

/-
## Universality

Non-Ramsey graphs contain all small graphs.
-/

/-- The stronger conclusion: all graphs appear as induced subgraphs. -/
theorem nonRamsey_universal (c : ℝ) (hc : c > 0) :
    ∃ c' > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V,
    isNonRamsey G c →
    isKUniversal G (Nat.floor (c' * Real.log n)) := by
  intro c hc
  obtain ⟨c', hc', N, hN⟩ := promel_rodl c hc
  use c', hc', N
  intro n hn V _ _ hV G hG
  exact hN n hn V hV G hG

/-
## Regular Subgraphs from Universality

Universality implies regular subgraphs exist.
-/

/-- Universal graphs contain regular subgraphs. -/
theorem universal_has_regular (G : SimpleGraph V) (k : ℕ) (hk : k ≥ 6) :
    isKUniversal G k →
    ∃ S : Finset V, isNontrivialRegular G S ∧ S.card ≥ 3 := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1031 on induced regular subgraphs.

**Status**: SOLVED

**The Question**: If G has no trivial subgraph on ≥ 10 log n vertices,
must G have an induced non-trivial regular subgraph on ≫ log n vertices?

**The Answer**: YES (Prömel-Rödl 1999).

**Stronger Result**: Such G contains ALL graphs on O(log n) vertices
as induced subgraphs (c log n - universality).

**Key Results**:
- Ramsey: every graph has trivial subgraph on ≫ log n vertices
- Prömel-Rödl: non-Ramsey graphs are c log n - universal
- Universality implies existence of all regular subgraphs

**Related Topics**:
- Ramsey theory
- Graph universality
- Regular graphs
- Problem 82 (general induced regular subgraph bounds)
-/

end Erdos1031
