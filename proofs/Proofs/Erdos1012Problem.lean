/-
Erdős Problem #1012: Long Cycles in Dense Graphs

Let k ≥ 0. Let f(k) be such that every graph on n ≥ f(k) vertices with
at least C(n-k-1, 2) + C(k+2, 2) + 1 edges contains a cycle on n-k vertices.

Determine or estimate f(k).

**Status**: SOLVED (Woodall 1972)
**Answer**: f(k) = 2k+3 works; graphs with enough edges have all cycle lengths 3 to n-k.

Reference: https://erdosproblems.com/1012
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Basic

open SimpleGraph Finset

namespace Erdos1012

/-!
## Graph Basics

We work with simple graphs on a finite vertex set.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges in a simple graph. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The number of vertices in the graph. -/
def vertexCount (G : SimpleGraph V) : ℕ := Fintype.card V

/-!
## The Edge Threshold

The critical edge count is C(n-k-1, 2) + C(k+2, 2) + 1.
This is the threshold above which long cycles must exist.
-/

/-- The Erdős edge threshold for the (n-k)-cycle problem. -/
def edgeThreshold (n k : ℕ) : ℕ :=
  Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1

/-- Alternative form: the threshold equals (n-k-1)(n-k-2)/2 + (k+2)(k+1)/2 + 1. -/
theorem edgeThreshold_expanded (n k : ℕ) (hn : n ≥ k + 1) :
    edgeThreshold n k = (n - k - 1) * (n - k - 2) / 2 + (k + 2) * (k + 1) / 2 + 1 := by
  sorry

/-!
## Cycles in Graphs

A cycle of length l is a closed walk visiting l distinct vertices.
-/

/-- A graph contains a cycle of length l. -/
def hasCycleOfLength (G : SimpleGraph V) (l : ℕ) : Prop :=
  ∃ (cycle : Fin l → V), Function.Injective cycle ∧
    (∀ i : Fin l, G.Adj (cycle i) (cycle ⟨(i.val + 1) % l, Nat.mod_lt _ (by omega)⟩))

/-- A Hamiltonian cycle visits all n vertices. -/
def isHamiltonian (G : SimpleGraph V) : Prop :=
  hasCycleOfLength G (Fintype.card V)

/-!
## The Function f(k)

f(k) is the minimum n₀ such that for all n ≥ n₀, any graph on n vertices
with at least edgeThreshold(n, k) edges contains an (n-k)-cycle.
-/

/-- Property: every graph on n vertices with ≥ threshold edges has (n-k)-cycle. -/
def hasLongCycle (n k : ℕ) : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      edgeCount G ≥ edgeThreshold n k →
      hasCycleOfLength G (n - k)

/-- f(k) = min n₀ such that hasLongCycle holds for all n ≥ n₀. -/
noncomputable def erdosF (k : ℕ) : ℕ :=
  Nat.find (erdos_f_exists k)
where
  erdos_f_exists : ∀ k, ∃ n₀, ∀ n ≥ n₀, hasLongCycle n k := by
    intro k
    use 2 * k + 3  -- Woodall's bound
    intro n hn
    exact woodall_theorem n k hn

/-!
## Ore's Theorem (1961): f(0) = 1

For k = 0, the threshold becomes C(n-1, 2) + C(2, 2) + 1 = C(n-1, 2) + 2.
Any graph with this many edges has a Hamiltonian cycle.
-/

/-- The k=0 threshold: C(n-1, 2) + 2. -/
theorem threshold_k0 (n : ℕ) : edgeThreshold n 0 = Nat.choose (n - 1) 2 + 2 := by
  simp [edgeThreshold]

/-- Ore (1961): f(0) = 1. Every graph on n ≥ 1 vertices with
    ≥ C(n-1, 2) + 2 edges has a Hamiltonian cycle. -/
axiom ore_theorem : ∀ n ≥ 1, hasLongCycle n 0

/-- Ore's result gives f(0) = 1. -/
theorem f_zero : erdosF 0 = 1 := by
  sorry

/-!
## Bondy's Theorem (1971): f(1) = 1

For k = 1, the threshold is C(n-2, 2) + C(3, 2) + 1 = C(n-2, 2) + 4.
Any graph with this many edges has an (n-1)-cycle.
-/

/-- The k=1 threshold: C(n-2, 2) + 4. -/
theorem threshold_k1 (n : ℕ) (hn : n ≥ 2) :
    edgeThreshold n 1 = Nat.choose (n - 2) 2 + 4 := by
  sorry

/-- Bondy (1971): f(1) = 1. -/
axiom bondy_theorem : ∀ n ≥ 1, hasLongCycle n 1

/-- Bondy's result gives f(1) = 1. -/
theorem f_one : erdosF 1 = 1 := by
  sorry

/-!
## Woodall's Theorem (1972): Complete Solution

Woodall proved the definitive result: for n ≥ 2k+3, any graph with
≥ edgeThreshold(n, k) edges contains cycles of ALL lengths from 3 to n-k.
-/

/-- A graph is pancyclic from 3 to m if it has cycles of all lengths 3, 4, ..., m. -/
def isPancyclicUpTo (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ l, 3 ≤ l → l ≤ m → hasCycleOfLength G l

/-- Woodall (1972): For n ≥ 2k+3 and sufficient edges, the graph has
    cycles of all lengths from 3 to n-k. -/
axiom woodall_theorem (n k : ℕ) (hn : n ≥ 2 * k + 3) :
    hasLongCycle n k

/-- Woodall's stronger result: pancyclic from 3 to n-k. -/
axiom woodall_pancyclic (n k : ℕ) (hn : n ≥ 2 * k + 3) :
    ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V = n →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        edgeCount G ≥ edgeThreshold n k →
        isPancyclicUpTo G (n - k)

/-!
## The Solution

Woodall's theorem shows f(k) ≤ 2k + 3 for all k.
Combined with Ore and Bondy's results, this completely determines f(k).
-/

/-- Upper bound: f(k) ≤ 2k + 3. -/
theorem erdosF_upper_bound (k : ℕ) : erdosF k ≤ 2 * k + 3 := by
  sorry

/-- The problem is solved: f(k) is well-defined and bounded. -/
theorem erdos_1012_solved : ∀ k, erdosF k ≤ 2 * k + 3 := erdosF_upper_bound

/-!
## Extremal Examples

The edge threshold is tight: there exist graphs with one fewer edge
that lack the required cycle.
-/

/-- Extremal construction: graphs achieving the threshold minus 1. -/
def extremalGraph (n k : ℕ) : Prop :=
  ∃ (V : Type*) [Fintype V] [DecidableEq V],
    ∃ (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n ∧
      edgeCount G = edgeThreshold n k - 1 ∧
      ¬hasCycleOfLength G (n - k)

/-- The threshold is tight: extremal graphs exist. -/
axiom threshold_tight (n k : ℕ) (hn : n ≥ 2 * k + 3) : extremalGraph n k

/-!
## Connection to Turán Theory

This problem relates to Turán-type extremal graph theory.
-/

/-- The Turán number ex(n, C_l) is max edges avoiding l-cycle. -/
noncomputable def turanNumber (n l : ℕ) : ℕ :=
  sorry  -- Complex definition involving cycle-free graphs

/-- For long cycles, the threshold relates to Turán numbers. -/
theorem threshold_turán_connection (n k : ℕ) (hn : n ≥ 2 * k + 3) :
    edgeThreshold n k > turanNumber n (n - k) := by
  sorry

/-!
## Summary

This file formalizes Erdős Problem #1012 on long cycles in dense graphs.

**Status**: SOLVED (Woodall 1972)

**The Question**: Let f(k) be min n₀ such that every graph on n ≥ n₀ vertices
with ≥ C(n-k-1, 2) + C(k+2, 2) + 1 edges has an (n-k)-cycle. Determine f(k).

**Key Results**:
- Ore (1961): f(0) = 1 (Hamiltonian cycle theorem)
- Bondy (1971): f(1) = 1
- Woodall (1972): f(k) ≤ 2k+3, and such graphs are pancyclic from 3 to n-k

**The Answer**: For n ≥ 2k+3 vertices, the edge threshold guarantees
not just an (n-k)-cycle but cycles of all intermediate lengths.
-/

end Erdos1012
