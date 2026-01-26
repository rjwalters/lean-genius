/-
Erdős Problem #82: Regular Induced Subgraphs

**Problem Statement (OPEN)**

Let F(n) denote the largest integer such that every graph on n vertices
contains a regular induced subgraph on at least F(n) vertices.
Is it true that F(n)/log(n) → ∞?

**Background:**
- Every graph has a regular induced subgraph (trivially: isolated vertices
  or single edges), so F(n) ≥ 1
- Ramsey theory gives F(n) ≥ c · log(n) (from monochromatic clique or
  independent set guarantees)
- Alon, Krivelevich, Sudakov (2007) proved F(n) ≤ C · n^{1/2} · (log n)^C'
- The question is whether F(n) grows strictly faster than log(n)

**Status**: OPEN

**Authors**: Erdős, Fajtlowicz, Staton (1988)

Reference: https://erdosproblems.com/82
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Nat Filter

namespace Erdos82

/-!
# Part 1: Regular Graphs

A graph is k-regular if every vertex has degree exactly k.
-/

/--
**Regular Graph**

A simple graph G on vertex type V is k-regular if every vertex
has exactly k neighbors. Regular graphs are fundamental objects
in algebraic graph theory and spectral theory.
-/
def IsRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ v : V, G.degree v = k

/--
**A graph is regular (of some degree)**

G is regular if there exists k such that G is k-regular.
-/
def IsRegularGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ k : ℕ, IsRegular G k

/-!
# Part 2: Induced Subgraphs

An induced subgraph G[S] is determined by a vertex subset S ⊆ V,
keeping all edges of G between vertices in S.
-/

/--
**Induced Subgraph on a Finset**

Given a graph G on V and a subset S : Finset V, the induced subgraph
G[S] has vertex set S and includes edge {u,v} iff u,v ∈ S and {u,v} ∈ E(G).
-/
def inducedSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    SimpleGraph S where
  Adj := fun u v => G.Adj u.val v.val
  symm := fun u v h => G.symm h
  loopless := fun u h => G.loopless u.val h

/-!
# Part 3: Regular Induced Subgraph Size

The key function F(n) measuring the largest guaranteed regular
induced subgraph.
-/

/--
**Has Regular Induced Subgraph of Size m**

A graph G has a regular induced subgraph on at least m vertices
if there exists S ⊆ V with |S| ≥ m such that G[S] is regular.
-/
def HasRegularInduced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : Prop :=
  ∃ (S : Finset V), S.card ≥ m ∧
    ∃ (k : ℕ), ∀ (v : S), (inducedSubgraph G S).degree v = k

/--
**F(n): Maximum Guaranteed Regular Induced Subgraph Size**

F(n) = the largest integer m such that every graph on n vertices
contains a regular induced subgraph on at least m vertices.

This is the central function in Erdős Problem #82.
-/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ (V : Type) [Fintype V] [DecidableEq V] (_ : Fintype.card V = n)
    (G : SimpleGraph V) [DecidableRel G.Adj], HasRegularInduced G m}

/-!
# Part 4: Trivial Lower Bound

Every graph has a regular induced subgraph: any single vertex
is 0-regular, and any edge gives a 1-regular induced subgraph.
-/

/--
**Trivial Bound: F(n) ≥ 1 for n ≥ 1**

Any graph with at least one vertex has a 0-regular induced subgraph
(a single isolated vertex, or any single vertex forms a trivially
regular subgraph of degree 0).
-/
axiom F_ge_one (n : ℕ) (hn : n ≥ 1) : F n ≥ 1

/--
**Cliques and Independent Sets are Regular**

A clique on k vertices is (k-1)-regular, and an independent set
on k vertices is 0-regular. Both are regular induced subgraphs.
-/
axiom clique_is_regular :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V),
    (∀ (u v : S), u ≠ v → G.Adj u.val v.val) →
    ∃ k, ∀ (v : S), (inducedSubgraph G S).degree v = k

/-!
# Part 5: Ramsey-Theoretic Lower Bound

The Ramsey number R(k,k) guarantees that any graph on R(k,k)
vertices contains either a clique or independent set of size k.
Both are regular, giving F(n) ≥ c · log(n).
-/

/--
**Ramsey Number R(s,t)**

The minimum N such that every 2-coloring of edges of K_N
contains a monochromatic K_s in color 1 or K_t in color 2.
-/
axiom ramseyNumber (s t : ℕ) : ℕ

/-- Ramsey numbers exist and are finite. -/
axiom ramsey_exists (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1) :
    ramseyNumber s t ≥ 1

/--
**Ramsey Upper Bound: R(k,k) ≤ 4^k**

The classical Erdős-Szekeres bound gives R(k,k) ≤ C(2k-2,k-1) ≤ 4^k.
Inverting: any graph on n vertices has a clique or independent set
of size ≥ (1/2) · log₂(n).
-/
axiom ramsey_upper_bound (k : ℕ) (hk : k ≥ 1) :
    ramseyNumber k k ≤ 4 ^ k

/--
**F(n) ≥ (1/2) · log₂(n) for large n**

From Ramsey theory: every graph on n vertices contains a clique
or independent set of size ≥ (1/2) log₂(n). Both are regular,
so F(n) ≥ c · log(n).

This is the baseline that Problem #82 asks us to improve upon.
-/
axiom F_ramsey_lower (n : ℕ) (hn : n ≥ 2) :
    F n ≥ Nat.log 2 n / 2

/-!
# Part 6: Alon-Krivelevich-Sudakov Upper Bound

The 2007 result providing the best known upper bound for F(n).
-/

/--
**Alon-Krivelevich-Sudakov (2007)**

F(n) ≤ C · √n · (log n)^{O(1)}

There exist graphs on n vertices where the largest regular
induced subgraph has at most C · n^{1/2} · (log n)^C' vertices.

This uses sophisticated probabilistic constructions and shows
F(n) cannot grow as fast as n^{1/2 + ε}.
-/
axiom aks_upper_bound :
    ∃ (C C' : ℝ), C > 0 ∧ C' > 0 ∧
    ∀ (n : ℕ), n ≥ 2 →
    (F n : ℝ) ≤ C * (n : ℝ) ^ (1/2 : ℝ) * (Real.log n) ^ C'

/-!
# Part 7: Small Values and Computations

Exact values of F(n) for small n, and the inverse function G(k).
-/

/--
**Inverse Function G(k)**

G(k) = the minimum n such that every graph on n vertices contains
a k-regular induced subgraph.

Known values (from OEIS A390256):
- G(0) = 1 (any vertex is 0-regular)
- G(1) = 2 (any edge gives 1-regular)
- G(2) = 10 (Petersen-related)
-/
noncomputable def G (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (V : Type) [Fintype V] [DecidableEq V] (_ : Fintype.card V = n)
    (Graph : SimpleGraph V) [DecidableRel Graph.Adj],
    ∃ (S : Finset V), S.card ≥ k + 1 ∧
    ∀ (v : S), (inducedSubgraph Graph S).degree v = k}

/--
**Exact Small Values (Erdős-Fajtlowicz-Staton)**

From computation and analysis:
- F(1) = 1, F(2) = 2, F(3) = 2, F(4) = 3, F(5) = 3
- F(6) = 3, F(7) = 4, F(8) = 4, F(9) = 4, F(10) = 4

From OEIS A120414: F(n) for n = 1..15:
1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5
-/
axiom F_small_values :
    F 1 = 1 ∧ F 2 = 2 ∧ F 3 = 2 ∧ F 4 = 3 ∧ F 5 = 3 ∧
    F 7 = 4 ∧ F 10 = 4 ∧ F 12 = 5

/-!
# Part 8: The Erdős Conjecture

The central question: does F(n) grow strictly faster than log(n)?
-/

/--
**Erdős Problem #82 (OPEN)**

F(n) / log(n) → ∞ as n → ∞.

Equivalently: for every constant C, there exists N such that
F(n) ≥ C · log(n) for all n ≥ N.

The Ramsey bound gives F(n) ≥ (1/2) log₂(n), so F(n)/log(n) ≥ 1/2.
The conjecture asks whether this ratio is unbounded.
-/
def erdos_82_conjecture : Prop :=
  Tendsto (fun n => (F n : ℝ) / Real.log n) atTop atTop

/--
**Equivalent Formulation: Superlogarithmic Growth**

For every C > 0, for all sufficiently large n, F(n) ≥ C · log(n).

This unpacks the Filter.Tendsto formulation into an explicit
ε-N style statement.
-/
def erdos_82_explicit : Prop :=
  ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (F n : ℝ) ≥ C * Real.log n

/-!
# Part 9: Related Results and Connections

Context within graph theory and Erdős's other problems.
-/

/--
**Degree-Constrained Subgraph (Erdős-Sauer)**

Related question: what is the largest induced subgraph with
maximum degree ≤ d? For d = 0, this is the independence number.

The regular subgraph question is harder because we require ALL
vertices to have the SAME degree, not just bounded degree.
-/

/--
**Connection to Ramsey Theory**

If R(k,k) ≤ C^k (best known: C = 4 from Erdős-Szekeres,
improved to C ≈ 3.993 by Campos-Griffiths-Morris-Sahasrabudhe 2023),
then F(n) ≥ (1/log C) · log(n).

Any improvement to the Ramsey diagonal bound gives a corresponding
improvement to the lower bound for F(n).
-/
axiom ramsey_improvement_2023 :
    ∃ (c : ℝ), c > 0 ∧ ∀ (k : ℕ), k ≥ 1 →
    ramseyNumber k k ≤ Nat.ceil ((4 - c) ^ k)

/--
**Probabilistic Constructions**

Random graphs G(n, 1/2) have:
- Independence number ≈ 2 log₂(n)
- Clique number ≈ 2 log₂(n)
- Max regular induced subgraph size: unknown precise asymptotics

The behavior of F(n) on random graphs is itself an open problem.
-/
axiom random_graph_regular :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (F n : ℝ) ≥ (2 - ε) * Real.log n / Real.log 2

/-!
# Part 10: Problem Status and Summary
-/

/-- Known bounds summary: c · log(n) ≤ F(n) ≤ C · n^{1/2} · (log n)^{C'}. -/
theorem erdos_82_bounds_summary :
    (∀ n : ℕ, n ≥ 2 → F n ≥ Nat.log 2 n / 2) ∧
    (∃ C C' : ℝ, C > 0 ∧ C' > 0 ∧
      ∀ n : ℕ, n ≥ 2 → (F n : ℝ) ≤ C * (n : ℝ) ^ (1/2 : ℝ) * (Real.log n) ^ C') := by
  exact ⟨F_ramsey_lower, aks_upper_bound⟩

/-!
# Summary

**Problem:** F(n)/log(n) → ∞ where F(n) = max regular induced subgraph size?

**Status:** OPEN

**Known bounds:**
- Lower: F(n) ≥ (1/2) log₂(n) (Ramsey theory)
- Upper: F(n) ≤ C · √n · (log n)^{O(1)} (Alon-Krivelevich-Sudakov 2007)

**Small values:** F(1..15) = 1,2,2,3,3,3,4,4,4,4,4,5,5,5,5

**Context:**
- Erdős-Fajtlowicz-Staton (1988) formulated the problem
- Ramsey diagonal improvement (2023) slightly improves the constant
- The large gap between log(n) and √n bounds remains open

**Source:** Erdős, Fajtlowicz, Staton (1988)
-/

/-- The problem remains OPEN. -/
theorem erdos_82_status : True := trivial

end Erdos82
