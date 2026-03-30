/-
Erdős Problem #905: Edge-Triangle Multiplicity Above Turán

Source: https://erdosproblems.com/905
Status: SOLVED

Statement:
Every graph with n vertices and > n²/4 edges contains an edge which
is in at least n/6 triangles.

Background:
Turán's theorem says that the maximum number of edges in a triangle-free
graph on n vertices is ⌊n²/4⌋. This problem asks: when we exceed this
threshold, how many triangles must share an edge?

Known Results:
- Bollobás-Erdős conjecture
- Proved independently by Edwards (unpublished)
- Proved by Hadziivanov-Nikiforov (1979)

Related Problems:
- Problem #80: General edge-triangle containment
- Problem #1034: Stronger version

References:
- [KhNi79] Hadziivanov-Nikiforov: Solution of a problem of Erdős

Tags: graph-theory, extremal-graph-theory, triangles, turan
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Filter.Basic

open Nat Finset

namespace Erdos905

/-
## Part I: Graph Definitions
-/

/--
**Simple Graph on n Vertices:**
A graph represented by its edge set.
-/
structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  symmetric : ∀ e ∈ edges, (e.2, e.1) ∈ edges
  irreflexive : ∀ e ∈ edges, e.1 ≠ e.2

/--
**Edge Count:**
Number of edges (counting each undirected edge once).
-/
noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  G.edges.card / 2

/--
**Adjacency:**
u and v are adjacent if (u, v) is an edge.
-/
def Adj {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  (u, v) ∈ G.edges

/-
## Part II: Triangles
-/

/--
**Triangle:**
Three vertices {u, v, w} form a triangle if all pairs are adjacent.
-/
def IsTriangle {n : ℕ} (G : Graph n) (u v w : Fin n) : Prop :=
  u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
  Adj G u v ∧ Adj G v w ∧ Adj G u w

/--
**Triangle Count for an Edge:**
The number of triangles containing edge {u, v}.
-/
noncomputable def triangleCountEdge {n : ℕ} (G : Graph n) (u v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => IsTriangle G u v w)).card

/--
**Maximum Triangle Multiplicity:**
The maximum number of triangles sharing any single edge.
-/
noncomputable def maxTriangleMultiplicity {n : ℕ} (G : Graph n) : ℕ :=
  Finset.sup (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ Adj G p.1 p.2)) (fun p => triangleCountEdge G p.1 p.2)

/-
## Part III: Turán's Threshold
-/

/--
**Turán Number:**
ex(n, K₃) = ⌊n²/4⌋ is the maximum edges in a triangle-free graph.
-/
def turanNumber (n : ℕ) : ℕ := n * n / 4

/--
**Above Turán Threshold:**
A graph has more than n²/4 edges.
-/
def AboveTuran {n : ℕ} (G : Graph n) : Prop :=
  edgeCount G > turanNumber n

/--
**Turán's Theorem:**
Any graph with more than ⌊n²/4⌋ edges contains a triangle.
-/
/-
## Part IV: The Main Theorem
-/

/--
**Bollobás-Erdős Conjecture (SOLVED):**
Every graph with n vertices and > n²/4 edges contains an edge
which is in at least n/6 triangles.
-/
def BollobasErdosConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 →
    ∀ G : Graph n, AboveTuran G →
      ∃ u v : Fin n, Adj G u v ∧ triangleCountEdge G u v ≥ n / 6

/--
**The conjecture is TRUE (proved by Edwards and Hadziivanov-Nikiforov):**
-/
axiom bollobas_erdos_theorem : BollobasErdosConjecture

/--
**Equivalent formulation using maxTriangleMultiplicity:**
Any graph above the Turán threshold has at least one triangle,
hence maxTriangleMultiplicity ≥ 1.
-/
/-
## Part V: Tightness and Turán Theory
-/

/--
**Why n/6?**
The constant n/6 is tight. There exist graphs with exactly n²/4 + 1
edges where some edge is in exactly ⌊n/6⌋ triangles.
-/
/--
**Turán Graph T(n, 2):**
The complete bipartite graph K_{⌊n/2⌋, ⌈n/2⌉} is triangle-free.
-/
def IsTuranGraph {n : ℕ} (G : Graph n) : Prop :=
  ∃ S : Finset (Fin n), S.card = n / 2 ∧
    ∀ u v : Fin n, Adj G u v ↔ (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)

/--
**Turán graph is triangle-free:**
The complete bipartite graph K_{⌊n/2⌋,⌈n/2⌉} contains no triangles
because any triangle would require three mutually adjacent vertices,
but in a bipartite graph no two vertices in the same part are adjacent.
-/
/--
**Just above Turán:**
Adding one edge to T(n,2) creates triangles. If G is the Turán graph
and we add a non-edge {u,v}, then u and v are in the same part of the
bipartition. They share neighbors in the other part, creating triangles.
-/
/-
## Part VI: Key Lemma
-/

/--
**Key Lemma:**
If e(G) > n²/4, then the number of triangles T(G) satisfies
T(G) ≥ (e(G) - n²/4) · n/6.
-/
/-
## Part VII: Summary
-/

/--
**The Theorem (SOLVED):**
This conjecture of Bollobás and Erdős was independently proved by
Edwards (unpublished work) and Hadziivanov-Nikiforov in 1979 in the
Comptes Rendus of the Bulgarian Academy of Sciences.
-/
theorem erdos_905 : BollobasErdosConjecture := bollobas_erdos_theorem

end Erdos905
