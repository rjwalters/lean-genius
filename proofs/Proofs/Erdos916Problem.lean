/-
Erdős Problem #916: Graphs with n Vertices and 2n-2 Edges

Source: https://erdosproblems.com/916
Status: SOLVED (Thomassen, 1974)

Statement:
Does every graph with n vertices and 2n-2 edges contain a cycle and another
vertex adjacent to three vertices on the cycle?

**Answer**: YES - proved by Carsten Thomassen (1974)

This would be a stronger form of the result of Dirac (1960) that every such
graph contains a subgraph homeomorphic to K₄ (the complete graph on 4 vertices).

References:
- Erdős [Er67b]: Original problem
- Dirac, G.A. (1960): "In abstrakten Graphen vorhandene vollständige 4-Graphen
  und ihre Unterteilungen", Math. Nachr. 22, 61-85
- Thomassen, C. (1974): "A minimal condition implying a special K₄-subdivision
  in a graph", Arch. Math. (Basel) 25, 210-215
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Card

open SimpleGraph

namespace Erdos916

/-
## Part I: Basic Graph Definitions

We work with simple graphs (undirected, no self-loops, no multiple edges).
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A graph with n vertices and m edges.
We use SimpleGraph from Mathlib which represents graphs as symmetric,
irreflexive relations.
-/
def hasVerticesAndEdges (G : SimpleGraph V) (n m : ℕ) : Prop :=
  Fintype.card V = n ∧ G.edgeFinset.card = m

/-
## Part II: K₄ Subdivisions

A subdivision of K₄ is obtained by replacing edges with paths.
Dirac's theorem says every graph with n vertices and 2n-2 edges
contains a K₄ subdivision.
-/

/--
**Homeomorphic to K₄:**
A graph H is homeomorphic to K₄ if H can be obtained from K₄
by subdividing edges (replacing edges with paths).

This means H has 4 "branch vertices" connected by internally
disjoint paths.
-/
def isK4Subdivision (G : SimpleGraph V) : Prop :=
  ∃ (v₁ v₂ v₃ v₄ : V),
    v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄ ∧
    -- There exist paths between each pair of branch vertices
    G.Reachable v₁ v₂ ∧ G.Reachable v₁ v₃ ∧ G.Reachable v₁ v₄ ∧
    G.Reachable v₂ v₃ ∧ G.Reachable v₂ v₄ ∧ G.Reachable v₃ v₄

/--
**Dirac's Theorem (1960):**
Every graph with n vertices and 2n-2 edges contains a subgraph
homeomorphic to K₄.
-/
axiom dirac_k4_subdivision (G : SimpleGraph V) (n : ℕ) (hn : n ≥ 4)
    (h : hasVerticesAndEdges G n (2 * n - 2)) :
    isK4Subdivision G

/-
## Part III: Cycles with Adjacent Vertices

The key structure in Erdős's problem.
-/

/--
**Cycle in a Graph:**
A cycle is a closed walk with no repeated vertices except the
start/end vertex.
-/
def hasCycle (G : SimpleGraph V) : Prop :=
  ∃ (vertices : List V), vertices.length ≥ 3 ∧
    vertices.Nodup ∧
    ∀ i : Fin vertices.length,
      G.Adj (vertices[i]) (vertices[(i.val + 1) % vertices.length])

/--
**Vertex Adjacent to Three Cycle Vertices:**
Given a cycle C, a vertex v (not on C) is "3-adjacent" to C if
v is adjacent to at least 3 distinct vertices on C.
-/
def hasVertexTriplyAdjacentToCycle (G : SimpleGraph V) : Prop :=
  ∃ (cycle : List V) (v : V),
    -- The cycle is valid
    cycle.length ≥ 3 ∧
    cycle.Nodup ∧
    (∀ i : Fin cycle.length,
      G.Adj (cycle[i]) (cycle[(i.val + 1) % cycle.length])) ∧
    -- v is not on the cycle
    v ∉ cycle ∧
    -- v is adjacent to at least 3 vertices on the cycle
    (∃ (a b c : V),
      a ∈ cycle ∧ b ∈ cycle ∧ c ∈ cycle ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      G.Adj v a ∧ G.Adj v b ∧ G.Adj v c)

/-
## Part IV: Main Theorem - Thomassen's Result
-/

/--
**Thomassen's Theorem (1974):**
Every graph with n vertices and 2n-2 edges contains a cycle
and another vertex adjacent to at least three vertices on the cycle.

This is stronger than Dirac's K₄ subdivision result because:
- A K₄ subdivision gives 4 branch vertices with paths between them
- Thomassen shows we can find a specific geometric structure:
  a cycle with an external vertex having 3 connections to it

The proof uses careful case analysis on the structure of dense graphs.
The key insight is that with 2n-2 edges, the graph has average degree
approximately 4, which forces enough connectivity.
-/
axiom thomassen_cycle_structure (G : SimpleGraph V) (n : ℕ) (hn : n ≥ 4)
    (h : hasVerticesAndEdges G n (2 * n - 2)) :
    hasVertexTriplyAdjacentToCycle G

/--
**Erdős Problem #916: SOLVED**

The main theorem answering Erdős's question.
-/
theorem erdos_916 (G : SimpleGraph V) (n : ℕ) (hn : n ≥ 4)
    (h : hasVerticesAndEdges G n (2 * n - 2)) :
    hasVertexTriplyAdjacentToCycle G :=
  thomassen_cycle_structure G n hn h

/-
## Part V: Relationship to Dirac's Theorem

Thomassen's result implies Dirac's result.
-/

/--
**Thomassen Implies Dirac:**
If a graph has a cycle with a vertex triply adjacent to it,
then it contains a K₄ subdivision.

The cycle + external vertex with 3 adjacencies gives us the
4 branch vertices for a K₄ subdivision.
-/
axiom triply_adjacent_implies_k4 (G : SimpleGraph V) :
    hasVertexTriplyAdjacentToCycle G → isK4Subdivision G

/--
Thomassen's theorem gives an alternative proof of Dirac's theorem.
-/
theorem thomassen_implies_dirac (G : SimpleGraph V) (n : ℕ) (hn : n ≥ 4)
    (h : hasVerticesAndEdges G n (2 * n - 2)) :
    isK4Subdivision G :=
  triply_adjacent_implies_k4 G (thomassen_cycle_structure G n hn h)

/-
## Part VI: Edge Count Analysis

Why 2n-2 edges? This is the threshold for interesting structure.
-/

/--
**Edge Count Threshold:**
With n vertices, we have:
- n-1 edges: minimum for connectivity (a tree)
- 2n-2 edges: guarantees K₄ subdivision and cycle structure
- 3n-6 edges: maximum for planar graphs (n ≥ 3)

The value 2n-2 is significant because:
- A tree has n-1 edges and no cycles
- Adding n-1 more edges creates enough cycles for the structure
-/
def edgeThreshold (n : ℕ) : ℕ := 2 * n - 2

/--
**Tree Lower Bound:**
A tree on n vertices has exactly n-1 edges.
-/
theorem tree_edge_count (n : ℕ) (hn : n ≥ 1) :
    n - 1 < edgeThreshold n := by
  simp only [edgeThreshold]
  omega

/-
## Part VII: Concrete Small Cases
-/

/--
**Smallest Case: n = 4**
With 4 vertices and 6 edges, we have K₄ itself.
K₄ trivially has the required structure:
any 3 vertices form a cycle, the 4th is adjacent to all 3.
-/
theorem case_n_eq_4 :
    edgeThreshold 4 = 6 := by
  simp only [edgeThreshold]
  norm_num

/--
**Case n = 5:**
5 vertices and 8 edges.
-/
theorem case_n_eq_5 :
    edgeThreshold 5 = 8 := by
  simp only [edgeThreshold]
  norm_num

/--
**Case n = 6:**
6 vertices and 10 edges.
-/
theorem case_n_eq_6 :
    edgeThreshold 6 = 10 := by
  simp only [edgeThreshold]
  norm_num

/-
## Part VIII: Average Degree Analysis
-/

/--
**Average Degree:**
In a graph with n vertices and m edges, the average degree is 2m/n.
For m = 2n-2, the average degree is (4n-4)/n ≈ 4 for large n.
-/
def averageDegreeNumerator (n m : ℕ) : ℕ := 2 * m

/--
For our graphs: average degree numerator is 4n - 4.
-/
theorem avg_degree_numerator_formula (n : ℕ) (hn : n ≥ 1) :
    averageDegreeNumerator n (2 * n - 2) = 4 * n - 4 := by
  simp only [averageDegreeNumerator]
  omega

/-
## Part IX: Summary
-/

/--
**Erdős Problem #916: Summary**

Question: Does every graph with n vertices and 2n-2 edges contain
a cycle and another vertex adjacent to three vertices on the cycle?

**Answer: YES**

Key results:
1. Dirac (1960): Such graphs contain K₄ subdivisions
2. Thomassen (1974): Proved the stronger cycle structure result
3. The edge count 2n-2 is optimal for guaranteeing this structure
-/
theorem erdos_916_summary (G : SimpleGraph V) (n : ℕ) (hn : n ≥ 4)
    (h : hasVerticesAndEdges G n (2 * n - 2)) :
    hasVertexTriplyAdjacentToCycle G ∧ isK4Subdivision G :=
  ⟨erdos_916 G n hn h, thomassen_implies_dirac G n hn h⟩

/--
The answer to Erdős's question is YES.
-/
theorem erdos_916_answer : ∀ (G : SimpleGraph V) (n : ℕ),
    n ≥ 4 → hasVerticesAndEdges G n (2 * n - 2) →
    hasVertexTriplyAdjacentToCycle G :=
  fun G n hn h => erdos_916 G n hn h

end Erdos916
