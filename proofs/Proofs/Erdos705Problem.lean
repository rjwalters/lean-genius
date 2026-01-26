/-
Erdős Problem #705: Unit Distance Graphs with Large Girth

**Problem Statement (OPEN)**

Let G be a finite unit distance graph in ℝ².
Is there some k such that if G has girth ≥ k, then χ(G) ≤ 3?

**Background:**
- The Hadwiger-Nelson problem asks for χ of the full unit distance graph
- The chromatic number of the plane is between 5 (de Grey, 2018) and 7
- Without girth constraints: χ = 4 easy (Moser spindle, 7 vertices, girth 3)
- With girth ≥ 4: χ = 4 (O'Donnell, 56 vertices; Chilakamarri, 47 vertices)
- With girth ≥ 5: χ = 4 (Wormald, 6448 vertices)
- With girth ≥ 6: No 4-chromatic example known!

**Status**: OPEN

Reference: https://erdosproblems.com/705
Source: Erdős (1981), p. 27

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Nat

namespace Erdos705

/-!
# Part 1: Unit Distance Graphs

A unit distance graph in ℝ² has vertices as points in the plane
and edges between points at Euclidean distance exactly 1.
-/

/--
**Unit Distance Adjacency**

Two points p, q ∈ ℝ² are adjacent in the unit distance graph
if and only if ||p - q|| = 1 (Euclidean distance).

Unit distance graphs are central to combinatorial geometry and
connect graph coloring to metric space structure.
-/
def unitDistAdj (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  p ≠ q ∧ dist p q = 1

/--
**Unit Distance Graph on a Point Set**

Given V ⊆ ℝ², the unit distance graph UDG(V) has vertex set V
and edges between all pairs at distance 1.
-/
def unitDistGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj := fun p q => unitDistAdj p.val q.val
  symm := by
    intro p q ⟨hne, hd⟩
    exact ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := by
    intro p ⟨hne, _⟩
    exact hne rfl

/-!
# Part 2: Chromatic Number and Girth

The two key graph parameters in this problem.
-/

/--
**Chromatic Number χ(G)**

The minimum number of colors needed to properly color G
(no two adjacent vertices share a color).
-/
axiom chromaticNumber' {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ

/-- A graph is k-colorable if χ(G) ≤ k. -/
def isKColorable {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  chromaticNumber' G ≤ k

/--
**Girth g(G)**

The length of the shortest cycle in G.
Convention: g(G) = 0 if G is acyclic (forests have infinite girth).
-/
axiom girth' {V : Type*} (G : SimpleGraph V) : ℕ

/-- A graph has girth at least k. -/
def hasGirthAtLeast {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  girth' G ≥ k ∨ girth' G = 0

/-!
# Part 3: Known 4-Chromatic Constructions

Concrete unit distance graphs with χ = 4 at various girths.
-/

/--
**Moser Spindle (1961)**

7 vertices, 11 edges, girth 3, χ = 4.
The smallest known 4-chromatic unit distance graph.
-/
axiom moser_spindle_exists :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card = 7 ∧ chromaticNumber' (unitDistGraph ↑V) = 4

/--
**O'Donnell's Graph (1994)**

56 vertices, girth 4, χ = 4.
Triangle-free but still 4-chromatic!
-/
axiom odonnell_graph_exists :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card = 56 ∧ girth' (unitDistGraph ↑V) ≥ 4 ∧
    chromaticNumber' (unitDistGraph ↑V) = 4

/--
**Wormald's Graph (1979)**

6448 vertices, girth 5, χ = 4.
No triangles, no 4-cycles — yet still 4-chromatic!
-/
axiom wormald_graph_exists :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card = 6448 ∧ girth' (unitDistGraph ↑V) ≥ 5 ∧
    chromaticNumber' (unitDistGraph ↑V) = 4

/--
**Chilakamarri (1995)**

47 vertices, girth 4, χ = 4.
Smallest known triangle-free 4-chromatic unit distance graph.
-/
axiom chilakamarri_family :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card = 47 ∧ girth' (unitDistGraph ↑V) ≥ 4 ∧
    chromaticNumber' (unitDistGraph ↑V) = 4

/-!
# Part 4: The Erdős Conjecture

The formal problem statement.
-/

/--
**Erdős Problem #705 (OPEN)**

∃ k such that every finite UDG with girth ≥ k has χ ≤ 3.

Since Wormald showed girth ≥ 5 does not suffice, we need k ≥ 6.
-/
def erdos_705_conjecture : Prop :=
  ∃ k : ℕ, ∀ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    hasGirthAtLeast (unitDistGraph ↑V) k →
    chromaticNumber' (unitDistGraph ↑V) ≤ 3

/-- The negation: 4-chromatic UDGs exist at every girth. -/
def erdos_705_negation : Prop :=
  ∀ k : ℕ, ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    hasGirthAtLeast (unitDistGraph ↑V) k ∧
    chromaticNumber' (unitDistGraph ↑V) ≥ 4

/-!
# Part 5: Deriving Consequences

What the known constructions tell us.
-/

/-- χ = 4 is achievable at girth 3 (Moser spindle). -/
theorem girth_3_chi_4 :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    chromaticNumber' (unitDistGraph ↑V) = 4 := by
  obtain ⟨V, _, hchi⟩ := moser_spindle_exists
  exact ⟨V, hchi⟩

/-- χ = 4 is achievable at girth ≥ 4 (O'Donnell). -/
theorem girth_4_chi_4 :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    girth' (unitDistGraph ↑V) ≥ 4 ∧ chromaticNumber' (unitDistGraph ↑V) = 4 := by
  obtain ⟨V, _, hg, hchi⟩ := odonnell_graph_exists
  exact ⟨V, hg, hchi⟩

/-- χ = 4 is achievable at girth ≥ 5 (Wormald). -/
theorem girth_5_chi_4 :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    girth' (unitDistGraph ↑V) ≥ 5 ∧ chromaticNumber' (unitDistGraph ↑V) = 4 := by
  obtain ⟨V, _, hg, hchi⟩ := wormald_graph_exists
  exact ⟨V, hg, hchi⟩

/-!
# Part 6: The Hadwiger-Nelson Connection

The broader context of coloring the plane.
-/

/--
**Hadwiger-Nelson Problem**

χ(ℝ²) = chromatic number of the plane = ?

Known: 5 ≤ χ(ℝ²) ≤ 7
- Lower: de Grey (2018), 1581-vertex 5-chromatic UDG
- Upper: hexagonal tiling with diameter < 1

Problem #705 concerns finite subgraphs with girth restrictions.
-/
axiom de_grey_lower_bound :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    chromaticNumber' (unitDistGraph ↑V) ≥ 5

/-!
# Part 7: Abstract vs. Geometric Graphs

Why geometry constrains chromatic number.
-/

/--
**Erdős (1959): High girth + high χ exist abstractly.**

For any g, k there exists an abstract graph with girth ≥ g and χ ≥ k.
Proved by the probabilistic method — a landmark result.

But for UNIT DISTANCE graphs, the Euclidean structure of ℝ²
may prevent this. Problem #705 asks exactly whether it does
(at least for χ ≥ 4).
-/
axiom erdos_1959_girth_chromatic :
    ∀ g k : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    girth' G ≥ g ∧ chromaticNumber' G ≥ k

/-!
# Part 8: Vertex Count Growth

How the size of constructions grows with girth.
-/

/--
**Known vertex counts:**
- Girth ≥ 3: 7 vertices (Moser spindle)
- Girth ≥ 4: 47 vertices (Chilakamarri)
- Girth ≥ 5: 6448 vertices (Wormald)
- Girth ≥ 6: ??? (no known 4-chromatic example)

The exponential growth (7 → 47 → 6448) suggests constructing
higher-girth examples may be impossible, supporting the conjecture.
-/
def vertexCountGrowth : List (ℕ × ℕ) :=
  [(3, 7), (4, 47), (5, 6448)]

/-!
# Part 9: Related Problems

Connections to other Erdős problems.
-/

/--
**Related Erdős Problems:**
- #508: Chromatic number of unit distance graphs
- #704: Specific questions about UDG structure
- #706: Further chromatic number questions for geometric graphs

These form a constellation of problems about how geometry
constrains graph coloring.
-/

/-!
# Part 10: Problem Status
-/

/-- The problem is OPEN. -/
def erdos_705_status : String := "OPEN"

/-- Main statement: known results from constructions. -/
theorem erdos_705_main :
    (∃ V : Finset (EuclideanSpace ℝ (Fin 2)),
      chromaticNumber' (unitDistGraph ↑V) = 4) ∧
    (∃ V : Finset (EuclideanSpace ℝ (Fin 2)),
      girth' (unitDistGraph ↑V) ≥ 4 ∧ chromaticNumber' (unitDistGraph ↑V) = 4) ∧
    (∃ V : Finset (EuclideanSpace ℝ (Fin 2)),
      girth' (unitDistGraph ↑V) ≥ 5 ∧ chromaticNumber' (unitDistGraph ↑V) = 4) := by
  exact ⟨girth_3_chi_4, girth_4_chi_4, girth_5_chi_4⟩

/-!
# Summary

**Problem:** Is there k such that girth(UDG) ≥ k implies χ(UDG) ≤ 3?

**Status:** OPEN

**Known 4-chromatic UDGs:**
- Girth ≥ 3: Moser spindle (7 vertices)
- Girth ≥ 4: Chilakamarri (47), O'Donnell (56)
- Girth ≥ 5: Wormald (6448)
- Girth ≥ 6: None known — the frontier!

**Context:** Abstract graphs can have high girth AND high χ (Erdős 1959),
but unit distance graphs are constrained by Euclidean geometry.

**Source:** Erdős (1981), p. 27
-/

end Erdos705
