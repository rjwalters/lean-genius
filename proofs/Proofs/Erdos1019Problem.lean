/-
Erdős Problem #1019: Saturated Planar Subgraphs in Dense Graphs

Does every graph on n vertices with ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges contain
a saturated planar graph with more than 3 vertices?

**Status**: SOLVED (Simonovits, PhD thesis)
**Answer**: YES - such graphs must contain either K₄ or C_l + 2K₁ for some l ≥ 3.

Reference: https://erdosproblems.com/1019
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

open SimpleGraph

namespace Erdos1019

/-
## Graph Basics

We work with simple graphs on finite vertex sets.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges in a simple graph. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The number of vertices. -/
def vertexCount : ℕ := Fintype.card V

/-
## Planar Graphs

A graph is planar if it can be embedded in the plane without crossings.
-/

/-- A graph is planar (abstract characterization). -/
def isPlanar (G : SimpleGraph V) : Prop :=
  sorry  -- Complex topological definition

/-- Euler's formula bound: planar graphs have ≤ 3n - 6 edges. -/
axiom planar_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
  isPlanar G → Fintype.card V ≥ 3 → edgeCount G ≤ 3 * Fintype.card V - 6

/-
## Saturated Planar Graphs

A saturated planar graph is a maximal planar graph (has exactly 3n - 6 edges).
-/

/-- A graph is saturated planar: planar with exactly 3n - 6 edges. -/
def isSaturatedPlanar (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  isPlanar G ∧ Fintype.card V ≥ 3 ∧ edgeCount G = 3 * Fintype.card V - 6

/-- Any saturated planar graph is planar. -/
theorem saturated_is_planar (G : SimpleGraph V) [DecidableRel G.Adj] :
    isSaturatedPlanar G → isPlanar G := by
  intro h
  exact h.1

/-- Saturated planar graphs achieve the edge bound. -/
theorem saturated_achieves_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    isSaturatedPlanar G → edgeCount G = 3 * Fintype.card V - 6 := by
  intro h
  exact h.2.2

/-
## Edge Density Threshold

The critical edge count is ⌊n²/4⌋ + ⌊(n+1)/2⌋.
-/

/-- The Turán number for triangles: ⌊n²/4⌋. -/
def turanEdges (n : ℕ) : ℕ := n^2 / 4

/-- The additional threshold: ⌊(n+1)/2⌋. -/
def additionalThreshold (n : ℕ) : ℕ := (n + 1) / 2

/-- The combined threshold for saturated planar subgraphs. -/
def saturatedPlanarThreshold (n : ℕ) : ℕ := turanEdges n + additionalThreshold n

/-- A graph exceeds the threshold for containing saturated planar subgraphs. -/
def exceedsThreshold (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G ≥ saturatedPlanarThreshold (Fintype.card V)

/-
## Triangles and Turán's Theorem

A triangle is a saturated planar graph on 3 vertices.
-/

/-- The complete graph K_n. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/-- A triangle K₃. -/
abbrev K3 : SimpleGraph (Fin 3) := completeGraph 3

/-- K₃ is a saturated planar graph. -/
axiom K3_saturated_planar : isSaturatedPlanar K3

/-- Turán's theorem: graphs with > n²/4 edges contain triangles. -/
axiom turan_triangle (G : SimpleGraph V) [DecidableRel G.Adj] :
  edgeCount G > turanEdges (Fintype.card V) →
  ∃ S : Finset V, S.card = 3 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-
## The Induced Subgraph

Checking for substructures.
-/

/-- The induced subgraph on a set of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj u v := G.Adj u.val v.val
  symm := fun _ _ h => G.symm h
  loopless := fun _ h => G.loopless _ h

/-- A graph contains a saturated planar subgraph on k vertices. -/
def hasSaturatedPlanarSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧
    ∀ [DecidableRel (inducedSubgraph G S).Adj], isSaturatedPlanar (inducedSubgraph G S)

/-- A graph contains a saturated planar subgraph on MORE than 3 vertices. -/
def hasLargeSaturatedPlanarSubgraph (G : SimpleGraph V) : Prop :=
  ∃ k > 3, hasSaturatedPlanarSubgraph G k

/-
## Complete Graph K₄

K₄ is the smallest saturated planar graph with more than 3 vertices.
-/

/-- K₄ is a saturated planar graph on 4 vertices. -/
axiom K4_saturated_planar : isSaturatedPlanar (completeGraph 4)

/-- A graph contains K₄ as a subgraph. -/
def containsK4 (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, S.card = 4 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- K₄ gives a saturated planar subgraph on 4 vertices. -/
theorem K4_gives_large_saturated (G : SimpleGraph V) :
    containsK4 G → hasLargeSaturatedPlanarSubgraph G := by
  sorry

/-
## Cycle Plus Independent Vertices

C_l + 2K₁ is a cycle with two additional vertices connected to all cycle vertices.
-/

/-- C_l + 2K₁ structure: cycle of length l with 2 apex vertices. -/
def containsCyclePlus2K1 (G : SimpleGraph V) (l : ℕ) : Prop :=
  l ≥ 3 ∧ ∃ (cycle : Fin l → V) (apex1 apex2 : V),
    apex1 ≠ apex2 ∧
    (∀ i, apex1 ∉ Set.range cycle) ∧
    (∀ i, apex2 ∉ Set.range cycle) ∧
    (∀ i : Fin l, G.Adj (cycle i) (cycle ⟨(i.val + 1) % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by omega : 0 < 3) ‹l ≥ 3›)⟩)) ∧
    (∀ i : Fin l, G.Adj apex1 (cycle i)) ∧
    (∀ i : Fin l, G.Adj apex2 (cycle i))

/-- C_l + 2K₁ is a saturated planar graph on l + 2 vertices. -/
axiom cyclePlus2K1_saturated_planar (l : ℕ) (hl : l ≥ 3) :
  ∀ (G : SimpleGraph (Fin (l + 2))),
    containsCyclePlus2K1 G l → isSaturatedPlanar G

/-- C_l + 2K₁ gives a large saturated planar subgraph. -/
theorem cyclePlus2K1_gives_large_saturated (G : SimpleGraph V) (l : ℕ) (hl : l ≥ 3) :
    containsCyclePlus2K1 G l → hasLargeSaturatedPlanarSubgraph G := by
  sorry

/-
## Erdős's Construction

There exist graphs with ⌊n²/4⌋ + ⌊(n-1)/2⌋ edges without large saturated planar subgraphs.
-/

/-- The lower threshold: ⌊n²/4⌋ + ⌊(n-1)/2⌋. -/
def lowerThreshold (n : ℕ) : ℕ := turanEdges n + (n - 1) / 2

/-- Erdős's construction achieves the lower threshold. -/
axiom erdos_construction_exists :
  ∀ n ≥ 4, ∃ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n ∧
    ∃ (G : SimpleGraph V) [DecidableRel G.Adj],
      edgeCount G = lowerThreshold n ∧ ¬hasLargeSaturatedPlanarSubgraph G

/-
## The Main Question

Does exceeding the threshold guarantee a large saturated planar subgraph?
-/

/-- The main question: does the threshold guarantee large saturated planar subgraphs? -/
def erdos_1019_question : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ 4 →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      exceedsThreshold G → hasLargeSaturatedPlanarSubgraph G

/-
## Simonovits's Theorem

The answer is YES: such graphs contain K₄ or C_l + 2K₁.
-/

/-- Simonovits (PhD thesis): Dense graphs contain K₄ or C_l + 2K₁. -/
axiom simonovits_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ 4 →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      exceedsThreshold G →
      containsK4 G ∨ ∃ l ≥ 3, containsCyclePlus2K1 G l

/-- The answer is YES: C_ε exists for all ε > 0. -/
theorem erdos_1019_solved : erdos_1019_question := by
  intro V _ _ hn G _ hDense
  obtain h | ⟨l, hl, hCycle⟩ := simonovits_theorem V hn G hDense
  · exact K4_gives_large_saturated G h
  · exact cyclePlus2K1_gives_large_saturated G l hl hCycle

/-
## Related Results

Erdős also proved a quantitative lower bound on the size of saturated planar subgraphs.
-/

/-- The lower bound on saturated planar subgraph size. -/
def saturatedPlanarSize (n k : ℕ) : ℕ := k / n

/-- Erdős (1969): Graphs with n²/4 + k edges have saturated planar subgraphs on ≫ k/n vertices. -/
axiom erdos_size_bound (n k : ℕ) (hn : n ≥ 4) :
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      edgeCount G ≥ turanEdges n + k →
      ∃ S : Finset V, S.card ≥ saturatedPlanarSize n k ∧
        ∀ [DecidableRel (inducedSubgraph G S).Adj], isSaturatedPlanar (inducedSubgraph G S)

/-
## Connection to Turán Theory

The threshold relates to extremal graph theory.
-/

/-- The complete bipartite graph K_{m,n}. -/
def completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := fun x y h => by cases x <;> cases y <;> simp_all
  loopless := fun x h => by cases x <;> simp at h

/-- Complete bipartite graphs are planar but not saturated (for large n). -/
theorem bipartite_not_saturated (m n : ℕ) (hm : m ≥ 3) (hn : n ≥ 3) :
    isPlanar (completeBipartite m n) → ¬isSaturatedPlanar (completeBipartite m n) := by
  sorry

/-
## Threshold Gap

The gap between lowerThreshold and saturatedPlanarThreshold is exactly 1.
-/

/-- The gap is exactly 1: the threshold is tight. -/
theorem threshold_gap (n : ℕ) (hn : n ≥ 1) :
    saturatedPlanarThreshold n = lowerThreshold n + 1 := by
  unfold saturatedPlanarThreshold lowerThreshold turanEdges additionalThreshold
  omega

/-- This shows the threshold is optimal. -/
theorem threshold_optimal :
    ∀ n ≥ 4,
      (∀ (V : Type*) [Fintype V] [DecidableEq V],
        Fintype.card V = n →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          edgeCount G ≥ saturatedPlanarThreshold n → hasLargeSaturatedPlanarSubgraph G) ∧
      (∃ (V : Type*) [Fintype V] [DecidableEq V],
        Fintype.card V = n ∧
        ∃ (G : SimpleGraph V) [DecidableRel G.Adj],
          edgeCount G = lowerThreshold n ∧ ¬hasLargeSaturatedPlanarSubgraph G) := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1019 on saturated planar subgraphs.

**Status**: SOLVED (Simonovits, PhD thesis)

**The Question**: Does every graph on n vertices with ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges
contain a saturated planar graph with more than 3 vertices?

**The Answer**: YES. Such graphs must contain either K₄ or C_l + 2K₁.

**Key Results**:
- Simonovits: Affirmative answer via K₄ or C_l + 2K₁
- Erdős construction: ⌊n²/4⌋ + ⌊(n-1)/2⌋ edges is achievable without large saturated planar
- The threshold is optimal (gap of exactly 1 edge)

**Related Topics**:
- Turán theory for triangles
- Extremal graph theory
- Planar graph characterization
-/

end Erdos1019
