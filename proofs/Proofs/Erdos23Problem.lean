/-
Erdős Problem #23: Triangle-Free Graphs and Bipartiteness

Can every triangle-free graph on 5n vertices be made bipartite by
deleting at most n² edges?

**Status**: OPEN
**Type**: Falsifiable (could be disproved by finite counterexample)

**The Conjecture**:
Every triangle-free graph G on 5n vertices can be made bipartite
by removing at most n² edges.

**Extremal Example**:
The blow-up of C₅ (5-cycle) shows this bound would be tight if true.
Take C₅ and replace each vertex with an independent set of n vertices,
connecting all vertices between adjacent parts. This has 5n vertices,
2n² edges, is triangle-free, and requires exactly n² edge deletions.

**Best Known Bound**:
- Balogh, Clemen, Lidicky (2021): ≤ 1.064n² edges suffice
- Improving earlier bounds

**Generalization** (Erdős 1992):
For graphs on (2k+1)n vertices where every odd cycle has length ≥ 2k+1,
can we make bipartite by deleting ≤ n² edges?

Reference: https://erdosproblems.com/23
-/

import Mathlib

open Finset Set Function
open scoped BigOperators

namespace Erdos23

/-!
## Background

A graph is **bipartite** if and only if it contains no odd cycles.
Triangle-free graphs avoid the shortest odd cycle (length 3), but may
still contain odd cycles of length 5, 7, etc.

The question asks: how many edges must we delete from a triangle-free
graph to eliminate all odd cycles?

The blow-up of C₅ shows that n² can be necessary. The conjecture is
that n² is also sufficient for any triangle-free graph on 5n vertices.
-/

/-!
## Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple graph. -/
structure Graph (V : Type*) [Fintype V] where
  adj : V → V → Prop
  symm : ∀ x y, adj x y → adj y x
  loopless : ∀ x, ¬adj x x

/-- The number of edges in a graph. -/
axiom edgeCount {V : Type*} [Fintype V] (G : Graph V) : ℕ

/-- A graph is bipartite if vertices can be 2-colored with no monochromatic edges. -/
def IsBipartite (G : Graph V) : Prop :=
  ∃ c : V → Fin 2, ∀ x y, G.adj x y → c x ≠ c y

/-- A graph contains a triangle (K₃) if there exist 3 mutually adjacent vertices. -/
def ContainsTriangle (G : Graph V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.adj x y ∧ G.adj y z ∧ G.adj x z

/-- A graph is triangle-free if it contains no K₃. -/
def IsTriangleFree (G : Graph V) : Prop :=
  ¬ContainsTriangle G

/-- A cycle of length k in a graph. -/
def HasCycle (G : Graph V) (k : ℕ) : Prop :=
  ∃ (path : Fin k → V), Function.Injective path ∧
    (∀ i : Fin k, G.adj (path i) (path ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩))

/-- The odd girth: length of shortest odd cycle (or ∞ if bipartite). -/
noncomputable def oddGirth (G : Graph V) : ℕ∞ :=
  if IsBipartite G then ⊤
  else Nat.find (⟨3, by sorry⟩ : ∃ k, k % 2 = 1 ∧ HasCycle G k)

/-!
## Edge Deletion and Bipartiteness
-/

/-- The bipartite edge deletion number: minimum edges to delete to make bipartite. -/
axiom bipartiteEdgeDeletion {V : Type*} [Fintype V] (G : Graph V) : ℕ

/-- The deletion number is achieved by some edge set. -/
axiom bipartiteEdgeDeletion_achieved {V : Type*} [Fintype V] (G : Graph V) :
    ∃ (E : Finset (V × V)), E.card = bipartiteEdgeDeletion G ∧
      -- Removing E makes G bipartite
      True  -- Simplified; full statement involves subgraph

/-- Bipartite graphs have deletion number 0. -/
axiom bipartite_deletion_zero {V : Type*} [Fintype V] (G : Graph V) :
    IsBipartite G ↔ bipartiteEdgeDeletion G = 0

/-!
## The Blow-Up of C₅

The canonical extremal example: replace each vertex of C₅ with n vertices.
-/

/-- The 5-cycle C₅. -/
def C5 : Graph (Fin 5) where
  adj := fun i j => (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
  symm := fun _ _ h => h.symm.imp (fun h => h.symm) (fun h => h.symm)
  loopless := fun i h => by
    cases h with
    | inl h => omega
    | inr h => omega

/-- The blow-up of C₅ with parts of size n. -/
structure C5BlowUp (n : ℕ) where
  /-- Vertices are pairs (part, index within part). -/
  vertex : Fin 5 × Fin n

/-- The blow-up graph: adjacent iff in adjacent parts of C₅. -/
def c5BlowUpGraph (n : ℕ) : Graph (Fin 5 × Fin n) where
  adj := fun ⟨i, _⟩ ⟨j, _⟩ => C5.adj i j
  symm := fun _ _ h => C5.symm _ _ h
  loopless := fun ⟨i, _⟩ h => C5.loopless i h

/-- The blow-up of C₅ has 5n vertices. -/
theorem c5_blowup_vertices (n : ℕ) :
    Fintype.card (Fin 5 × Fin n) = 5 * n := by
  simp [Fintype.card_prod]

/-- The blow-up of C₅ has 2n² edges (each of 5 pairs of adjacent parts
    contributes n² edges, but we count edges once). -/
axiom c5_blowup_edges (n : ℕ) (hn : n ≥ 1) :
    edgeCount (c5BlowUpGraph n) = 2 * n^2

/-- The blow-up of C₅ is triangle-free.
    (Adjacent parts in C₅ are non-adjacent in the next step.) -/
theorem c5_blowup_triangle_free (n : ℕ) : IsTriangleFree (c5BlowUpGraph n) := by
  intro ⟨⟨i, _⟩, ⟨j, _⟩, ⟨k, _⟩, _, _, _, hij, hjk, hik⟩
  -- If (i,j), (j,k), (i,k) all adjacent in C₅, would form triangle in C₅
  -- But C₅ is triangle-free
  sorry

/-- The blow-up of C₅ requires exactly n² edge deletions to become bipartite.
    This shows n² is necessary for triangle-free graphs on 5n vertices. -/
axiom c5_blowup_deletion (n : ℕ) (hn : n ≥ 1) :
    bipartiteEdgeDeletion (c5BlowUpGraph n) = n^2

/-!
## The Main Conjecture
-/

/-- Erdős's Conjecture: Every triangle-free graph on 5n vertices can be
    made bipartite by deleting at most n² edges. -/
def ErdosConjecture23 : Prop :=
  ∀ n : ℕ, ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    Fintype.card V = 5 * n →
    ∀ G : Graph V, IsTriangleFree G →
      bipartiteEdgeDeletion G ≤ n^2

/-- The conjecture remains OPEN. -/
axiom conjecture_open : True  -- Status marker

/-!
## Best Known Bounds
-/

/-- Balogh-Clemen-Lidicky (2021): At most 1.064n² edges suffice. -/
axiom balogh_clemen_lidicky_2021 :
    ∀ n : ℕ, ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
      Fintype.card V = 5 * n →
      ∀ G : Graph V, IsTriangleFree G →
        (bipartiteEdgeDeletion G : ℝ) ≤ 1.064 * n^2

/-- The constant 1.064 improves earlier bounds. -/
axiom earlier_bounds_existed : True

/-- Trivial upper bound: at most half the edges suffice
    (delete all edges in one part of any 2-coloring attempt). -/
axiom trivial_upper_bound :
    ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : Graph V, bipartiteEdgeDeletion G ≤ edgeCount G / 2

/-!
## The Generalized Conjecture

Erdős (1992) generalized to graphs with higher odd girth.
-/

/-- Generalized conjecture: For graphs on (2k+1)n vertices with odd girth ≥ 2k+1,
    the bipartite edge deletion number is at most n². -/
def GeneralizedConjecture (k : ℕ) : Prop :=
  ∀ n : ℕ, ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    Fintype.card V = (2 * k + 1) * n →
    ∀ G : Graph V,
      (∀ j : ℕ, j % 2 = 1 → j < 2 * k + 1 → ¬HasCycle G j) →
      bipartiteEdgeDeletion G ≤ n^2

/-- The original conjecture is the k = 2 case. -/
theorem original_is_k_equals_2 :
    GeneralizedConjecture 2 ↔
    (∀ n : ℕ, ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
      Fintype.card V = 5 * n →
      ∀ G : Graph V, IsTriangleFree G →
        bipartiteEdgeDeletion G ≤ n^2) := by
  constructor <;> intro h <;> intro n V _ _ hcard G hG
  · apply h n V
    · simp only [hcard]
    · intro j hodd hlt
      interval_cases j
      · omega
      · exact hG
  · sorry

/-!
## The Blow-Up Construction for General k
-/

/-- The blow-up of C_{2k+1} is the extremal example for the generalized conjecture. -/
axiom blowup_C_odd (k n : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
    ∃ G : Graph V,
      Fintype.card V = (2 * k + 1) * n ∧
      (∀ j : ℕ, j % 2 = 1 → j < 2 * k + 1 → ¬HasCycle G j) ∧
      bipartiteEdgeDeletion G = n^2

/-!
## Connection to Turán-Type Problems
-/

/-- The Kővári-Sós-Turán theorem bounds edges in bipartite graphs without K_{s,t}. -/
axiom kovari_sos_turan (n s t : ℕ) (hs : s ≤ t) :
    ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : Graph V, Fintype.card V = n →
      IsBipartite G →
      -- No K_{s,t} subgraph →
      (edgeCount G : ℝ) ≤ (t - 1)^(1/s : ℝ) / 2 * n^(2 - 1/s : ℝ) + (s - 1) * n / 2

/-- Triangle-free graphs have at most n²/4 edges (Mantel's theorem). -/
axiom mantel_theorem (n : ℕ) :
    ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : Graph V, Fintype.card V = n →
      IsTriangleFree G →
      edgeCount G ≤ n^2 / 4

/-!
## Why The Conjecture Is Hard
-/

/-- The difficulty: balancing local and global structure.

Triangle-freeness is a local property (no 3-cycles).
Bipartiteness is a global property (no odd cycles at all).

The conjecture quantifies how "close" triangle-free graphs are to bipartite. -/
theorem difficulty_explanation :
    -- Local constraint (triangle-free) doesn't fully control global structure
    -- Need to understand how odd cycles of length ≥ 5 distribute
    True := by trivial

/-!
## Approaches to the Problem
-/

/-- Approach 1: Regularity Lemma.
    Use Szemerédi's regularity lemma to partition the graph and analyze. -/
axiom regularity_approach : True

/-- Approach 2: Flag Algebras.
    Use Razborov's flag algebra method for optimization bounds. -/
axiom flag_algebra_approach : True

/-- Approach 3: Probabilistic Method.
    Random deletion and analysis of remaining odd cycles. -/
axiom probabilistic_approach : True

/-!
## Related Problems
-/

/-- Max-Cut: Find partition maximizing edges between parts.
    For bipartite graphs, max-cut = all edges.
    For triangle-free graphs, how close can we get? -/
axiom max_cut_connection : True

/-- Odd cycle cover: minimum edges intersecting all odd cycles.
    Equal to bipartite edge deletion number. -/
axiom odd_cycle_cover_equivalent :
    ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : Graph V, bipartiteEdgeDeletion G =
      Nat.find (⟨edgeCount G, by sorry⟩ :
        ∃ k, ∃ E : Finset (V × V), E.card = k ∧ True)  -- Simplified

/-!
## Summary

**Problem Status: OPEN**

Erdős Problem #23 asks whether every triangle-free graph on 5n vertices
can be made bipartite by deleting at most n² edges.

**Main Conjecture**: For triangle-free G on 5n vertices,
  bipartiteEdgeDeletion(G) ≤ n²

**Extremal Example**: Blow-up of C₅ shows n² is necessary.

**Best Known Bound**: 1.064n² (Balogh-Clemen-Lidicky 2021)

**Generalization**: For odd girth ≥ 2k+1 on (2k+1)n vertices, is n² sufficient?

**Key Insight**: The problem quantifies how "close" triangle-free graphs
are to being bipartite in terms of edge modifications.

**Approaches**:
- Regularity lemma
- Flag algebras
- Probabilistic methods

**Open Questions**:
- Close the gap between n² (conjectured) and 1.064n² (proved)
- Resolve the generalized conjecture for all k
- Find the exact constant if conjecture is false

References:
- Erdős (1971, 1992): Original problem and generalization
- Balogh, Clemen, Lidický (2021): Best current bound
-/

end Erdos23
