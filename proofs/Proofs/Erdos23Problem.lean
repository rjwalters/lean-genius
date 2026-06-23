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

/-
## Background

A graph is **bipartite** if and only if it contains no odd cycles.
Triangle-free graphs avoid the shortest odd cycle (length 3), but may
still contain odd cycles of length 5, 7, etc.

The question asks: how many edges must we delete from a triangle-free
graph to eliminate all odd cycles?

The blow-up of C₅ shows that n² can be necessary. The conjecture is
that n² is also sufficient for any triangle-free graph on 5n vertices.
-/

/-
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
    (∀ i : Fin k, ∃ j : Fin k, j.val = (i.val + 1) % k ∧ G.adj (path i) (path j))

/-
## Edge Deletion and Bipartiteness
-/

/-- The bipartite edge deletion number: minimum edges to delete to make bipartite. -/
axiom bipartiteEdgeDeletion {V : Type*} [Fintype V] (G : Graph V) : ℕ

/-
## The Blow-Up of C₅

The canonical extremal example: replace each vertex of C₅ with n vertices.
-/

/-- The 5-cycle C₅. -/
def C5 : Graph (Fin 5) where
  adj := fun i j => (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
  symm := fun _ _ h => Or.symm h
  loopless := fun i h => by
    rcases h with h | h <;> omega

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

/-- C₅ is triangle-free: no three vertices are mutually adjacent. -/
theorem c5_triangle_free : IsTriangleFree C5 := by
  intro ⟨i, j, k, hij_ne, hjk_ne, hik_ne, hij, hjk, hik⟩
  simp only [C5] at hij hjk hik
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- The blow-up of C₅ is triangle-free.
    (Adjacent parts in C₅ are non-adjacent in the next step.) -/
theorem c5_blowup_triangle_free (n : ℕ) : IsTriangleFree (c5BlowUpGraph n) := by
  intro ⟨⟨i, _⟩, ⟨j, _⟩, ⟨k, _⟩, hij_ne, hjk_ne, hik_ne, hij, hjk, hik⟩
  simp only [c5BlowUpGraph] at hij hjk hik
  have hne1 : i ≠ j := fun h => by subst h; exact C5.loopless i hij
  have hne2 : j ≠ k := fun h => by subst h; exact C5.loopless j hjk
  have hne3 : i ≠ k := fun h => by subst h; exact C5.loopless i hik
  exact c5_triangle_free ⟨i, j, k, hne1, hne2, hne3, hij, hjk, hik⟩

/-
## The Main Conjecture
-/

/-- Erdős's Conjecture: Every triangle-free graph on 5n vertices can be
    made bipartite by deleting at most n² edges. -/
def ErdosConjecture23 : Prop :=
  ∀ n : ℕ, ∀ V : Type, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    Fintype.card V = 5 * n →
    ∀ G : Graph V, IsTriangleFree G →
      bipartiteEdgeDeletion G ≤ n^2

-- The conjecture remains OPEN.

/-
## Best Known Bounds
-/

/-
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

/-
## The Blow-Up Construction for General k
-/

/-
## Connection to Turán-Type Problems
-/

/-
## Odd Cycle Cover Equivalence
-/

/-
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
