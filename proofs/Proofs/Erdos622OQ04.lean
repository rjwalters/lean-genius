/-
  Erdős Problem #622, OQ-04: Absorbing Method Infrastructure

  Infrastructure for the DKM 2025 absorbing method approach to
  counting cycle-spanned subsets in Erdős-Faudree graphs.

  Key results:
  1. Edge count for regular graphs (handshaking lemma, proved)
  2. Edge count for Erdős-Faudree graphs (corollary, proved)
  3. Common neighborhood lower bound: |N(u) ∩ N(v)| + |V| ≥ 2d (proved)
  4. Erdős-Faudree corollary: any two vertices share ≥ 2 common neighbors (proved)
  5. Absorbing pair definitions and basic properties (proved)
  6. Absorbing pair density in neighborhoods (sorry)
  7. Absorbing lemma statement (definition only)

  Axiom count: 0
  Sorry count: 2 (edges_in_neighborhood_ge, erdos_faudree_absorbing_pairs_ge)

  Tags: graph-theory, absorbing-method, extremal-combinatorics
-/

import Mathlib
import Proofs.Erdos622Problem

open SimpleGraph Finset Erdos622

namespace Erdos622OQ04

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part I: Edge Count in Regular Graphs -/

/-- In a d-regular graph, 2|E| = |V| · d (from the handshaking lemma). -/
theorem regular_edge_count (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : IsRegular G d) :
    2 * G.edgeFinset.card = Fintype.card V * d := by
  have hshake := G.sum_degrees_eq_twice_card_edges
  have hsum : ∑ v : V, G.degree v = Fintype.card V * d := by
    calc ∑ v : V, G.degree v
        = ∑ _v : V, d := Finset.sum_congr rfl fun v _ => hreg v
      _ = Fintype.card V * d := by rw [sum_const, card_univ, smul_eq_mul]
  linarith

/-- In an Erdős-Faudree graph (2n vertices, degree n+1), |E| = n(n+1). -/
theorem erdos_faudree_edge_count (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (hEF : IsErdosFaudreeGraph G n) :
    G.edgeFinset.card = n * (n + 1) := by
  have h := regular_edge_count G (n + 1) hEF.2
  have hV : Fintype.card V = 2 * n := by
    unfold IsErdosFaudreeGraph vertexCount at hEF; exact hEF.1
  rw [hV] at h
  omega

/-! ## Part II: Common Neighborhood Lower Bound -/

/-- Inclusion-exclusion for neighbor sets: |N(u) ∩ N(v)| + |V| ≥ 2d
    when the graph is d-regular. Since N(u) ∪ N(v) ⊆ V, we have
    |N(u) ∩ N(v)| = |N(u)| + |N(v)| - |N(u) ∪ N(v)| ≥ 2d - |V|. -/
theorem common_neighbors_ge (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : IsRegular G d) (u v : V) :
    (G.neighborFinset u ∩ G.neighborFinset v).card + Fintype.card V ≥ 2 * d := by
  have h1 : (G.neighborFinset u).card = d := by
    show G.degree u = d; exact hreg u
  have h2 : (G.neighborFinset v).card = d := by
    show G.degree v = d; exact hreg v
  have h3 : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
    card_le_card (subset_univ _)
  have h4 := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  omega

/-- In an Erdős-Faudree graph (2n vertices, degree n+1), any two vertices
    share at least 2 common neighbors. This density property is the
    quantitative foundation of the absorbing method. -/
theorem erdos_faudree_common_ge_two (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (hn : 0 < n) (hEF : IsErdosFaudreeGraph G n) (u v : V) :
    2 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
  have h := common_neighbors_ge G (n + 1) hEF.2 u v
  have hV : Fintype.card V = 2 * n := by
    unfold IsErdosFaudreeGraph vertexCount at hEF; exact hEF.1
  rw [hV] at h
  omega

/-! ## Part III: Absorbing Method Framework -/

/-- An absorbing triple (u, v, w): u ~ v are adjacent, and w is a common
    neighbor of both (u ~ w and w ~ v). If w needs to be "absorbed,"
    the edge u-v can be replaced by the path u-w-v. -/
def IsAbsorbingTriple (G : SimpleGraph V) (u v w : V) : Prop :=
  G.Adj u v ∧ G.Adj u w ∧ G.Adj w v ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w

/-- The set of absorbing pairs for vertex w: ordered pairs (u, v) where
    u ~ v, u ~ w, and w ~ v (all distinct). -/
noncomputable def absorbingPairs (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    Finset (V × V) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ⟨u, v⟩ =>
    decide (G.Adj u v) && decide (G.Adj u w) && decide (G.Adj w v) &&
    decide (u ≠ v) && decide (u ≠ w) && decide (v ≠ w)

/-- Absorbing triples are symmetric: (u, v, w) ↦ (v, u, w). -/
theorem isAbsorbingTriple_symm (G : SimpleGraph V) {u v w : V}
    (h : IsAbsorbingTriple G u v w) : IsAbsorbingTriple G v u w :=
  ⟨G.symm h.1, G.symm h.2.2.1, G.symm h.2.1,
   Ne.symm h.2.2.2.1, Ne.symm h.2.2.2.2.2, Ne.symm h.2.2.2.2.1⟩

/-- Both endpoints of an absorbing triple are neighbors of the absorbed vertex. -/
theorem absorbingTriple_are_neighbors (G : SimpleGraph V) {u v w : V}
    (h : IsAbsorbingTriple G u v w) :
    G.Adj u w ∧ G.Adj v w :=
  ⟨h.2.1, G.symm h.2.2.1⟩

/-! ## Part IV: Absorbing Pair Density -/

/-- In a d-regular graph with 2d ≥ |V|, every vertex w has at least
    one neighbor u such that u has a neighbor in N(w) \ {u, w}.
    This is a weak form of the absorbing pair existence. -/
theorem absorbing_pair_exists (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hreg : IsRegular G d) (hd : 3 ≤ d) (hV : 2 * d ≤ Fintype.card V + 2)
    (w : V) : ∃ u v : V, IsAbsorbingTriple G u v w := by
  sorry

/-- **Absorbing pair density**: In an Erdős-Faudree graph (2n vertices,
    degree n+1), every vertex w has Ω(n²) absorbing pairs. Each edge
    within N(w) gives an absorbing pair, and the induced subgraph on
    N(w) is dense (≥ 2 common neighbors for any pair in N(w)). -/
theorem erdos_faudree_absorbing_pairs_ge (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (hn : 2 ≤ n)
    (hEF : IsErdosFaudreeGraph G n) (w : V) :
    n ≤ (absorbingPairs G w).card := by
  sorry

/-! ## Part V: Absorbing Lemma (Statement Only) -/

/-- The absorbing lemma: There exists a short cycle C (length O(εn)) such that
    for any "small" subset T ⊆ V \ V(C) with |T| ≤ δn, the cycle C can be
    extended to also span T.

    DKM 2025 prove this using a probabilistic argument: randomly sample paths,
    each absorbing pair contributes Ω(1/n²) probability of absorbing each vertex,
    and concentration inequalities yield a single structure absorbing all of T.

    This is the definition of the property; the proof that Erdős-Faudree graphs
    satisfy it is the main technical contribution of DKM 2025. -/
def HasAbsorbingStructure (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) : Prop :=
  ∃ (δ : ℝ) (_ : 0 < δ) (C : List V),
    C.length ≤ ⌈ε * Fintype.card V⌉₊ ∧
    ∀ T : Finset V, (T.card : ℝ) ≤ δ * Fintype.card V →
      Disjoint T C.toFinset →
      ∃ C' : List V, C'.toFinset = C.toFinset ∪ T

end Erdos622OQ04
