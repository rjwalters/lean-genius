/-
  Aristotle companion for Erdős Problem #548: The Erdős-Sós Conjecture

  Routine supporting lemmas for automated proof search by Aristotle.
  See Erdos548Problem.lean for the main formalization.

  Note: extremalNumber is defined via Nat.sInf on a sorry-based bound;
  Aristotle skips that. This companion focuses on concrete graph constructions
  (pathGraph, starGraph) and the handshaking lemma.

  All 5 targets PROVED directly (2026-07-23, researcher-1) — no sorries remain:
  - pathGraph_adj_symm: adjacency in the path graph is symmetric (by definition)
  - starGraph_center_adj: center vertex is adjacent to every leaf
  - starGraph_adj_symm: adjacency in the star graph is symmetric (by definition)
  - sum_degrees_twice_edges_ari: handshaking lemma for edgeCount
  - containsSubgraph_refl: every graph contains itself as a subgraph
-/

import Mathlib
import Proofs.Erdos548Problem

namespace Erdos548Aristotle

open Erdos548 SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency in the path graph is symmetric: if i→j then j→i. -/
theorem pathGraph_adj_symm (n : ℕ) (i j : Fin n) :
    (Erdos548.pathGraph n).Adj i j ↔ (Erdos548.pathGraph n).Adj j i :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- The center vertex (index 0) is adjacent to every leaf in the star graph. -/
theorem starGraph_center_adj (k : ℕ) (hk : k ≥ 1) (j : Fin (k + 1))
    (hj : j.val ≠ 0) : (Erdos548.starGraph k).Adj ⟨0, Nat.zero_lt_succ k⟩ j :=
  Or.inl ⟨rfl, hj⟩

/-- Adjacency in the star graph is symmetric. -/
theorem starGraph_adj_symm (k : ℕ) (i j : Fin (k + 1)) :
    (Erdos548.starGraph k).Adj i j ↔ (Erdos548.starGraph k).Adj j i :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- The handshaking lemma: sum of degrees equals twice the edge count.
    Uses Mathlib's SimpleGraph.sum_degrees_eq_twice_card_edges. -/
theorem sum_degrees_twice_edges_ari (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Finset.univ.sum fun v => G.degree v) = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

/-- Every graph contains itself as a subgraph (identity injection). -/
theorem containsSubgraph_refl (G : SimpleGraph V) : ContainsSubgraph G G :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

end Erdos548Aristotle
