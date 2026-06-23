/-
  Aristotle targets for Erdős Problem #546
  Routine supporting lemmas for automated proof search.
  See Erdos546Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Sudakov/AKS bounds — require deep probabilistic arguments)
  - Routine supporting facts: edge counts for paths, cycles, complete bipartite graphs
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos546Aristotle

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of edges in a simple graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- A graph has no isolated vertices. -/
def NoIsolatedVertices (G : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ w : V, G.Adj v w

/-- Path graph on n vertices: vertex i adjacent to i+1. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j h; cases h with | inl h => right; exact h | inr h => left; exact h
  loopless := by intro i h; cases h with | inl h => omega | inr h => omega

/-- Cycle graph on n vertices (n ≥ 3): vertex i adjacent to (i+1) mod n. -/
def cycleGraph (n : ℕ) (hn : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val % n) ∨ (j.val + 1 = i.val % n)
  symm := by intro i j h; cases h with | inl h => right; exact h | inr h => left; exact h
  loopless := by intro i h; cases h with | inl h => simp at h | inr h => simp at h

/-- Complete bipartite graph K_{a,b}. -/
def completeBipartite (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := match x, y with
    | Sum.inl _, Sum.inr _ => true
    | Sum.inr _, Sum.inl _ => true
    | _, _ => false
  symm := by intro x y; simp only; cases x <;> cases y <;> simp
  loopless := by intro x; cases x <;> simp

-- Routine: pathGraph n has n-1 edges.
theorem path_edge_count (n : ℕ) (hn : n ≥ 1) :
    edgeCount (pathGraph n) = n - 1 := by
  sorry

-- Routine: cycleGraph n hn has n edges.
theorem cycle_edge_count (n : ℕ) (hn : n ≥ 3) :
    edgeCount (cycleGraph n hn) = n := by
  sorry

-- Routine: completeBipartite a b has a * b edges.
theorem complete_bipartite_edge_count (a b : ℕ) :
    edgeCount (completeBipartite a b) = a * b := by
  sorry

-- Routine: pathGraph n has no isolated vertices when n ≥ 2.
theorem path_no_isolated (n : ℕ) (hn : n ≥ 2) :
    NoIsolatedVertices (pathGraph n) := by
  sorry

-- Routine: cycleGraph n hn has no isolated vertices.
theorem cycle_no_isolated (n : ℕ) (hn : n ≥ 3) :
    NoIsolatedVertices (cycleGraph n hn) := by
  sorry

-- Routine: completeBipartite a b has no isolated vertices when a ≥ 1 and b ≥ 1.
theorem complete_bipartite_no_isolated (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) :
    NoIsolatedVertices (completeBipartite a b) := by
  sorry

-- Routine: edgeCount (pathGraph (n+1)) = edgeCount (pathGraph n) + 1 for n ≥ 1.
theorem path_edge_count_succ (n : ℕ) (hn : n ≥ 1) :
    edgeCount (pathGraph (n + 1)) = edgeCount (pathGraph n) + 1 := by
  sorry

end Erdos546Aristotle
