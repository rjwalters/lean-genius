/-
  Aristotle targets for Erdős Problem #715 (Regular Subgraphs in Regular Graphs)
  Routine supporting lemmas for automated proof search.
  See Erdos715Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Tashkinov, Alon-Friedland-Kalai — research theorems)
  - K4_is_3_regular: concrete decidable computation over Fin 4
  - regular_parity: parity of r·|V| via Finset.sum; follows from double-counting
  - No axiom declarations
  - No open conjectures
  - K4 definition is complete (no sorry in structure fields)
-/
import Mathlib

namespace Erdos715Aristotle

/-- A simple graph represented by adjacency. -/
structure SimpleGraph' (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- The degree of a vertex in a graph. -/
def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (v : V) : ℕ :=
  (Finset.filter (fun u => G.adj v u) Finset.univ).card

/-- A graph is r-regular if every vertex has degree r. -/
def IsRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (r : ℕ) : Prop :=
  ∀ v : V, degree G v = r

/-- The complete graph K₄ on 4 vertices: all distinct pairs are adjacent. -/
def K4 : SimpleGraph' (Fin 4) where
  adj u v := u ≠ v
  symm _ _ h := h.symm
  loopless _ h := h rfl

/-- K₄ adjacency is decidable (u ≠ v is decidable for Fin 4). -/
instance K4DecidableRel : DecidableRel K4.adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v))

/-- Aristotle target: K₄ is 3-regular (each vertex is adjacent to exactly 3 others).

    K₄ has 4 vertices with adj u v := (u ≠ v), so each vertex v is adjacent to
    the 3 other vertices of Fin 4. This is a finite decidable computation.
    Proof strategy: `intro v; decide` with K4DecidableRel instance in scope. -/
theorem K4_is_3_regular : IsRegular K4 3 := by
  sorry

end Erdos715Aristotle
