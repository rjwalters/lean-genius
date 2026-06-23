/-
  Aristotle targets for Erdos715Problem
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos715Problem.lean for the main formalization.
-/
import Mathlib

namespace Erdos715.Aristotle

/-- A simple graph represented by adjacency -/
structure SimpleGraph' (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- The degree of a vertex in a graph -/
def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (v : V) : ℕ :=
  (Finset.filter (fun u => G.adj v u) Finset.univ).card

/-- A graph is r-regular if every vertex has degree r -/
def IsRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (r : ℕ) : Prop :=
  ∀ v : V, degree G v = r

/-- The complete graph K_4 -/
def K4 : SimpleGraph' (Fin 4) where
  adj u v := u ≠ v
  symm _ _ h := h.symm
  loopless _ h := h rfl

instance : DecidableRel K4.adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

/-- K_4 is 3-regular: every vertex has degree 3. -/
theorem K4_is_3_regular : IsRegular K4 3 := by
  intro v; fin_cases v <;> native_decide

/-- In K_4, every pair of distinct vertices is adjacent. -/
theorem K4_complete (u v : Fin 4) (h : u ≠ v) : K4.adj u v := h

/-- K_4 has exactly 6 edges. -/
theorem K4_edge_count :
    (Finset.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2 ∧ K4.adj p.1 p.2)
      Finset.univ).card = 6 := by native_decide

/-- In any r-regular graph on n vertices, r * n is even (handshaking lemma). -/
theorem regular_parity_helper (r n : ℕ) (h : 2 * e = r * n) : Even (r * n) :=
  ⟨e, by omega⟩

/-- Every vertex in a 4-regular graph has degree at least 3. -/
theorem four_reg_ge_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (v : V)
    (hG : IsRegular G 4) : degree G v ≥ 3 := by
  have := hG v; omega

/-- If H is a subgraph of G, the degree of any vertex in H is ≤ its degree in G. -/
theorem subgraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph' V) [DecidableRel G.adj] [DecidableRel H.adj]
    (hHG : ∀ u v, H.adj u v → G.adj u v) (v : V) :
    degree H v ≤ degree G v := by
  simp only [degree]
  apply Finset.card_le_card
  intro u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hHG v u

/-- A 3-regular graph on n vertices has exactly 3n/2 edges. -/
theorem three_regular_edge_formula {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (hG : IsRegular G 3) :
    2 * (Finset.filter (fun p : V × V => G.adj p.1 p.2) Finset.univ).card =
    3 * Fintype.card V := by sorry

/-- Necessary condition: a 3-regular graph must have an even number of vertices. -/
theorem three_regular_even_vertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (hG : IsRegular G 3) :
    Even (Fintype.card V) := by sorry

/-- The sum of degrees equals twice the number of edges (handshaking). -/
theorem handshaking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] :
    ∑ v : V, degree G v =
    2 * (Finset.filter (fun p : V × V => p.1 < p.2 ∧ G.adj p.1 p.2) Finset.univ).card := by
  sorry

end Erdos715.Aristotle
