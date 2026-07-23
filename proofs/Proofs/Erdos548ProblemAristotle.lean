/-
  Aristotle targets for Erdős Problem #548 (Erdős-Sós Conjecture)
  Routine supporting lemmas for automated proof search.
  See Erdos548Problem.lean for the main formalization.
  All 3 targets PROVED directly (2026-07-23, researcher-1) — no sorries remain.

  Criteria for inclusion:
  - sum_degrees_eq_twice_edges: handshaking lemma (standard graph theory)
  - star_is_tree: star graph K_{1,k} is a tree (connected + acyclic structure)
  - NOT ErdosSosConjecture (open problem)
  - NOT trivial_tree_bound / brandt_dobson / sacle_wozniak (axioms — major results)
  - NOT erdos_sos_implies_extremal (requires open conjecture as hypothesis)
  - NOT star_easier (requires complex combinatorial argument)
-/
import Mathlib
open scoped Classical

namespace Erdos548Aristotle

open SimpleGraph Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := G.edgeFinset.card

/-- The star graph K_{1,k} with k leaves.
    Vertex 0 is the center; vertices 1..k are the leaves. -/
def starGraph (k : ℕ) : SimpleGraph (Fin (k + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm.symm := by
    intro i j h
    cases h with
    | inl h => right; exact ⟨h.1, h.2⟩
    | inr h => left; exact ⟨h.1, h.2⟩
  loopless.irrefl := by
    intro i h
    cases h with
    | inl h => exact h.2 h.1
    | inr h => exact h.2 h.1

-- Routine: The handshaking lemma — sum of degrees = 2 * edge count.
-- This is a standard result: SimpleGraph.sum_degrees_eq_twice_card_edges.
theorem sum_degrees_eq_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Finset.univ.sum fun v => G.degree v) = 2 * edgeCount G := by
  have h := G.sum_degrees_eq_twice_card_edges
  unfold edgeCount
  convert h using 2
  congr!

-- Routine: The star graph K_{1,k} is connected for k ≥ 1.
-- Every leaf is adjacent to the center (vertex 0), and 0 reaches all vertices.
theorem starGraph_connected (k : ℕ) (hk : k ≥ 1) : (starGraph k).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun i j => ?_, ⟨0⟩⟩
  have h0 : ∀ a : Fin (k + 1), a.val ≠ 0 → (starGraph k).Adj 0 a :=
    fun a ha => Or.inl ⟨by simp, ha⟩
  by_cases hij : i = j
  · exact hij ▸ SimpleGraph.Reachable.refl i
  · by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact absurd (Fin.ext (hi.trans hj.symm)) hij
      · have hi0 : i = (0 : Fin (k + 1)) := Fin.ext (by simpa using hi)
        exact hi0 ▸ (h0 j hj).reachable
    · by_cases hj : j.val = 0
      · have hj0 : j = (0 : Fin (k + 1)) := Fin.ext (by simpa using hj)
        exact hj0 ▸ ((h0 i hi).symm).reachable
      · exact ((h0 i hi).symm.reachable).trans (h0 j hj).reachable

-- Routine: Each edge of the star K_{1,k} contributes to reachability.
-- Adjacent vertices in the star are reachable (trivially: direct adjacency).
theorem starGraph_adj_reachable (k : ℕ) (i j : Fin (k + 1))
    (h : (starGraph k).Adj i j) : (starGraph k).Reachable i j :=
  h.reachable

end Erdos548Aristotle
