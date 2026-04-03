/-
  Aristotle targets for Erdős Problem #548
  Routine supporting lemmas for automated proof search.
  See Erdos548Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT ErdosSosConjecture (open problem)
  - NOT erdos_sos_implies_extremal (depends on open conjecture as hypothesis)
  - NOT erdos_548_status (asserts open conjecture via Or.inl — always sorry)
  - NOT axiom-dependent theorems
  - Routine graph structure: star adjacency, star connectivity, handshaking lemma
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos548Aristotle

open SimpleGraph Finset

/-- The star graph K_{1,k} with k leaves. -/
def starGraph (k : ℕ) : SimpleGraph (Fin (k + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm := by
    intro i j h
    cases h with
    | inl h => right; exact ⟨h.2, h.1⟩
    | inr h => left; exact ⟨h.2, h.1⟩
  loopless := by
    intro i h
    cases h with
    | inl h => exact h.2 h.1
    | inr h => exact h.2 h.1

/-- Number of edges in a graph. -/
noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

-- Routine: Adjacency in the star graph iff one vertex is center and other is not.
-- Follows directly from the definition of starGraph.
theorem starGraph_adj_iff (k : ℕ) (i j : Fin (k + 1)) :
    (starGraph k).Adj i j ↔ (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0) := by
  simp [starGraph]

-- Routine: The center vertex (0) is adjacent to every non-center vertex.
-- By definition, (0, j) satisfies the left disjunct when j.val ≠ 0.
theorem starGraph_center_adj (k : ℕ) (j : Fin (k + 1)) (hj : j.val ≠ 0) :
    (starGraph k).Adj ⟨0, Nat.succ_pos k⟩ j := by
  simp [starGraph]
  exact hj

-- Routine: Every non-center vertex is adjacent to the center.
-- By definition, (i, 0) satisfies the right disjunct when i.val ≠ 0.
theorem starGraph_leaf_adj_center (k : ℕ) (i : Fin (k + 1)) (hi : i.val ≠ 0) :
    (starGraph k).Adj i ⟨0, Nat.succ_pos k⟩ := by
  simp [starGraph]
  exact hi

-- Routine: The star graph has no self-loops.
-- Adj i i would require i.val = 0 ∧ i.val ≠ 0, a contradiction.
theorem starGraph_loopless (k : ℕ) (i : Fin (k + 1)) :
    ¬(starGraph k).Adj i i := by
  simp [starGraph]

-- Routine: Non-center vertices are not adjacent to each other.
-- Two leaves i, j (both ≠ 0) satisfy neither disjunct of the adjacency condition.
theorem starGraph_leaves_not_adj (k : ℕ) (i j : Fin (k + 1))
    (hi : i.val ≠ 0) (hj : j.val ≠ 0) :
    ¬(starGraph k).Adj i j := by
  simp [starGraph, hi, hj]

-- Routine: Sum of degrees equals twice the number of edges (handshaking lemma).
-- Mathlib: SimpleGraph.sum_degrees_eq_twice_card_edges gives
-- ∑ v, G.degree v = 2 * G.edgeFinset.card.
theorem sum_degrees_eq_twice_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Finset.univ.sum fun v => G.degree v) = 2 * edgeCount G := by
  sorry

-- Routine: For k ≥ 1, the star K_{1,k} is connected.
-- Every vertex is reachable from the center: non-center vertices via direct edge.
theorem starGraph_connected (k : ℕ) (hk : k ≥ 1) : (starGraph k).Connected := by
  sorry

-- Routine: In K_{1,k}, any two distinct vertices are reachable from each other.
-- Center reaches all via direct edge; leaves reach other leaves via center.
theorem starGraph_reachable (k : ℕ) (hk : k ≥ 1) (i j : Fin (k + 1)) :
    (starGraph k).Reachable i j := by
  sorry

-- Routine: k ≥ 1 implies Fin (k + 1) is nonempty.
theorem starGraph_nonempty (k : ℕ) (hk : k ≥ 1) : Nonempty (Fin (k + 1)) := by
  exact ⟨⟨0, Nat.succ_pos k⟩⟩

-- Routine: 2 ^ n > 0 for all n.
-- Positive powers of 2 are positive.
theorem two_pow_pos (n : ℕ) : 2 ^ n > 0 := Nat.pos_pow_of_pos n (by norm_num)

-- Routine: For k ≥ 1, k + 1 ≥ 2.
theorem k_succ_ge_two (k : ℕ) (hk : k ≥ 1) : k + 1 ≥ 2 := by omega

end Erdos548Aristotle
