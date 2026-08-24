import Proofs.Erdos85ConnectedDefectNeighborhoodMissingPairs

/-!
# A fork in a connected defect neighborhood

The strict missing-pair surplus in one defect neighborhood cannot be a
matching: some neighbor is nonadjacent, within that neighborhood, to at
least two other neighbors.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If a graph on `q-1` vertices has `q+2` missing ordered edge slots, then
some vertex has at least two nonneighbors. -/
theorem exists_compl_degree_two_of_missingPair_slots
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    {q : ℕ} (hq : 3 ≤ q) (hcard : Fintype.card W = q - 1)
    (hslots : q + 2 + 2 * H.edgeFinset.card ≤ (q - 1) * (q - 2)) :
    ∃ y : W, 2 ≤ Hᶜ.degree y := by
  by_contra hnone
  have hdeg : ∀ y : W, Hᶜ.degree y ≤ 1 := by
    intro y
    have hlt : Hᶜ.degree y < 2 := Nat.lt_of_not_ge (by
      intro hy
      exact hnone ⟨y, hy⟩)
    omega
  have hsum_le : (∑ y : W, Hᶜ.degree y) ≤ q - 1 := by
    calc
      (∑ y : W, Hᶜ.degree y) ≤ ∑ _y : W, 1 :=
        Finset.sum_le_sum fun y _ ↦ hdeg y
      _ = Fintype.card W := by simp
      _ = q - 1 := hcard
  have hpoint : ∀ y : W, Hᶜ.degree y + H.degree y = q - 2 := by
    intro y
    rw [SimpleGraph.degree_compl, hcard]
    have hdegree : H.degree y ≤ q - 2 := by
      have := H.degree_lt_card_verts y
      omega
    omega
  have hsum : (∑ y : W, Hᶜ.degree y) + 2 * H.edgeFinset.card =
      (q - 1) * (q - 2) := by
    rw [← H.sum_degrees_eq_twice_card_edges, ← Finset.sum_add_distrib]
    calc
      (∑ y : W, (Hᶜ.degree y + H.degree y)) = ∑ _y : W, (q - 2) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hpoint y
      _ = (q - 1) * (q - 2) := by simp [hcard]
  omega

/-- In the connected dyadic branch, one defect neighborhood contains a
vertex with at least two local nonneighbors. -/
theorem connected_binarySquare_dyadic_exists_neighborhood_fork
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ (x : V) (y : (secondOrderDefectGraph G).neighborSet x),
      2 ≤ (((secondOrderDefectGraph G).induce
        ((secondOrderDefectGraph G).neighborSet x))ᶜ).degree y := by
  let D := secondOrderDefectGraph G
  obtain ⟨x, hx⟩ :=
    connected_binarySquare_dyadic_exists_neighborhood_missingPair_slots
      G hfree hq hqpow hreg hcard hDconn
  have hDreg : ∀ v, D.degree v = q - 1 := by
    intro v
    have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
      rw [hcard]
      calc
        q * q = q * ((q - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
        _ = q * (q - 1) + q := by ring
        _ = q * (q - 1) + 3 + (q - 3) := by omega
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus v
    change D.degree v = (q - 3) + 2 at h
    omega
  have hNcard : Fintype.card (D.neighborSet x) = q - 1 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ D.neighborSet x) =
        D.neighborFinset x := by ext z; simp
    rw [heq, D.card_neighborFinset_eq_degree, hDreg x]
  obtain ⟨y, hy⟩ := exists_compl_degree_two_of_missingPair_slots
    (D.induce (D.neighborSet x)) hq hNcard hx
  exact ⟨x, y, hy⟩

end

end Erdos85

#print axioms Erdos85.exists_compl_degree_two_of_missingPair_slots
#print axioms Erdos85.connected_binarySquare_dyadic_exists_neighborhood_fork
