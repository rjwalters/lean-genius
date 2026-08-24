import Proofs.Erdos85ConnectedDefectLocalTriangleDeficit

/-!
# Missing pairs in a connected defect neighborhood

The strict local triangle deficit means that, at one vertex, the induced
defect neighborhood misses at least `q+2` ordered edge slots relative to the
complete graph on its `q-1` vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic form: the local edge deficit leaves `q+2` doubled missing
pair slots below the complete graph on `q-1` vertices. -/
theorem add_two_add_two_mul_edges_le_pred_mul_sub_two
    (q e : ℕ) (hq : 3 ≤ q)
    (hdeficit : 2 * e + 4 * q ≤ q * q) :
    q + 2 + 2 * e ≤ (q - 1) * (q - 2) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = r + 3 := ⟨q - 3, by omega⟩
  norm_num at hdeficit ⊢
  have hsub : r + 3 - 2 = r + 1 := by omega
  rw [hsub]
  nlinarith

/-- Uniform dyadic connected-branch witness with `q+2` doubled missing
neighbor-pair slots. -/
theorem connected_binarySquare_dyadic_exists_neighborhood_missingPair_slots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    ∃ x : V, q + 2 + 2 * ((secondOrderDefectGraph G).induce
      ((secondOrderDefectGraph G).neighborSet x)).edgeFinset.card ≤
        (q - 1) * (q - 2) := by
  obtain ⟨x, hx⟩ := connected_binarySquare_dyadic_exists_localEdges_deficit
    G hfree hq hqpow hreg hcard hDconn
  exact ⟨x, add_two_add_two_mul_edges_le_pred_mul_sub_two q _ hq hx⟩

end

end Erdos85

#print axioms Erdos85.add_two_add_two_mul_edges_le_pred_mul_sub_two
#print axioms Erdos85.connected_binarySquare_dyadic_exists_neighborhood_missingPair_slots
