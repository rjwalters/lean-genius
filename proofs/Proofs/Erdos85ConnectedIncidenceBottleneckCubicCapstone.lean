import Proofs.Erdos85DefectMaxEdgeConnectivity
import Proofs.Erdos85ConnectedClosedNeighborhoodEscape
import Proofs.Erdos85ConnectedIncidenceBottleneckRowRepresentation

/-!
# Connected incidence-bottleneck cubic energy

This file closes the graph-facing composition: connectedness makes every
closed defect neighborhood cut positive, maximal defect connectivity gives
the `q - 1` cut lower bound, and the exact row representation yields the
literal `q^3` Frobenius lower bound for the incidence bottleneck.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A connected regular square-order second-order defect graph forces cubic
energy in the integer incidence bottleneck. -/
theorem connected_binarySquare_regular_incidenceBottleneck_energy_ge_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqeven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (hDconn : (secondOrderDefectGraph G).Connected) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    ((q * q * q : ℕ) : ℤ) ≤ ∑ x : V, ∑ y : V, (E x y) ^ 2 := by
  let D := secondOrderDefectGraph G
  have hcut : ∀ x,
      q - 1 ≤ finsetGraphCutIncidenceCount D
        (insert x (D.neighborFinset x)) := by
    intro x
    obtain ⟨u, hu, v, hvx, hvnot, huv⟩ :=
      connected_regular_squareOrder_exists_closedNeighborhood_escape
        D hDconn (by omega : 2 ≤ q) hDreg hcard x
    let S : Finset V := insert x (D.neighborFinset x)
    have huS : u ∈ S := by
      rcases hu with rfl | hxu
      · simp [S]
      · simp [S, SimpleGraph.mem_neighborFinset, hxu]
    have hvS : v ∉ S := by
      simp [S, hvx, SimpleGraph.mem_neighborFinset, hvnot]
    have hvCut : v ∈ D.neighborFinset u \ S := by
      exact Finset.mem_sdiff.mpr
        ⟨(SimpleGraph.mem_neighborFinset D u v).mpr huv, hvS⟩
    have hcutPos : 0 < finsetGraphCutSize D S := by
      unfold finsetGraphCutSize
      apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      exact ⟨u, huS, Finset.card_pos.mpr ⟨v, hvCut⟩⟩
    have hmax := binarySquare_regular_pred_le_defectCut_of_pos
      G hfree hq hreg hcard S hcutPos
    simpa [S, finsetGraphCutIncidenceCount, finsetGraphCutSize] using hmax
  exact binarySquare_regular_incidenceBottleneck_energy_ge_cube_of_cut_pred_le
    G hfree (by omega : 1 ≤ q) hqeven hreg hcard hDreg hcut

#print axioms connected_binarySquare_regular_incidenceBottleneck_energy_ge_cube

end

end Erdos85
