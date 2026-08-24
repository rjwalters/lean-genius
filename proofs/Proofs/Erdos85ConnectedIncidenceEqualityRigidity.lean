import Proofs.Erdos85ConnectedIncidenceBottleneckCubicCapstone
import Proofs.Erdos85IncidenceEqualityGraphCapstone

/-!
# Equality rigidity for the connected incidence bottleneck

In the connected binary-square branch every closed defect star has cut at
least `q`.  Therefore equality in the global cubic Frobenius bound forces
equality in every row.  The pointwise equality classifier then restricts
the triangle-free-edge degree at every vertex to zero or two.
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- Equality in the connected cubic incidence-bottleneck bound forces every
closed defect neighborhood to have cut exactly `q`. -/
theorem connected_binarySquare_incidenceBottleneck_eq_cube_imp_closedCut_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqEven : Even q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected)
    (henergy :
      let A := G.adjMatrix ℤ
      let D := (secondOrderDefectGraph G).adjMatrix ℤ
      let J := Matrix.of (fun _ _ : V => (1 : ℤ))
      let E := A * D - (J - A)
      ∑ x : V, ∑ y : V, (E x y) ^ 2 = ((q * q * q : ℕ) : ℤ))
    (x : V) :
    finsetGraphCutSize (secondOrderDefectGraph G)
      (insert x ((secondOrderDefectGraph G).neighborFinset x)) = q := by
  let D := secondOrderDefectGraph G
  let cut := fun x : V =>
    finsetGraphCutSize D (insert x (D.neighborFinset x))
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ v, D.degree v = q - 1 := by
    intro v
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus v
    change D.degree v = (q - 3) + 2 at h
    omega
  have hcutPred : ∀ v, q - 1 ≤ cut v := by
    intro v
    obtain ⟨u, hu, w, hwv, hwnot, huw⟩ :=
      connected_regular_squareOrder_exists_closedNeighborhood_escape
        D hDconn (by omega : 2 ≤ q) hDreg hcard v
    let S : Finset V := insert v (D.neighborFinset v)
    have huS : u ∈ S := by
      rcases hu with rfl | hvu
      · simp [S]
      · simp [S, SimpleGraph.mem_neighborFinset, hvu]
    have hwS : w ∉ S := by
      simp [S, hwv, SimpleGraph.mem_neighborFinset, hwnot]
    have hwCut : w ∈ D.neighborFinset u \ S := by
      exact Finset.mem_sdiff.mpr
        ⟨(SimpleGraph.mem_neighborFinset D u w).mpr huw, hwS⟩
    have hcutPos : 0 < finsetGraphCutSize D S := by
      unfold finsetGraphCutSize
      apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      exact ⟨u, huS, Finset.card_pos.mpr ⟨w, hwCut⟩⟩
    simpa [cut, S, D] using binarySquare_regular_pred_le_defectCut_of_pos
      G hfree hq hreg hcard S (by simpa [D] using hcutPos)
  have hcutLower : ∀ v, q ≤ cut v := by
    intro v
    have h := q_le_closedNeighborhood_cut_of_even_of_pred_le
      D (by omega : 1 ≤ q) hqEven hDreg
      (by simpa [cut, finsetGraphCutIncidenceCount,
        finsetGraphCutSize] using hcutPred) v
    simpa [cut, finsetGraphCutIncidenceCount,
      finsetGraphCutSize] using h
  have hsumCutZ : (∑ v : V, (cut v : ℤ)) = ((q * q * q : ℕ) : ℤ) := by
    have hrows :
        (∑ v : V, ∑ y : V,
          ((G.adjMatrix ℤ).mulVec
            (finsetIntIndicator (insert v (D.neighborFinset v))) y - 1) ^ 2) =
          ∑ v : V, (cut v : ℤ) := by
      apply Finset.sum_congr rfl
      intro v _hv
      simpa [D, cut, finsetGraphCutIncidenceCount, finsetGraphCutSize] using
        (binarySquare_regular_closedDefectNeighborhood_incidenceError_energy
          G hfree (by omega : 1 ≤ q) hreg hcard hDreg v)
    have hrepr :=
      sum_closedNeighborhood_incidenceError_sq_eq_incidenceBottleneck_sq G D
    dsimp only at hrepr
    rw [hrows] at hrepr
    dsimp only at henergy
    rw [← hrepr] at henergy
    exact henergy
  have hsumCut : ∑ v : V, cut v = q * q * q := by
    exact_mod_cast hsumCutZ
  have hsumConst : ∑ _v : V, q = q * q * q := by
    simp [hcard]
  have hall : ∀ v ∈ (Finset.univ : Finset V), q = cut v := by
    apply (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset V))
      (f := fun _v : V => q) (g := cut)
      (fun v _hv => hcutLower v)).mp
    rw [hsumConst, hsumCut]
  simpa [D, cut] using (hall x (Finset.mem_univ x)).symm

set_option maxHeartbeats 1000000 in
/-- Global equality in the connected cubic bottleneck makes the entire
triangle-free-edge graph locally zero-or-two regular. -/
theorem connected_binarySquare_incidenceBottleneck_eq_cube_imp_triangleFreeDegree_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 8 ≤ q)
    (hqEven : Even q) (hfour : 4 ∣ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected)
    (henergy :
      let A := G.adjMatrix ℤ
      let D := (secondOrderDefectGraph G).adjMatrix ℤ
      let J := Matrix.of (fun _ _ : V => (1 : ℤ))
      let E := A * D - (J - A)
      ∑ x : V, ∑ y : V, (E x y) ^ 2 = ((q * q * q : ℕ) : ℤ))
    (x : V) :
    (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 := by
  have hcut :=
    connected_binarySquare_incidenceBottleneck_eq_cube_imp_closedCut_eq
      G hfree (by omega : 3 ≤ q) hqEven hreg hcard hDconn henergy x
  exact
    binarySquare_closedDefectNeighborhood_cut_eq_degree_imp_triangleFreeDegree_zero_or_two
      G hfree hq hqEven hfour hreg hcard x hcut

end

end Erdos85

#print axioms Erdos85.connected_binarySquare_incidenceBottleneck_eq_cube_imp_closedCut_eq
#print axioms Erdos85.connected_binarySquare_incidenceBottleneck_eq_cube_imp_triangleFreeDegree_zero_or_two
