import Proofs.Erdos85DefectPairsSupportDensity

/-!
# Complement balance for internal defect pairs

The coarse support-density bound forgets edges internal to the complement.
Regularity gives an exact correction: the two internal edge counts differ by
the regular-degree charge of the two shore sizes.  For a final dyadic support,
its complement is precisely the exceptional line family, where independent
structure supplies many forced defect edges.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Internal directed incidences are twice the number of supported edges. -/
theorem sum_internal_incidence_eq_twice_supported_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (B : Finset V) :
    (∑ v ∈ B, (D.neighborFinset v ∩ B).card) =
      2 * (supportedEdgeGraph D B).edgeFinset.card := by
  classical
  calc
    (∑ v ∈ B, (D.neighborFinset v ∩ B).card) =
        ∑ v ∈ B, (supportedEdgeGraph D B).degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← (supportedEdgeGraph D B).card_neighborFinset_eq_degree]
      congr 1
      ext w
      simp [SimpleGraph.mem_neighborFinset, hv, and_comm]
    _ = ∑ v : V, (supportedEdgeGraph D B).degree v := by
      apply Finset.sum_subset (Finset.subset_univ B)
      intro v hvU hvB
      rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
      intro hvSupp
      obtain ⟨w, hvw⟩ := hvSupp
      exact hvB (supportedEdgeGraph_adj D B v w |>.mp hvw).2.1
    _ = 2 * (supportedEdgeGraph D B).edgeFinset.card :=
      (supportedEdgeGraph D B).sum_degrees_eq_twice_card_edges

/-- Exact complement balance in an `r`-regular graph. -/
theorem regular_supported_edge_complement_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {r : ℕ} (hreg : ∀ v, D.degree v = r) (B : Finset V) :
    r * B.card + 2 * (supportedEdgeGraph D (Bᶜ : Finset V)).edgeFinset.card =
      2 * (supportedEdgeGraph D B).edgeFinset.card +
        r * (Bᶜ : Finset V).card := by
  let C := (Bᶜ : Finset V)
  let iB := ∑ v ∈ B, (D.neighborFinset v ∩ B).card
  let iC := ∑ v ∈ C, (D.neighborFinset v ∩ C).card
  let xBC := ∑ v ∈ B, (D.neighborFinset v ∩ C).card
  let xCB := ∑ v ∈ C, (D.neighborFinset v ∩ B).card
  have hB := regular_shore_compl_incidence_sum D hreg B B
  have hC := regular_shore_compl_incidence_sum D hreg C C
  have hcross : xBC = xCB := by
    dsimp only [xBC, xCB]
    exact sum_card_neighbor_inter_comm D B C
  have hB' : iB + xCB = r * B.card := by
    simpa [iB, xCB, C] using hB
  have hC' : iC + xBC = r * C.card := by
    have hCC : (Cᶜ : Finset V) = B := by simp [C]
    simpa [iC, xBC, C, hCC] using hC
  have hiB := sum_internal_incidence_eq_twice_supported_edges D B
  have hiC := sum_internal_incidence_eq_twice_supported_edges D C
  change iB = 2 * (supportedEdgeGraph D B).edgeFinset.card at hiB
  change iC = 2 * (supportedEdgeGraph D C).edgeFinset.card at hiC
  dsimp only [C] at hC' hiC ⊢
  omega

/-- Exact square-order balance for the canonical defect-pair families of a
support and its complement. -/
theorem binarySquare_secondOrderDefectPairs_complement_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ}
    (hDreg : ∀ v, (secondOrderDefectGraph G).degree v = q - 1)
    (B : Finset V) :
    (q - 1) * B.card +
        2 * (secondOrderDefectPairs G (Bᶜ : Finset V)).card =
      2 * (secondOrderDefectPairs G B).card +
        (q - 1) * (Bᶜ : Finset V).card := by
  have h := regular_supported_edge_complement_balance
    (secondOrderDefectGraph G) hDreg B
  rw [supportedSecondOrder_edge_card_eq_defectPairs G B,
    supportedSecondOrder_edge_card_eq_defectPairs G (Bᶜ : Finset V)] at h
  exact h

/-- C4-free square-order specialization deriving defect regularity from the
ambient graph hypotheses. -/
theorem c4Free_binarySquare_secondOrderDefectPairs_complement_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (B : Finset V) :
    (q - 1) * B.card +
        2 * (secondOrderDefectPairs G (Bᶜ : Finset V)).card =
      2 * (secondOrderDefectPairs G B).card +
        (q - 1) * (q * q - B.card) := by
  have h := binarySquare_secondOrderDefectPairs_complement_balance G
    (binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard) B
  rwa [Finset.card_compl, hcard] at h

/-- Arithmetic elimination of the internal-pair variable while retaining
the complement's forced pair count. -/
theorem pairBudget_complementBalance_eliminate
    {cost budget r b c eB eC : ℕ}
    (heB : eB ≤ budget)
    (hcost : cost ≤ budget - eB)
    (hbalance : r * b + 2 * eC = 2 * eB + r * c) :
    2 * cost + r * b + 2 * eC ≤ 2 * budget + r * c := by
  omega

end

end Erdos85

#print axioms Erdos85.sum_internal_incidence_eq_twice_supported_edges
#print axioms Erdos85.regular_supported_edge_complement_balance
#print axioms Erdos85.binarySquare_secondOrderDefectPairs_complement_balance
#print axioms
  Erdos85.c4Free_binarySquare_secondOrderDefectPairs_complement_balance
#print axioms Erdos85.pairBudget_complementBalance_eliminate
