import Proofs.Erdos85DyadicStoppingSupportDefectPenalizedCherrySqueeze
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# Exact zero-common-pair interpretation of the dyadic cherry penalty

The second-order defect graph is the union of the nonedge defect relation
and the triangle-free-edge relation.  In a C4-free graph it therefore
contains exactly the distinct pairs with no common ambient neighbor.  This
file records that the penalty in the defect-penalized dyadic cherry squeeze
already removes every pair which can never be served; there is no additional
triangle-free-edge penalty to add.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Canonical two-subsets of `B` having no common ambient neighbor. -/
def zeroCommonNeighborPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    Finset (Finset V) :=
  (B.powersetCard 2).filter fun T =>
    ∀ u ∈ T, ∀ v ∈ T, u ≠ v →
      (G.neighborFinset u ∩ G.neighborFinset v).card = 0

/-- In a C4-free graph, the defect-pair penalty is exactly the full family
of two-subsets with no common neighbor.  In particular it already includes
both antipodal nonedges and triangle-free original edges. -/
theorem secondOrderDefectPairs_eq_zeroCommonNeighborPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (B : Finset V) :
    secondOrderDefectPairs G B = zeroCommonNeighborPairs G B := by
  ext T
  simp only [secondOrderDefectPairs, zeroCommonNeighborPairs,
    Finset.mem_filter]
  constructor
  · rintro ⟨hT, hD⟩
    refine ⟨hT, ?_⟩
    intro u hu v hv huv
    exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree huv).mp (hD u hu v hv huv)
  · rintro ⟨hT, hzero⟩
    refine ⟨hT, ?_⟩
    intro u hu v hv huv
    exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree huv).mpr (hzero u hu v hv huv)

/-- Audit-facing form of the strongest available pair-budget squeeze: its
subtracted term is literally the number of internal zero-common-neighbor
pairs of the stopping support. -/
theorem c4Free_dyadicStoppingSupport_twoShore_zeroCommonPair_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
        (Sᶜ : Finset V).card *
          (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 ≤
      (dyadicOccupancySupport G S j).card.choose 2 -
        (zeroCommonNeighborPairs G (dyadicOccupancySupport G S j)).card := by
  rw [← secondOrderDefectPairs_eq_zeroCommonNeighborPairs G hfree]
  exact c4Free_dyadicStoppingSupport_twoShore_defectPenalized_cherry_squeeze
    G hfree hreg S j hdiv hqdiv

end

end Erdos85

#print axioms Erdos85.secondOrderDefectPairs_eq_zeroCommonNeighborPairs
#print axioms Erdos85.c4Free_dyadicStoppingSupport_twoShore_zeroCommonPair_cherry_squeeze
