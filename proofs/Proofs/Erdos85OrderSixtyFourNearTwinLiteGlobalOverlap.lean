import Proofs.Erdos85SevenRegularNearTwinLiteOwnerOverlapBound
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Global all-owner overlap bound for order-64 codegree-five pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component order-64 branch, an ambient defect pair of matrix
codegree five has owner/defect overlap-row imbalance at most two, uniformly in
the owner color and the test vertex. -/
theorem orderSixtyFour_fourComponents_global_codegreeFive_allOwner_overlap_le_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {x y : Fin 64}
    (hcode : ((secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) x y = 5) :
    ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ z : Fin 64,
        |(((componentOwnerGraph G
              (secondOrderDefectGraph G) c).neighborFinset x ∩
            (secondOrderDefectGraph G).neighborFinset z).card : ℤ) -
          (((componentOwnerGraph G
              (secondOrderDefectGraph G) c).neighborFinset y ∩
            (secondOrderDefectGraph G).neighborFinset z).card : ℤ)| ≤ 2 := by
  classical
  have hcommon : ((secondOrderDefectGraph G).neighborFinset x ∩
      (secondOrderDefectGraph G).neighborFinset y).card = 5 := by
    have h := adjMatrix_sq_apply_eq_card_common
      (secondOrderDefectGraph G) x y
    rw [h] at hcode
    exact_mod_cast hcode
  intro c z
  have hc := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount c
  exact orderSixtyFour_codegreeFive_ownerGraph_overlapDifference_le_two
    G hfree hreg c hc hcommon z

end

end Erdos85
