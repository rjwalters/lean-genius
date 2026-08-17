import Proofs.Erdos85OrderSixtyFourResidualLaplacianProduct

/-! # Square residual determinant of the sixteen-vertex defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- In the seven-component order-64 branch, the unique sixteen-vertex
defect component has square residual Laplacian determinant over `ℚ`. -/
theorem orderSixtyFour_seven_components_sixteenBlock_residual_det_isSquare
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Fintype c.supp]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∃ (hC : ∀ v ∈ LinearMap.ker (coordinateSumLinearMap c.supp),
          (sevenRegularLaplacianMatrix
            ((secondOrderDefectGraph G).induce c.supp)).toLin' v ∈
              LinearMap.ker (coordinateSumLinearMap c.supp)),
        IsSquare
          (LinearMap.det
            ((sevenRegularLaplacianMatrix
              ((secondOrderDefectGraph G).induce c.supp)).toLin'.restrict
                hC)) := by
  let hdec := ‹DecidableEq
    (secondOrderDefectGraph G).ConnectedComponent›
  classical
  letI : DecidableEq
      (secondOrderDefectGraph G).ConnectedComponent := hdec
  let D := secondOrderDefectGraph G
  have hDreg : ∀ x : Fin 64, D.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  obtain ⟨c, hc16, hsmallSize⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  obtain ⟨hA, hL, hdetSq⟩ :=
    orderSixtyFour_residual_laplacian_det_eq_adjacency_det_sq
      G hfree hmin hcover
  have hstable : sevenRegularLaplacianMatrix D = D.lapMatrix ℚ :=
    sevenRegularLaplacianMatrix_eq_lapMatrix D hDreg
  have hW : ∀ v ∈ LinearMap.ker
      (defectComponentNormalizedProjection D).toLin',
      (sevenRegularLaplacianMatrix D).toLin' v ∈
        LinearMap.ker (defectComponentNormalizedProjection D).toLin' := by
    simpa only [hstable] using hL
  let hC (e : D.ConnectedComponent) :=
    sevenRegularComponentLaplacian_maps_meanZero D hDreg e
  let f (e : D.ConnectedComponent) : ℚ :=
    LinearMap.det
      ((sevenRegularLaplacianMatrix (D.induce e.supp)).toLin'.restrict
        (hC e))
  have hprod :
      LinearMap.det
          ((sevenRegularLaplacianMatrix D).toLin'.restrict hW) =
        ∏ e : D.ConnectedComponent, f e := by
    exact det_sevenRegularLaplacian_restrict_eq_prod_components
      D hW hC
  have hglobalSq : IsSquare
      (LinearMap.det
        ((sevenRegularLaplacianMatrix D).toLin'.restrict hW)) := by
    refine ⟨LinearMap.det ((G.adjMatrix ℚ).toLin'.restrict hA), ?_⟩
    have hend :
        (sevenRegularLaplacianMatrix D).toLin'.restrict hW =
          (D.lapMatrix ℚ).toLin'.restrict hL := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact congrArg (fun M => M.mulVec v.1) hstable
    rw [hend]
    exact hdetSq.trans (pow_two _)
  have hprodSq : IsSquare (∏ e : D.ConnectedComponent, f e) := by
    obtain ⟨a, ha⟩ := hglobalSq
    exact ⟨a, hprod.symm.trans ha⟩
  have hsmall : ∀ e, e ≠ c → f e = (8 : ℚ) ^ 7 := by
    intro e hec
    obtain ⟨hE, hdetE⟩ :=
      exists_componentResidual_det_eq_eight_pow_seven_of_order_eight
        D hDreg e (hsmallSize e hec)
    simpa only [f] using hdetE
  have hcSquare : IsSquare (f c) :=
    isSquare_distinguished_of_seven_product_and_six_eightFactors
      hcount f c hsmall hprodSq
  refine ⟨c, hc16, hC c, ?_⟩
  exact hcSquare

end

end Erdos85
