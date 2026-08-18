import Proofs.Erdos85OrderSixtyFourEightComponentKill
import Proofs.Erdos85PrincipalIndicatorTrace

/-! # The principal defect-sector trace at order 64 -/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- The diagonal of the component quotient sums to eight.  This holds for
every defect partition, not only the uniform eight-block branch. -/
theorem orderSixtyFour_componentQuotient_diagonal_sum_eq_eight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c) = 8 := by
  classical
  let D := secondOrderDefectGraph G
  change (∑ c : D.ConnectedComponent,
    componentQuotientMatrix G D c c) = 8
  have hentry (c : D.ConnectedComponent) :
      8 * componentQuotientMatrix G D c c = c.supp.ncard :=
    orderSixtyFour_eight_mul_componentQuotientMatrix_apply
      G hfree hmin hcover c c
  have hsizes : (∑ c : D.ConnectedComponent, c.supp.ncard) = 64 := by
    calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (Fin 64) :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
      _ = 64 := by simp
  have hmul : 8 * (∑ c : D.ConnectedComponent,
      componentQuotientMatrix G D c c) = 64 := by
    calc
      8 * (∑ c : D.ConnectedComponent,
          componentQuotientMatrix G D c c) =
          ∑ c : D.ConnectedComponent,
            8 * componentQuotientMatrix G D c c := by
        rw [Finset.mul_sum]
      _ = ∑ c : D.ConnectedComponent, c.supp.ncard := by
        exact Finset.sum_congr rfl fun c _ => hentry c
      _ = 64 := hsizes
  omega

/-- The adjacency trace on the top (`7`) eigenspace of the defect graph is
exactly eight.  Hence every complementary invariant sector must carry total
trace `-8`, since the ambient adjacency matrix has zero trace. -/
theorem orderSixtyFour_principal_defect_sector_trace_eq_eight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    LinearMap.trace ℚ _
        (kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
          (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
          (by
            simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
              congrArg Matrix.toLin'
                (adjMatrix_comm_secondOrderDefect_of_regular_rat
                  G hfree
                    (orderSixtyFour_regular_of_tightCover
                      G hfree hmin hcover)))
          (X - C (7 : ℚ))) = 8 := by
  classical
  let D := secondOrderDefectGraph G
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, D.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  have hcommR := adjMatrix_comm_secondOrderDefect_of_regular_real
    G hfree hreg
  have hcommQ := adjMatrix_comm_secondOrderDefect_of_regular_rat
    G hfree hreg
  have htrace := trace_principal_kerAevalRestrict
    G D hDreg hcommR
      (by simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
        congrArg Matrix.toLin' hcommQ)
  dsimp only [D] at htrace
  have hsum := orderSixtyFour_componentQuotient_diagonal_sum_eq_eight
    G hfree hmin hcover
  have hsumQ : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (componentQuotientMatrix G (secondOrderDefectGraph G) c c : ℚ)) = 8 := by
    exact_mod_cast hsum
  convert htrace.trans hsumQ using 1 <;> simp

end

end Erdos85
