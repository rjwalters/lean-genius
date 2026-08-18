import Proofs.Erdos85RestrictedOwnerCommutesInducedDefect
import Proofs.Erdos85SevenRegularNearTwinOwnerCollisionPropagation
import Proofs.Erdos85BinarySquareCenteredComponentLaplacian

/-! # Restricted owner collisions propagate along defect near twins -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A repeated-fork row collision in a restricted owner factor propagates to
the private pair of an induced-defect near twin, staying inside the same
sixteen-vertex component. -/
theorem orderSixtyFour_restrictedOwner_nearTwin_rowCollision_propagates
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = 16)
    {x y : source.supp}
    (hcommon :
      ((((secondOrderDefectGraph G).induce source.supp).neighborFinset x) ∩
        (((secondOrderDefectGraph G).induce source.supp).neighborFinset y)).card = 6)
    (hxyRows : ∀ w : source.supp,
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ x w =
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ y w) :
    ∃ p q : source.supp, p ≠ q ∧ ∀ z : source.supp,
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ p z =
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ q z := by
  let D := (secondOrderDefectGraph G).induce source.supp
  let O := restrictedComponentOwnerGraph G source owner
  have hDreg : ∀ z : source.supp, D.degree z = 7 := by
    intro z
    simpa [D] using binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) source z
  have hcommOD : O.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * O.adjMatrix ℤ := by
    exact orderSixtyFour_restrictedOwner_adjMatrix_comm_inducedDefect
      G hfree hreg source owner howner
  exact sevenRegular_nearTwin_commutingGraph_rowCollision_propagates
    D O hDreg hcommon hcommOD.symm hxyRows

end

end Erdos85
