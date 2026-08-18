import Proofs.Erdos85BinarySquareSizeTwoOwnerFactorization
import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85DefectComponentBlockCommute

/-! # Restricted owner factors commute with the induced defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **q-generic restricted commutation.**  Every owner-color block restricted
to a source defect component commutes with the defect graph induced on that
source.  No component-size classification is needed: this is the principal
block of the global owner/defect commutation relation. -/
theorem binarySquare_regular_restrictedOwner_adjMatrix_comm_inducedDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q m : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * m) :
    (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ =
      ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ *
        (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ := by
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D owner
  have hglobal : O.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * O.adjMatrix ℤ := by
    exact binarySquare_regular_componentOwnerGraph_adjMatrix_comm_defect
      G hfree hq hreg hcard owner howner
  have hblock := induce_component_adjMatrix_comm_of_comm O D hglobal source
  change (O.induce source.supp).adjMatrix ℤ *
      (D.induce source.supp).adjMatrix ℤ =
    (D.induce source.supp).adjMatrix ℤ *
      (O.induce source.supp).adjMatrix ℤ
  exact hblock

/-- In the order-64 all-size-sixteen branch, every restricted owner 2-factor
commutes with the induced defect graph on its source component.  This is the
block-level bridge needed to propagate repeated-fork row collisions. -/
theorem orderSixtyFour_restrictedOwner_adjMatrix_comm_inducedDefect
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = 16) :
    (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ =
      ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ *
        (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ := by
  exact binarySquare_regular_restrictedOwner_adjMatrix_comm_inducedDefect
    G hfree (q := 8) (m := 2) (by norm_num) hreg (by norm_num)
      source owner (by norm_num [howner])

end

end Erdos85
