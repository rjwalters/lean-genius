import Proofs.Erdos85GroundedDefectNonsingular
import Proofs.Erdos85OrderFortyNineThreeHighSquareCandidateBlock
import Proofs.Erdos85OrderFortyNineUngroundedDefectComponent

/-! # Groundedness implies nonsingularity of the order-49 defect block -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

def orderFortyNineOrdinaryDefectGraph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    SimpleGraph (Fin 46) :=
  (secondOrderDefectGraph G).comap orderFortyNineOrdinaryVertex

local instance orderFortyNineOrdinaryDefectGraph_decidableAdj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    DecidableRel (orderFortyNineOrdinaryDefectGraph G).Adj :=
  Classical.decRel _

def orderFortyNineOrdinaryHighIncidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (i : Fin 46) : ℚ :=
  6 - (orderFortyNineOrdinaryDefectGraph G).degree i

theorem orderFortyNineOrdinaryDefectL_eq_lapMatrix_add_diagonal
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    orderFortyNineOrdinaryDefectL G =
      (orderFortyNineOrdinaryDefectGraph G).lapMatrix ℚ +
        diagonal (orderFortyNineOrdinaryHighIncidence G) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [orderFortyNineOrdinaryDefectL, orderFortyNineOrdinaryDefectGraph,
      orderFortyNineOrdinaryHighIncidence, orderFortyNineOrdinaryVertex,
      SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix]
  · simp [orderFortyNineOrdinaryDefectL, orderFortyNineOrdinaryDefectGraph,
      orderFortyNineOrdinaryHighIncidence, orderFortyNineOrdinaryVertex,
      SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

theorem orderFortyNineOrdinaryDefectL_isUnit_of_grounded
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hdegree : ∀ i, (orderFortyNineOrdinaryDefectGraph G).degree i ≤ 6)
    (hground : ∀ i, ∃ j,
      (orderFortyNineOrdinaryDefectGraph G).Reachable i j ∧
        (orderFortyNineOrdinaryDefectGraph G).degree j < 6) :
    IsUnit (orderFortyNineOrdinaryDefectL G).det := by
  rw [orderFortyNineOrdinaryDefectL_eq_lapMatrix_add_diagonal]
  apply isUnit_det_lapMatrix_add_diagonal_of_grounded
  · intro i
    have hi : ((orderFortyNineOrdinaryDefectGraph G).degree i : ℚ) ≤ 6 := by
      exact_mod_cast hdegree i
    dsimp [orderFortyNineOrdinaryHighIncidence]
    linarith
  · intro i
    obtain ⟨j, hij, hj⟩ := hground i
    refine ⟨j, hij, ?_⟩
    have hj' : ((orderFortyNineOrdinaryDefectGraph G).degree j : ℚ) < 6 := by
      exact_mod_cast hj
    dsimp [orderFortyNineOrdinaryHighIncidence]
    linarith

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryDefectL_eq_lapMatrix_add_diagonal
#print axioms Erdos85.orderFortyNineOrdinaryDefectL_isUnit_of_grounded
