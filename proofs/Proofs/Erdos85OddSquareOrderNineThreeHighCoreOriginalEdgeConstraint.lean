import Proofs.Erdos85DefectPathOwner
import Proofs.Erdos85OddSquareOrderNineThreeHighBinOneDefectTypes

/-! # Original-edge constraint on the q = 9 three-high ordinary core

Node: B.3 / GAP B-CLASSIFY.  A non-rainbow vertex of the properly
three-colored ordinary defect core has two neighbors of one high color.  Their
shared high root is the exact common-neighbor owner, so the two incident
defect edges cannot both be original edges.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Along a defect two-path through a low bin-one vertex, if the two distinct
endpoints share a high neighbor, at least one path edge is absent from the
original graph. -/
theorem squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y z r : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hrH : r ∈ squareOrderHighVertices G 9)
    (hDxy : (secondOrderDefectGraph G).Adj x y)
    (hDyz : (secondOrderDefectGraph G).Adj y z)
    (hxz : x ≠ z)
    (hrx : G.Adj r x) (hrz : G.Adj r z) :
    ¬ (G.Adj x y ∧ G.Adj y z) := by
  have hyLow : y ∈ (Finset.univ : Finset V) \ squareOrderHighVertices G 9 :=
    (Finset.mem_filter.mp hy).1
  have hyr : y ≠ r := by
    intro hyr
    subst y
    exact (Finset.mem_sdiff.mp hyLow).2 hrH
  have hnotDxz : ¬ (secondOrderDefectGraph G).Adj x z :=
    not_secondOrderDefect_adj_of_commonNeighbor
      G hfree hxz hrx.symm hrz.symm
  exact not_both_originalEdges_of_induced_secondOrderDefect_path_of_commonOwner
    G hfree hDxy hDyz hxz hnotDxz hrx hrz hyr

end

end Erdos85

#print axioms Erdos85.squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
