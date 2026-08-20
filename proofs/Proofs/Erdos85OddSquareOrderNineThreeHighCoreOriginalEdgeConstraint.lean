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

/-- More generally, among any collection of defect neighbors of a bin-one
center that all have one fixed high color, at most one is joined to the
center by an original edge.  Thus original edges form a matching across every
monochromatic fan in the ordinary defect core. -/
theorem squareOrderNine_binOne_sameHigh_defectNeighbors_original_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {y r : V}
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hrH : r ∈ squareOrderHighVertices G 9)
    (S : Finset V)
    (hSdefect : S ⊆ (secondOrderDefectGraph G).neighborFinset y)
    (hScolor : ∀ x ∈ S, G.Adj r x) :
    (S ∩ G.neighborFinset y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx z hz
  have hxS := (Finset.mem_inter.mp hx).1
  have hzS := (Finset.mem_inter.mp hz).1
  by_contra hxz
  have hDxy : (secondOrderDefectGraph G).Adj x y :=
    ((secondOrderDefectGraph G).mem_neighborFinset y x).mp
      (hSdefect hxS) |>.symm
  have hDyz : (secondOrderDefectGraph G).Adj y z :=
    ((secondOrderDefectGraph G).mem_neighborFinset y z).mp (hSdefect hzS)
  have hnot := squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
    G hfree hy hrH hDxy hDyz hxz (hScolor x hxS) (hScolor z hzS)
  exact hnot ⟨
    ((G.mem_neighborFinset y x).mp (Finset.mem_inter.mp hx).2).symm,
    (G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hz).2⟩

end

end Erdos85

#print axioms Erdos85.squareOrderNine_binOne_not_both_originalEdges_of_sameHigh_twoPath
#print axioms Erdos85.squareOrderNine_binOne_sameHigh_defectNeighbors_original_card_le_one
