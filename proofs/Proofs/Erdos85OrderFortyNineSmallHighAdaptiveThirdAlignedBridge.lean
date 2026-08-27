import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveThirdGraphConsumer
import Proofs.Erdos85OrderFortyNineThreeHighScoutGraphBridge

/-! # Aligned-labeling bridge for the adaptive third split -/

namespace Erdos85

open SimpleGraph

set_option maxRecDepth 10000 in
theorem orderFortyNineThreeHighB1AdaptiveFixedEdges_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E) :
    let H := orderFortyNineRelabeledGraph G E
    ∀ i j,
      orderFortyNineThreeHighB1AdaptiveFixedEdge i j = true → H.Adj i j := by
  dsimp only
  rcases haligned with ⟨hlabel, h0, h1, h2⟩
  rcases hlabel with ⟨_, _, hsupport, _⟩
  let H := orderFortyNineRelabeledGraph G E
  have supportEdge (i : Fin 49) (w : Fin 9) (hw : w.val < 3)
      (hbit : (orderFortyNineSupportMask
        orderFortyNineThreeHighDistOneNoCoincidenceMasks i).getLsbD w.val = true) :
      H.Adj i ⟨w.val, by omega⟩ := by
    have h := hsupport i w hw
    rw [hbit] at h
    exact of_decide_eq_true h
  have h03 : H.Adj 0 3 := (H.adj_comm _ _).2 (supportEdge 3 0 (by omega) (by decide))
  have h04 : H.Adj 0 4 := (H.adj_comm _ _).2 (supportEdge 4 0 (by omega) (by decide))
  have h24 : H.Adj 2 4 := (H.adj_comm _ _).2 (supportEdge 4 2 (by omega) (by decide))
  have h25 : H.Adj 2 5 := (H.adj_comm _ _).2 (supportEdge 5 2 (by omega) (by decide))
  have h218 : H.Adj 2 18 := (H.adj_comm _ _).2 (supportEdge 18 2 (by omega) (by decide))
  have h219 : H.Adj 2 19 := (H.adj_comm _ _).2 (supportEdge 19 2 (by omega) (by decide))
  have h220 : H.Adj 2 20 := (H.adj_comm _ _).2 (supportEdge 20 2 (by omega) (by decide))
  have h34 : H.Adj 3 4 := (h0 (3, 4) (by native_decide)).2 (by native_decide)
  have h312 : H.Adj 3 12 := (h1 (3, 12) (by native_decide)).2 (by native_decide)
  have h418 : H.Adj 4 18 := (h2 (4, 18) (by native_decide)).2 (by native_decide)
  have h513 : H.Adj 5 13 := (h1 (5, 13) (by native_decide)).2 (by native_decide)
  have h519 : H.Adj 5 19 := (h2 (5, 19) (by native_decide)).2 (by native_decide)
  intro i j hij
  unfold orderFortyNineThreeHighB1AdaptiveFixedEdge at hij
  simp at hij
  rcases hij with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
    first | assumption | exact (H.adj_comm _ _).2 (by assumption)

/-- Fully graph-facing third-level pruning: an aligned `b1` graph realizing
the two selected adaptive edges must be one of the sixteen residual cubes. -/
theorem orderFortyNineThreeHighB1AdaptiveResidual_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (li ri : Fin 8)
    (hleft : (orderFortyNineRelabeledGraph G E).Adj 18
      (orderFortyNineThreeHighB1AdaptiveCandidates li))
    (hright : (orderFortyNineRelabeledGraph G E).Adj 20
      (orderFortyNineThreeHighB1AdaptiveCandidates ri)) :
    orderFortyNineThreeHighB1AdaptiveResidual li ri = true := by
  apply orderFortyNineThreeHighB1AdaptiveResidual_of_graph
    (orderFortyNineRelabeledGraph G E)
    (orderFortyNineRelabeledGraph_not_containsC4 G E hfree) li ri
  · exact orderFortyNineThreeHighB1AdaptiveFixedEdges_of_aligned G E haligned
  · exact hleft
  · exact hright

end Erdos85
