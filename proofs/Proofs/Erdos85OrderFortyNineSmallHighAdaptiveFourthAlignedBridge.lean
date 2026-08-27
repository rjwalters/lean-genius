import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveThirdAlignedBridge
import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFourthGraphConsumer

/-! # Aligned-labeling bridge for the adaptive fourth split -/

namespace Erdos85

open SimpleGraph

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem orderFortyNineThreeHighB1AdaptiveFourthFixedEdges_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (h324 : (orderFortyNineRelabeledGraph G E).Adj 3 24)
    (h325 : (orderFortyNineRelabeledGraph G E).Adj 3 25) :
    ∀ i j, orderFortyNineThreeHighB1AdaptiveFourthFixedEdge i j = true →
      (orderFortyNineRelabeledGraph G E).Adj i j := by
  rcases haligned with ⟨hlabel, h0, h1, h2⟩
  rcases hlabel with ⟨_, _, hsupport, _⟩
  let H := orderFortyNineRelabeledGraph G E
  have supportEdge (i : Fin 49) (w : Fin 9) (hw : w.val < 3)
      (hbit : (orderFortyNineSupportMask
        orderFortyNineThreeHighDistOneNoCoincidenceMasks i).getLsbD w.val = true) :
      H.Adj ⟨w.val, by omega⟩ i := by
    apply (H.adj_comm _ _).2
    have h := hsupport i w hw
    rw [hbit] at h
    exact of_decide_eq_true h
  have h03 := supportEdge 3 0 (by omega) (by decide)
  have h04 := supportEdge 4 0 (by omega) (by decide)
  have h06 := supportEdge 6 0 (by omega) (by decide)
  have h07 := supportEdge 7 0 (by omega) (by decide)
  have h08 := supportEdge 8 0 (by omega) (by decide)
  have h09 := supportEdge 9 0 (by omega) (by decide)
  have h010 := supportEdge 10 0 (by omega) (by decide)
  have h011 := supportEdge 11 0 (by omega) (by decide)
  have h13 := supportEdge 3 1 (by omega) (by decide)
  have h15 := supportEdge 5 1 (by omega) (by decide)
  have h112 := supportEdge 12 1 (by omega) (by decide)
  have h113 := supportEdge 13 1 (by omega) (by decide)
  have h114 := supportEdge 14 1 (by omega) (by decide)
  have h115 := supportEdge 15 1 (by omega) (by decide)
  have h116 := supportEdge 16 1 (by omega) (by decide)
  have h117 := supportEdge 17 1 (by omega) (by decide)
  have h24 := supportEdge 4 2 (by omega) (by decide)
  have h25 := supportEdge 5 2 (by omega) (by decide)
  have h218 := supportEdge 18 2 (by omega) (by decide)
  have h219 := supportEdge 19 2 (by omega) (by decide)
  have h220 := supportEdge 20 2 (by omega) (by decide)
  have h221 := supportEdge 21 2 (by omega) (by decide)
  have h222 := supportEdge 22 2 (by omega) (by decide)
  have h223 := supportEdge 23 2 (by omega) (by decide)
  have h34 : H.Adj 3 4 := (h0 (3, 4) (by native_decide)).2 (by native_decide)
  have h67 : H.Adj 6 7 := (h0 (6, 7) (by native_decide)).2 (by native_decide)
  have h89 : H.Adj 8 9 := (h0 (8, 9) (by native_decide)).2 (by native_decide)
  have h1011 : H.Adj 10 11 := (h0 (10, 11) (by native_decide)).2 (by native_decide)
  have h312 : H.Adj 3 12 := (h1 (3, 12) (by native_decide)).2 (by native_decide)
  have h513 : H.Adj 5 13 := (h1 (5, 13) (by native_decide)).2 (by native_decide)
  have h1415 : H.Adj 14 15 := (h1 (14, 15) (by native_decide)).2 (by native_decide)
  have h1617 : H.Adj 16 17 := (h1 (16, 17) (by native_decide)).2 (by native_decide)
  have h418 : H.Adj 4 18 := (h2 (4, 18) (by native_decide)).2 (by native_decide)
  have h519 : H.Adj 5 19 := (h2 (5, 19) (by native_decide)).2 (by native_decide)
  have h2021 : H.Adj 20 21 := (h2 (20, 21) (by native_decide)).2 (by native_decide)
  have h2223 : H.Adj 22 23 := (h2 (22, 23) (by native_decide)).2 (by native_decide)
  intro i j hij
  unfold orderFortyNineThreeHighB1AdaptiveFourthFixedEdge at hij
  simp at hij
  rcases hij with h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
    first | assumption | exact (H.adj_comm _ _).mp (by assumption)

/-- End-to-end fourth-level structural pruning for an aligned `b1` graph.
The two parent pins and four selector edges are the only facts not already
contained in the aligned-labeling package. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthResidual_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (li ri ai bi : Fin 8)
    (h324 : (orderFortyNineRelabeledGraph G E).Adj 3 24)
    (h325 : (orderFortyNineRelabeledGraph G E).Adj 3 25)
    (hleft : (orderFortyNineRelabeledGraph G E).Adj 18
      (orderFortyNineThreeHighB1AdaptiveCandidates li))
    (hright : (orderFortyNineRelabeledGraph G E).Adj 20
      (orderFortyNineThreeHighB1AdaptiveCandidates ri))
    (ha : (orderFortyNineRelabeledGraph G E).Adj 21
      (orderFortyNineThreeHighB1AdaptiveCandidates ai))
    (hb : (orderFortyNineRelabeledGraph G E).Adj 22
      (orderFortyNineThreeHighB1AdaptiveCandidates bi)) :
    orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = true := by
  let H := orderFortyNineRelabeledGraph G E
  have hthird := orderFortyNineThreeHighB1AdaptiveResidual_of_aligned
    G hfree E haligned li ri hleft hright
  apply orderFortyNineThreeHighB1AdaptiveFourthResidual_of_graph H
    (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
    li ri ai bi hthird
  intro i j hij
  simp only [orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hij
  have hfixed := orderFortyNineThreeHighB1AdaptiveFourthFixedEdges_of_aligned
    G E haligned h324 h325
  rcases hij with ((((h | h | h) | h | h) | h | h) | h | h)
  all_goals first
    | exact hfixed i j h
    | rcases h with ⟨rfl, rfl⟩ <;> assumption
    | rcases h with ⟨rfl, rfl⟩ <;>
        exact (H.adj_comm _ _).mp (by assumption)

end Erdos85
