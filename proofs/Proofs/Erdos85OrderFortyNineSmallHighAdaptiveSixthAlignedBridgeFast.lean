import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthGraphConsumerFast
import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFifthAlignedBridge

/-! # Aligned-labeling bridge for the adaptive sixth split -/

namespace Erdos85

open SimpleGraph

/-- The high-`2` support fiber is exactly the range of the eight sixth
candidate indices. -/
theorem orderFortyNineThreeHighB1AdaptiveHighTwoCandidates_surjective
    (x : Fin 49)
    (hx : x ∈ orderFortyNineSupportFiber
      orderFortyNineThreeHighDistOneNoCoincidenceMasks (2 : Fin 9)) :
    ∃ i : Fin 8,
      orderFortyNineThreeHighB1AdaptiveHighTwoCandidates i = x := by
  have hsurj : ∀ y : Fin 49,
      y ∈ orderFortyNineSupportFiber
          orderFortyNineThreeHighDistOneNoCoincidenceMasks (2 : Fin 9) →
        ∃ i : Fin 8,
          orderFortyNineThreeHighB1AdaptiveHighTwoCandidates i = y := by
    native_decide
  exact hsurj x hx

/-- Every late low vertex in an aligned graph has a neighbor represented by
one of the eight high-`2` sixth candidates. -/
theorem orderFortyNineThreeHighB1AdaptiveHighTwoSelector_exists_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (v : Fin 49) (hv : 3 < v.val) :
    ∃ i : Fin 8, (orderFortyNineRelabeledGraph G E).Adj v
      (orderFortyNineThreeHighB1AdaptiveHighTwoCandidates i) := by
  have haligned' := haligned
  rcases haligned' with ⟨hlabel, _, _, _⟩
  rcases hlabel with ⟨_, _, _, hpartition⟩
  let H := orderFortyNineRelabeledGraph G E
  have hcard := hpartition v (by omega) (2 : Fin 9) (by omega)
  have hpos : 0 <
      (H.neighborFinset v ∩ orderFortyNineSupportFiber
        orderFortyNineThreeHighDistOneNoCoincidenceMasks (2 : Fin 9)).card := by
    change 0 <
      ((orderFortyNineRelabeledGraph G E).neighborFinset v ∩
        orderFortyNineSupportFiber
          orderFortyNineThreeHighDistOneNoCoincidenceMasks (2 : Fin 9)).card
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxparts := Finset.mem_inter.mp hx
  obtain ⟨i, rfl⟩ :=
    orderFortyNineThreeHighB1AdaptiveHighTwoCandidates_surjective x hxparts.2
  exact ⟨i, by simpa [H, SimpleGraph.mem_neighborFinset] using hxparts.1⟩

/-- Chosen high-`2` selectors at vertices `24` and `25` of a live fifth
aligned graph land in the exact sixth residue. -/
theorem orderFortyNineThreeHighB1AdaptiveSixthResidual_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (h324 : (orderFortyNineRelabeledGraph G E).Adj 3 24)
    (h325 : (orderFortyNineRelabeledGraph G E).Adj 3 25)
    (li ri ai bi ci di ei : Fin 8)
    (h18 : (orderFortyNineRelabeledGraph G E).Adj 18
      (orderFortyNineThreeHighB1AdaptiveCandidates li))
    (h20 : (orderFortyNineRelabeledGraph G E).Adj 20
      (orderFortyNineThreeHighB1AdaptiveCandidates ri))
    (h21 : (orderFortyNineRelabeledGraph G E).Adj 21
      (orderFortyNineThreeHighB1AdaptiveCandidates ai))
    (h22 : (orderFortyNineRelabeledGraph G E).Adj 22
      (orderFortyNineThreeHighB1AdaptiveCandidates bi))
    (h23 : (orderFortyNineRelabeledGraph G E).Adj 23
      (orderFortyNineThreeHighB1AdaptiveCandidates ci))
    (h24 : (orderFortyNineRelabeledGraph G E).Adj 24
      (orderFortyNineThreeHighB1AdaptiveHighTwoCandidates di))
    (h25 : (orderFortyNineRelabeledGraph G E).Adj 25
      (orderFortyNineThreeHighB1AdaptiveHighTwoCandidates ei)) :
    orderFortyNineThreeHighB1AdaptiveSixthResidual
      li ri ai bi ci di ei = true := by
  let H := orderFortyNineRelabeledGraph G E
  have hfifth := orderFortyNineThreeHighB1AdaptiveFifthResidual_of_aligned
    G hfree E haligned h324 h325 li ri ai bi ci h18 h20 h21 h22 h23
  apply orderFortyNineThreeHighB1AdaptiveSixthFastResidual_of_graph H
    (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
    li ri ai bi ci di ei hfifth
  intro i j hij
  simp only [orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hij
  rcases hij with (hfifthEdge | h | h) | h | h
  · simp only [orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfifthEdge
    rcases hfifthEdge with hfourthEdge | h | h
    · simp only [orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfourthEdge
      have hfixed := orderFortyNineThreeHighB1AdaptiveFourthFixedEdges_of_aligned
        G E haligned h324 h325
      rcases hfourthEdge with ((((h | h | h) | h | h) | h | h) | h | h)
      all_goals first
        | exact hfixed i j h
        | rcases h with ⟨rfl, rfl⟩ <;> assumption
        | rcases h with ⟨rfl, rfl⟩ <;>
            exact (H.adj_comm _ _).mp (by assumption)
    · rcases h with ⟨rfl, rfl⟩
      exact h23
    · rcases h with ⟨rfl, rfl⟩
      exact (H.adj_comm _ _).mp h23
  · rcases h with ⟨rfl, rfl⟩
    exact h24
  · rcases h with ⟨rfl, rfl⟩
    exact (H.adj_comm _ _).mp h24
  · rcases h with ⟨rfl, rfl⟩
    exact h25
  · rcases h with ⟨rfl, rfl⟩
    exact (H.adj_comm _ _).mp h25

/-- Every aligned live fifth cell has a sixth residual child pair. -/
theorem orderFortyNineThreeHighB1AdaptiveSixthResidual_exists_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (h324 : (orderFortyNineRelabeledGraph G E).Adj 3 24)
    (h325 : (orderFortyNineRelabeledGraph G E).Adj 3 25)
    (li ri ai bi ci : Fin 8)
    (h18 : (orderFortyNineRelabeledGraph G E).Adj 18
      (orderFortyNineThreeHighB1AdaptiveCandidates li))
    (h20 : (orderFortyNineRelabeledGraph G E).Adj 20
      (orderFortyNineThreeHighB1AdaptiveCandidates ri))
    (h21 : (orderFortyNineRelabeledGraph G E).Adj 21
      (orderFortyNineThreeHighB1AdaptiveCandidates ai))
    (h22 : (orderFortyNineRelabeledGraph G E).Adj 22
      (orderFortyNineThreeHighB1AdaptiveCandidates bi))
    (h23 : (orderFortyNineRelabeledGraph G E).Adj 23
      (orderFortyNineThreeHighB1AdaptiveCandidates ci)) :
    ∃ di ei : Fin 8,
      orderFortyNineThreeHighB1AdaptiveSixthResidual
        li ri ai bi ci di ei = true := by
  obtain ⟨di, h24⟩ :=
    orderFortyNineThreeHighB1AdaptiveHighTwoSelector_exists_of_aligned
      G E haligned 24 (by omega)
  obtain ⟨ei, h25⟩ :=
    orderFortyNineThreeHighB1AdaptiveHighTwoSelector_exists_of_aligned
      G E haligned 25 (by omega)
  exact ⟨di, ei, orderFortyNineThreeHighB1AdaptiveSixthResidual_of_aligned
    G hfree E haligned h324 h325 li ri ai bi ci di ei
      h18 h20 h21 h22 h23 h24 h25⟩

end Erdos85
