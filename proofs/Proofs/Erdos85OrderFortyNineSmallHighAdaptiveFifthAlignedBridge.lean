import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFifthGraphConsumer
import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFourthAlignedBridge

/-! # Aligned-labeling bridge for the adaptive fifth split -/

namespace Erdos85

open SimpleGraph

/-- The high-`1` support fiber is exactly the range of the eight adaptive
candidate indices. -/
theorem orderFortyNineThreeHighB1AdaptiveCandidates_surjective_on_highOneFiber
    (x : Fin 49)
    (hx : x ∈ orderFortyNineSupportFiber
      orderFortyNineThreeHighDistOneNoCoincidenceMasks (1 : Fin 9)) :
    ∃ ci : Fin 8, orderFortyNineThreeHighB1AdaptiveCandidates ci = x := by
  have hsurj : ∀ y : Fin 49,
      y ∈ orderFortyNineSupportFiber
          orderFortyNineThreeHighDistOneNoCoincidenceMasks (1 : Fin 9) →
        ∃ ci : Fin 8, orderFortyNineThreeHighB1AdaptiveCandidates ci = y := by
    native_decide
  exact hsurj x hx

/-- Partition exhaustiveness at vertex `23`: an aligned B1 graph realizes at
least one of the eight fifth selector edges. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthSelector_exists_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E) :
    ∃ ci : Fin 8, (orderFortyNineRelabeledGraph G E).Adj 23
      (orderFortyNineThreeHighB1AdaptiveCandidates ci) := by
  have haligned' := haligned
  rcases haligned' with ⟨hlabel, _, _, _⟩
  rcases hlabel with ⟨_, _, _, hpartition⟩
  let H := orderFortyNineRelabeledGraph G E
  have hcard := hpartition (23 : Fin 49) (by omega) (1 : Fin 9) (by omega)
  have hpos : 0 <
      (H.neighborFinset 23 ∩ orderFortyNineSupportFiber
        orderFortyNineThreeHighDistOneNoCoincidenceMasks (1 : Fin 9)).card := by
    change 0 <
      ((orderFortyNineRelabeledGraph G E).neighborFinset 23 ∩
        orderFortyNineSupportFiber
          orderFortyNineThreeHighDistOneNoCoincidenceMasks (1 : Fin 9)).card
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxparts := Finset.mem_inter.mp hx
  obtain ⟨ci, rfl⟩ :=
    orderFortyNineThreeHighB1AdaptiveCandidates_surjective_on_highOneFiber
      x hxparts.2
  exact ⟨ci, by simpa [H, SimpleGraph.mem_neighborFinset] using hxparts.1⟩

/-- A chosen fifth selector in an aligned live fourth parent lands in the
exact sixty-four-cell fifth residue. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthResidual_of_aligned
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
    orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci = true := by
  let H := orderFortyNineRelabeledGraph G E
  have hfourth := orderFortyNineThreeHighB1AdaptiveFourthResidual_of_aligned
    G hfree E haligned li ri ai bi h324 h325 h18 h20 h21 h22
  apply orderFortyNineThreeHighB1AdaptiveFifthResidual_of_graph H
    (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
    li ri ai bi ci hfourth
  intro i j hij
  simp only [orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hij
  rcases hij with hfourthEdge | h | h
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

/-- Every aligned live fourth parent has a fifth residual child.  Combined
with the zero-or-one census, this rules out the sixteen zero-child parents
without any SAT cover certificate. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthResidual_exists_of_aligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49))
    (haligned : ThreeHighDistOneB1ScoutAlignedLabeling G E)
    (h324 : (orderFortyNineRelabeledGraph G E).Adj 3 24)
    (h325 : (orderFortyNineRelabeledGraph G E).Adj 3 25)
    (li ri ai bi : Fin 8)
    (h18 : (orderFortyNineRelabeledGraph G E).Adj 18
      (orderFortyNineThreeHighB1AdaptiveCandidates li))
    (h20 : (orderFortyNineRelabeledGraph G E).Adj 20
      (orderFortyNineThreeHighB1AdaptiveCandidates ri))
    (h21 : (orderFortyNineRelabeledGraph G E).Adj 21
      (orderFortyNineThreeHighB1AdaptiveCandidates ai))
    (h22 : (orderFortyNineRelabeledGraph G E).Adj 22
      (orderFortyNineThreeHighB1AdaptiveCandidates bi)) :
    ∃ ci : Fin 8,
      orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci = true := by
  obtain ⟨ci, h23⟩ :=
    orderFortyNineThreeHighB1AdaptiveFifthSelector_exists_of_aligned G E haligned
  exact ⟨ci, orderFortyNineThreeHighB1AdaptiveFifthResidual_of_aligned
    G hfree E haligned h324 h325 li ri ai bi ci h18 h20 h21 h22 h23⟩

end Erdos85
