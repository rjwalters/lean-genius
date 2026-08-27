import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthStructural

/-! # Fast graph consumer for the adaptive sixth split -/

namespace Erdos85

open SimpleGraph

private def orderFortyNineAdaptiveSixthFastVertices : List (Fin 49) :=
  (List.finRange 26).map fun i => ⟨i.val, by omega⟩

private def orderFortyNineAdaptiveSixthFastEndpointPairs :
    List (Fin 49 × Fin 49) :=
  ((List.finRange 24).map fun i => (⟨i.val, by omega⟩, 24)) ++
  ((List.finRange 25).map fun i => (⟨i.val, by omega⟩, 25))

private def orderFortyNineAdaptiveSixthFastCommon
    (li ri ai bi ci di ei : Fin 8) (i j : Fin 49) : List (Fin 49) :=
  orderFortyNineAdaptiveSixthFastVertices.filter fun w =>
    orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
      li ri ai bi ci di ei i w &&
    orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
      li ri ai bi ci di ei j w

private def orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitness
    (li ri ai bi ci di ei : Fin 8) : Option OrderFortyNineAdaptiveC4Witness :=
  match orderFortyNineAdaptiveSixthFastEndpointPairs.find? fun ij =>
      2 ≤ (orderFortyNineAdaptiveSixthFastCommon
        li ri ai bi ci di ei ij.1 ij.2).length with
  | none => none
  | some (i, j) =>
      match orderFortyNineAdaptiveSixthFastCommon
        li ri ai bi ci di ei i j with
      | w :: w' :: _ => some (i, j, w, w')
      | _ => none

private def orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitnessValid
    (li ri ai bi ci di ei : Fin 8) : Bool :=
  match orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitness
      li ri ai bi ci di ei with
  | none => false
  | some (i, j, w, w') =>
      i ≠ j && w ≠ w' &&
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        li ri ai bi ci di ei i w &&
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        li ri ai bi ci di ei j w &&
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        li ri ai bi ci di ei i w' &&
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        li ri ai bi ci di ei j w'

private def orderFortyNineAdaptiveSixthFastLive (i : Fin 8) : Bool :=
  i = 2 || 4 ≤ i.val

private def orderFortyNineAdaptiveSixthFastMate (i : Fin 8) : Fin 8 :=
  if i = 4 then 5 else if i = 5 then 4 else if i = 6 then 7 else
    if i = 7 then 6 else i

private def orderFortyNineAdaptiveSixthFastParent
    (li ri ai bi ci : Fin 8) : Bool :=
  4 ≤ li.val && 2 ≤ ri.val && ri != 3 && li != ri &&
  orderFortyNineAdaptiveSixthFastLive ai &&
  orderFortyNineAdaptiveSixthFastLive bi && ai != bi &&
  ai != li && ai != ri && bi != li && bi != ri &&
  ai != orderFortyNineAdaptiveSixthFastMate ri &&
  !(((ri = 2 && ai = orderFortyNineAdaptiveSixthFastMate li) ||
      (ai = 2 && ri = orderFortyNineAdaptiveSixthFastMate li)) &&
    bi != 2 && bi != li && bi != orderFortyNineAdaptiveSixthFastMate li) &&
  orderFortyNineAdaptiveSixthFastLive ci &&
  ci != li && ci != ri && ci != ai && ci != bi

private def orderFortyNineAdaptiveSixthFastSelectorLive
    (ri ai bi ci di ei : Fin 8) : Bool :=
  orderFortyNineThreeHighB1AdaptiveSixthLiveIndex ri ai bi ci di &&
  orderFortyNineThreeHighB1AdaptiveSixthLiveIndex ri ai bi ci ei && di != ei

theorem orderFortyNineAdaptiveSixthFastParent_of_fifth
    (li ri ai bi ci : Fin 8)
    (hfifth : orderFortyNineThreeHighB1AdaptiveFifthResidual
      li ri ai bi ci = true) :
    orderFortyNineAdaptiveSixthFastParent li ri ai bi ci = true := by
  native_decide +revert

theorem orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitness_of_dead
    (li ri ai bi ci di ei : Fin 8)
    (hparent : orderFortyNineAdaptiveSixthFastParent li ri ai bi ci = true)
    (hdead : orderFortyNineAdaptiveSixthFastSelectorLive
      ri ai bi ci di ei = false) :
    orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitnessValid
      li ri ai bi ci di ei = true := by
  native_decide +revert

theorem orderFortyNineThreeHighB1AdaptiveSixthFastResidual_of_graph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (li ri ai bi ci di ei : Fin 8)
    (hfifth : orderFortyNineThreeHighB1AdaptiveFifthResidual
      li ri ai bi ci = true)
    (hedges : ∀ i j,
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
          li ri ai bi ci di ei i j = true → G.Adj i j) :
    orderFortyNineThreeHighB1AdaptiveSixthResidual
      li ri ai bi ci di ei = true := by
  by_contra hres
  have hdead :
      orderFortyNineThreeHighB1AdaptiveSixthResidual
        li ri ai bi ci di ei = false :=
    Bool.eq_false_of_not_eq_true hres
  have hparent := orderFortyNineAdaptiveSixthFastParent_of_fifth
    li ri ai bi ci hfifth
  have hselector : orderFortyNineAdaptiveSixthFastSelectorLive
      ri ai bi ci di ei = false := by
    simpa [orderFortyNineThreeHighB1AdaptiveSixthResidual,
      orderFortyNineAdaptiveSixthFastSelectorLive, hfifth] using hdead
  have hvalid :=
    orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitness_of_dead
      li ri ai bi ci di ei hparent hselector
  unfold orderFortyNineThreeHighB1AdaptiveSixthFastDeadWitnessValid at hvalid
  split at hvalid
  · contradiction
  · next i j w w' hwitness =>
      have ⟨hvalid, hjw'⟩ := Bool.and_eq_true_iff.mp hvalid
      have ⟨hvalid, hiw'⟩ := Bool.and_eq_true_iff.mp hvalid
      have ⟨hvalid, hjw⟩ := Bool.and_eq_true_iff.mp hvalid
      have ⟨hvalid, hiw⟩ := Bool.and_eq_true_iff.mp hvalid
      have ⟨hij, hww'⟩ := Bool.and_eq_true_iff.mp hvalid
      have hij_ne : i ≠ j := of_decide_eq_true hij
      have hww_ne : w ≠ w' := of_decide_eq_true hww'
      let common := G.neighborFinset i ∩ G.neighborFinset j
      have hw : w ∈ common := by
        simp [common, hedges i w hiw, hedges j w hjw]
      have hw' : w' ∈ common := by
        simp [common, hedges i w' hiw', hedges j w' hjw']
      exact hww_ne (Finset.card_le_one.mp
        (common_le_one_of_not_containsC4 hfree i j hij_ne) w hw w' hw')

end Erdos85
