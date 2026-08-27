import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFifthStructural

/-! # Graph consumer for the adaptive fifth split -/

namespace Erdos85

open SimpleGraph

private def orderFortyNineThreeHighB1AdaptiveFifthWitnessValid
    (li ri ai bi ci : Fin 8) : Bool :=
  match orderFortyNineThreeHighB1AdaptiveFifthWitness li ri ai bi ci with
  | none => false
  | some (i, j, w, w') =>
      i ≠ j && w ≠ w' &&
      orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci i w &&
      orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci j w &&
      orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci i w' &&
      orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci j w'

/-- Inside a live fourth parent, the computed fifth witness is valid exactly
for the 576 structurally dead children. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthWitness_iff_dead :
    ∀ li ri ai bi ci : Fin 8,
      orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = true →
      (orderFortyNineThreeHighB1AdaptiveFifthWitnessValid li ri ai bi ci = true ↔
        orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci = false) := by
  native_decide

/-- A C4-free graph realizing a live fourth parent and one fifth selector
must lie in the exact sixty-four-cell fifth residue. -/
theorem orderFortyNineThreeHighB1AdaptiveFifthResidual_of_graph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (li ri ai bi ci : Fin 8)
    (hfourth : orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = true)
    (hedges : ∀ i j,
      orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge li ri ai bi ci i j = true →
        G.Adj i j) :
    orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci = true := by
  by_contra hres
  have hdead :
      orderFortyNineThreeHighB1AdaptiveFifthResidual li ri ai bi ci = false :=
    Bool.eq_false_of_not_eq_true hres
  have hvalid :=
    (orderFortyNineThreeHighB1AdaptiveFifthWitness_iff_dead
      li ri ai bi ci hfourth).2 hdead
  unfold orderFortyNineThreeHighB1AdaptiveFifthWitnessValid at hvalid
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
