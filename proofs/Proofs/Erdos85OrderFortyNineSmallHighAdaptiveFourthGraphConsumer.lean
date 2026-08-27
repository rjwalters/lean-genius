import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveFourthStructural
import Proofs.Erdos85Problem

/-!
# Graph consumer for the adaptive fourth split

This module certifies the finite C4 calculation behind the fourth-level
residual census.  The fixed-edge predicate is the exact positive support and
matching fragment used by the computation; it intentionally does not inherit
the smaller third-level witness fragment.
-/

namespace Erdos85

open SimpleGraph

/-- Positive support, parent, and matching edges used by the fourth-level C4
witnesses. -/
def orderFortyNineThreeHighB1AdaptiveFourthFixedEdge
    (i j : Fin 49) : Bool :=
  let pairs : List (Fin 49 × Fin 49) :=
    [(0, 3), (0, 4), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
     (1, 3), (1, 5), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17),
     (2, 4), (2, 5), (2, 18), (2, 19), (2, 20), (2, 21), (2, 22), (2, 23),
     (3, 4), (3, 12), (3, 24), (3, 25), (4, 18), (5, 13), (5, 19),
     (6, 7), (8, 9), (10, 11), (14, 15), (16, 17), (20, 21), (22, 23)]
  pairs.any fun ab =>
    (i = ab.1 && j = ab.2) || (i = ab.2 && j = ab.1)

/-- Forced edges in one live third cell and one positive fourth child. -/
def orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge
    (li ri ai bi : Fin 8) (i j : Fin 49) : Bool :=
  orderFortyNineThreeHighB1AdaptiveFourthFixedEdge i j ||
    ((i = 18 && j = orderFortyNineThreeHighB1AdaptiveCandidates li) ||
      (j = 18 && i = orderFortyNineThreeHighB1AdaptiveCandidates li)) ||
    ((i = 20 && j = orderFortyNineThreeHighB1AdaptiveCandidates ri) ||
      (j = 20 && i = orderFortyNineThreeHighB1AdaptiveCandidates ri)) ||
    ((i = 21 && j = orderFortyNineThreeHighB1AdaptiveCandidates ai) ||
      (j = 21 && i = orderFortyNineThreeHighB1AdaptiveCandidates ai)) ||
    ((i = 22 && j = orderFortyNineThreeHighB1AdaptiveCandidates bi) ||
      (j = 22 && i = orderFortyNineThreeHighB1AdaptiveCandidates bi))

private def orderFortyNineAdaptiveFourthWitnessVertices : List (Fin 49) :=
  (List.finRange 26).map fun i => ⟨i.val, by omega⟩

private def orderFortyNineAdaptiveFourthEndpointPairs :
    List (Fin 49 × Fin 49) :=
  orderFortyNineAdaptiveFourthWitnessVertices.flatMap fun i =>
    (orderFortyNineAdaptiveFourthWitnessVertices.filter fun j => i.val < j.val).map
      fun j => (i, j)

private def orderFortyNineAdaptiveFourthCommon
    (li ri ai bi : Fin 8) (i j : Fin 49) : List (Fin 49) :=
  orderFortyNineAdaptiveFourthWitnessVertices.filter fun w =>
    orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi i w &&
      orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi j w

/-- A computed pair of endpoints and two common neighbors whenever the forced
fourth child is structurally dead. -/
def orderFortyNineThreeHighB1AdaptiveFourthWitness
    (li ri ai bi : Fin 8) : Option OrderFortyNineAdaptiveC4Witness :=
  match orderFortyNineAdaptiveFourthEndpointPairs.find? fun ij =>
      2 ≤ (orderFortyNineAdaptiveFourthCommon li ri ai bi ij.1 ij.2).length with
  | none => none
  | some (i, j) =>
      match orderFortyNineAdaptiveFourthCommon li ri ai bi i j with
      | w :: w' :: _ => some (i, j, w, w')
      | _ => none

private def orderFortyNineThreeHighB1AdaptiveFourthWitnessValid
    (li ri ai bi : Fin 8) : Bool :=
  match orderFortyNineThreeHighB1AdaptiveFourthWitness li ri ai bi with
  | none => false
  | some (i, j, w, w') =>
      i ≠ j && w ≠ w' &&
      orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi i w &&
      orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi j w &&
      orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi i w' &&
      orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi j w'

/-- The compact eighty-cell predicate is exactly the residue of the computed
C4 witness search inside the sixteen live third cells. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthWitness_iff_dead :
    ∀ li ri ai bi : Fin 8,
      orderFortyNineThreeHighB1AdaptiveResidual li ri = true →
      (orderFortyNineThreeHighB1AdaptiveFourthWitnessValid li ri ai bi = true ↔
        orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = false) := by
  native_decide

/-- A C4-free graph realizing the exact fixed edges and four selector edges
must lie in the eighty-cell fourth residue. -/
theorem orderFortyNineThreeHighB1AdaptiveFourthResidual_of_graph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (li ri ai bi : Fin 8)
    (hthird : orderFortyNineThreeHighB1AdaptiveResidual li ri = true)
    (hedges : ∀ i j,
      orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge li ri ai bi i j = true →
        G.Adj i j) :
    orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = true := by
  by_contra hres
  have hdead : orderFortyNineThreeHighB1AdaptiveFourthResidual li ri ai bi = false :=
    Bool.eq_false_of_not_eq_true hres
  have hvalid :=
    (orderFortyNineThreeHighB1AdaptiveFourthWitness_iff_dead li ri ai bi hthird).2 hdead
  unfold orderFortyNineThreeHighB1AdaptiveFourthWitnessValid at hvalid
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
