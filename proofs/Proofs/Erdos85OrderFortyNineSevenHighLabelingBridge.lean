import Proofs.Erdos85OrderFortyNineSevenHighCanonicalCapstone
import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge

/-!
# Canonical-labeling bridge for the seven-high stratum

This isolates the remaining graph normalization task from the Boolean
terminal.  A canonical labeling records precisely degree placement, fixed
high supports, and the low-neighborhood partition law for the relabeled
graph.  The generic graph faithfulness theorem then supplies the exact edge
assignment consumed by the representative certificate.
-/

namespace Erdos85

open SimpleGraph
open OrderFortyNineSevenHighCensus

def SevenHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat) : Prop :=
  let H := orderFortyNineRelabeledGraph G E
  masks.size = 49 ∧
  (∀ i : Fin 49, H.degree i = if i.val < 7 then 8 else 7) ∧
  (∀ i : Fin 49, ∀ w : Fin 9, w.val < 7 →
    decide (H.Adj i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val) ∧
  (∀ i : Fin 49, 7 ≤ i.val → ∀ w : Fin 9, w.val < 7 →
    (H.neighborFinset i ∩ orderFortyNineSupportFiber masks w).card = 1)

theorem orderFortyNineBooleanConstraints_of_sevenHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat)
    (haligned : SevenHighAlignedLabeling G E masks) :
    orderFortyNineBooleanConstraints 7 masks
      (orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E)) := by
  rcases haligned with ⟨hsize, hdegree, hsupport, hpartition⟩
  exact orderFortyNineGraphEdges_satisfy
    (orderFortyNineRelabeledGraph G E) 7 masks hsize (by omega)
      hdegree (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
      hsupport hpartition

def SevenHighCanonicalLabelingCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 7 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ index, index < (reps blocks).length ∧ ∃ E : Equiv.Perm (Fin 49),
      SevenHighAlignedLabeling G E (representativeMasks blocks index)

/-- A canonical vertex-labeling cover is sufficient for the certificate-facing
graph cover.  No SAT or finite-classification assumption enters this step. -/
theorem sevenHighCanonicalGraphCover_of_labelingCover
    {blocks : Nat} (hcover : SevenHighCanonicalLabelingCover blocks) :
    SevenHighCanonicalGraphCover blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨index, hindex, E, haligned⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  refine ⟨index, hindex,
    orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E), ?_⟩
  exact orderFortyNineBooleanConstraints_of_sevenHighAlignedLabeling
    G hfree E (representativeMasks blocks index) haligned

end Erdos85
