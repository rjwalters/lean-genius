import Proofs.Erdos85OrderFortyNineThreeHighCanonicalMasks
import Proofs.Erdos85OrderFortyNineStrataCapstone
import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge

/-! # Canonical-labeling bridge for the three-high stratum -/

namespace Erdos85

open SimpleGraph

def ThreeHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat) : Prop :=
  let H := orderFortyNineRelabeledGraph G E
  masks.size = 49 ∧
  (∀ i : Fin 49, H.degree i = if i.val < 3 then 8 else 7) ∧
  (∀ i : Fin 49, ∀ w : Fin 9, w.val < 3 →
    decide (H.Adj i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val) ∧
  (∀ i : Fin 49, 3 ≤ i.val → ∀ w : Fin 9, w.val < 3 →
    (H.neighborFinset i ∩ orderFortyNineSupportFiber masks w).card = 1)

theorem orderFortyNineBooleanConstraints_of_threeHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat)
    (haligned : ThreeHighAlignedLabeling G E masks) :
    orderFortyNineBooleanConstraints 3 masks
      (orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E)) := by
  rcases haligned with ⟨hsize, hdegree, hsupport, hpartition⟩
  exact orderFortyNineGraphEdges_satisfy
    (orderFortyNineRelabeledGraph G E) 3 masks hsize (by omega)
      hdegree (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
      hsupport hpartition

def ThreeHighMaskCanonicalLabelingCover (blocks : Nat) (masks : Array Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 3 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ E : Equiv.Perm (Fin 49), ThreeHighAlignedLabeling G E masks

theorem orderFortyNineTripleCellExcluded_three_of_labelingCover
    {blocks : Nat} {masks : Array Nat}
    (hcover : ThreeHighMaskCanonicalLabelingCover blocks masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 3 masks edges → False) :
    OrderFortyNineTripleCellExcluded 3 blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨E, haligned⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  exact hexclude _
    (orderFortyNineBooleanConstraints_of_threeHighAlignedLabeling
      G hfree E masks haligned)

theorem orderFortyNineTripleCellExcluded_three_t0_of_labelingCover
    (hcover : ThreeHighMaskCanonicalLabelingCover 0
      orderFortyNineThreeHighT0Masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 3
        orderFortyNineThreeHighT0Masks edges → False) :
    OrderFortyNineTripleCellExcluded 3 0 :=
  orderFortyNineTripleCellExcluded_three_of_labelingCover hcover hexclude

theorem orderFortyNineTripleCellExcluded_three_t1_of_labelingCover
    (hcover : ThreeHighMaskCanonicalLabelingCover 1
      orderFortyNineThreeHighT1Masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 3
        orderFortyNineThreeHighT1Masks edges → False) :
    OrderFortyNineTripleCellExcluded 3 1 :=
  orderFortyNineTripleCellExcluded_three_of_labelingCover hcover hexclude

end Erdos85
