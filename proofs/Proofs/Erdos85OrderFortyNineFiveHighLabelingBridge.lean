import Proofs.Erdos85OrderFortyNineFiveHighCanonicalMasks
import Proofs.Erdos85OrderFortyNineStrataCapstone
import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge

/-!
# Canonical-labeling bridge for the five-high stratum

This separates the remaining finite support-system normalization from the
already verified CNF semantics.  Once a permutation aligns a graph with one
of the three canonical mask arrays, the generic graph-edge theorem produces
the exact Boolean terminal consumed by the checked-LRAT entry point.
-/

namespace Erdos85

open SimpleGraph

def FiveHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat) : Prop :=
  let H := orderFortyNineRelabeledGraph G E
  masks.size = 49 ∧
  (∀ i : Fin 49, H.degree i = if i.val < 5 then 8 else 7) ∧
  (∀ i : Fin 49, ∀ w : Fin 9, w.val < 5 →
    decide (H.Adj i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val) ∧
  (∀ i : Fin 49, 5 ≤ i.val → ∀ w : Fin 9, w.val < 5 →
    (H.neighborFinset i ∩ orderFortyNineSupportFiber masks w).card = 1)

theorem orderFortyNineBooleanConstraints_of_fiveHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat)
    (haligned : FiveHighAlignedLabeling G E masks) :
    orderFortyNineBooleanConstraints 5 masks
      (orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E)) := by
  rcases haligned with ⟨hsize, hdegree, hsupport, hpartition⟩
  exact orderFortyNineGraphEdges_satisfy
    (orderFortyNineRelabeledGraph G E) 5 masks hsize (by omega)
      hdegree (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
      hsupport hpartition

/-- The exact remaining graph-classification statement for one five-high
triple cell. -/
def FiveHighCanonicalLabelingCover (blocks : Nat) (masks : Array Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 5 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ E : Equiv.Perm (Fin 49), FiveHighAlignedLabeling G E masks

theorem orderFortyNineTripleCellExcluded_five_of_labelingCover
    {blocks : Nat} {masks : Array Nat}
    (hcover : FiveHighCanonicalLabelingCover blocks masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 5 masks edges → False) :
    OrderFortyNineTripleCellExcluded 5 blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨E, haligned⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  exact hexclude _
    (orderFortyNineBooleanConstraints_of_fiveHighAlignedLabeling
      G hfree E masks haligned)

theorem orderFortyNineTripleCellExcluded_five_t0_of_labelingCover
    (hcover : FiveHighCanonicalLabelingCover 0
      orderFortyNineFiveHighT0Masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 5
        orderFortyNineFiveHighT0Masks edges → False) :
    OrderFortyNineTripleCellExcluded 5 0 :=
  orderFortyNineTripleCellExcluded_five_of_labelingCover hcover hexclude

theorem orderFortyNineTripleCellExcluded_five_t1_of_labelingCover
    (hcover : FiveHighCanonicalLabelingCover 1
      orderFortyNineFiveHighT1Masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 5
        orderFortyNineFiveHighT1Masks edges → False) :
    OrderFortyNineTripleCellExcluded 5 1 :=
  orderFortyNineTripleCellExcluded_five_of_labelingCover hcover hexclude

theorem orderFortyNineTripleCellExcluded_five_t2_of_labelingCover
    (hcover : FiveHighCanonicalLabelingCover 2
      orderFortyNineFiveHighT2Masks)
    (hexclude : ∀ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 5
        orderFortyNineFiveHighT2Masks edges → False) :
    OrderFortyNineTripleCellExcluded 5 2 :=
  orderFortyNineTripleCellExcluded_five_of_labelingCover hcover hexclude

end Erdos85
