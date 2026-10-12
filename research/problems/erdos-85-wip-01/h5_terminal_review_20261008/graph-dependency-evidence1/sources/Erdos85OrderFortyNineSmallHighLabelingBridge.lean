import Proofs.Erdos85OrderFortyNineSmallHighCanonicalCapstone
import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge

/-!
# Canonical-labeling bridge for the small-high strata

An aligned labeling records exactly the four conditions needed by the generic
order-49 graph-to-Boolean terminal.  Specializing it at h=3 and h=5 reduces
the graph-cover obligations to pure canonical vertex labeling.
-/

namespace Erdos85

open SimpleGraph
open OrderFortyNineSmallHighCensus

def SmallHighAlignedLabeling (h : Nat)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat) : Prop :=
  let H := orderFortyNineRelabeledGraph G E
  masks.size = 49 ∧
  (∀ i : Fin 49, H.degree i = if i.val < h then 8 else 7) ∧
  (∀ i : Fin 49, ∀ w : Fin 9, w.val < h →
    decide (H.Adj i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val) ∧
  (∀ i : Fin 49, h ≤ i.val → ∀ w : Fin 9, w.val < h →
    (H.neighborFinset i ∩ orderFortyNineSupportFiber masks w).card = 1)

theorem orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
    {h : Nat} (hh : h ≤ 9)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (E : Equiv.Perm (Fin 49)) (masks : Array Nat)
    (haligned : SmallHighAlignedLabeling h G E masks) :
    orderFortyNineBooleanConstraints h masks
      (orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E)) := by
  rcases haligned with ⟨hsize, hdegree, hsupport, hpartition⟩
  exact orderFortyNineGraphEdges_satisfy
    (orderFortyNineRelabeledGraph G E) h masks hsize hh
      hdegree (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
      hsupport hpartition

def ThreeHighCanonicalLabelingCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 3 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ E : Equiv.Perm (Fin 49), SmallHighAlignedLabeling 3 G E
      (threeHighRepresentativeMasks blocks)

def FiveHighCanonicalLabelingCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 5 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ E : Equiv.Perm (Fin 49), SmallHighAlignedLabeling 5 G E
      (fiveHighRepresentativeMasks blocks)

theorem threeHighCanonicalGraphCover_of_labelingCover
    {blocks : Nat} (hcover : ThreeHighCanonicalLabelingCover blocks) :
    ThreeHighCanonicalGraphCover blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨E, haligned⟩ := hcover G inferInstance inferInstance inferInstance
    hfree hmin hhigh hblocks
  refine ⟨orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E), ?_⟩
  exact orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
    (h := 3) (by omega) G hfree E (threeHighRepresentativeMasks blocks) haligned

theorem fiveHighCanonicalGraphCover_of_labelingCover
    {blocks : Nat} (hcover : FiveHighCanonicalLabelingCover blocks) :
    FiveHighCanonicalGraphCover blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨E, haligned⟩ := hcover G inferInstance inferInstance inferInstance
    hfree hmin hhigh hblocks
  refine ⟨orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E), ?_⟩
  exact orderFortyNineBooleanConstraints_of_smallHighAlignedLabeling
    (h := 5) (by omega) G hfree E (fiveHighRepresentativeMasks blocks) haligned

end Erdos85
