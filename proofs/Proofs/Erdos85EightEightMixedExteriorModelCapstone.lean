import Proofs.Erdos85EightEightMixedExteriorModelIso

/-! # Fixed-model graph isomorphism capstone for mixed eight-plus-eight -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Once a cyclic labeling has the intrinsic mixed-`8+8` exterior-pair
description, sign phase alignment produces the exact graph isomorphism used
by the checked mixed-owner certificate pipeline. -/
noncomputable def mixedEightExteriorPairModelIso_of_cycleLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (label : EightEightCycleLabeling (G.induce c.supp))
    (s : V → ℤ)
    (hsign : ∀ x : c.supp, s x.1 = -1 ∨ s x.1 = 1)
    (hflip : ∀ ⦃x y : c.supp⦄,
      (G.induce c.supp).Adj x y → s x.1 = -s y.1)
    (hmodel : ∀ x y : c.supp,
      (exteriorPairGraph G c).Adj x y ↔
        if (label.toEquiv x).val / 8 = (label.toEquiv y).val / 8 then
          MixedOwnerBridge.eightEightMixedExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1) :
    exteriorPairGraph G c ≃g
      MixedOwnerBridge.eightEightMixedExteriorPairGraph :=
  MixedOwnerBridge.mixedEightExteriorPairModelIso G c
    (eightEightAlignedVertexEquiv label (fun x => s x.1))
    (eightEightMixedExteriorPair_model_of_cycleLabeling
      (exteriorPairGraph G c) (G.induce c.supp) label (fun x => s x.1)
        hsign hflip hmodel)

/-- Checked mixed terminal in intrinsic cyclic coordinates.  This is the
graph-facing socket: phase alignment, outside-owner enumeration, DIMACS
valuation, and the LRAT contradiction are all internal to the conclusion. -/
theorem mixedEightExteriorPairModel_false_of_cycleLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (label : EightEightCycleLabeling (G.induce c.supp))
    (s : V → ℤ)
    (hsign : ∀ x : c.supp, s x.1 = -1 ∨ s x.1 = 1)
    (hflip : ∀ ⦃x y : c.supp⦄,
      (G.induce c.supp).Adj x y → s x.1 = -s y.1)
    (hmodel : ∀ x y : c.supp,
      (exteriorPairGraph G c).Adj x y ↔
        if (label.toEquiv x).val / 8 = (label.toEquiv y).val / 8 then
          MixedOwnerBridge.eightEightMixedExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1) : False := by
  let modelIso := mixedEightExteriorPairModelIso_of_cycleLabeling
    G c label s hsign hflip hmodel
  apply MixedOwnerBridge.mixedEightExteriorPairModel_false
    G hfree c hcard hinc hqcard hRedges modelIso
  intro x y
  change (G.induce c.supp).Adj x y ↔ _
  rw [label.map_adj_iff]
  rw [← eightEightParityShift_preserves_adj
    (!eightEightLabelSign label (fun z => s z.1) 0)
    (!eightEightLabelSign label (fun z => s z.1) 8)]
  rw [eightEightCycleGraph_adj_iff_cycleAdj_mixedBridge]
  rfl

end


end Erdos85

#print axioms Erdos85.mixedEightExteriorPairModelIso_of_cycleLabeling
#print axioms Erdos85.mixedEightExteriorPairModel_false_of_cycleLabeling
