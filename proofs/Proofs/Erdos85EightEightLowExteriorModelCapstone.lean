import Proofs.Erdos85EightEightLowExteriorModelIso

/-! # Fixed-model graph isomorphism capstone for low eight-plus-eight -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Once a cyclic labeling has the intrinsic low-`8+8` exterior-pair
description, sign phase alignment produces the exact graph isomorphism used
by the exterior-owner certificate pipeline. -/
noncomputable def lowEightExteriorPairModelIso_of_cycleLabeling
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
          eightEightLowExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1) :
    exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph :=
  lowEightExteriorPairModelIso G c
    (eightEightAlignedVertexEquiv label (fun x => s x.1))
    (eightEightLowExteriorPair_model_of_cycleLabeling
      (exteriorPairGraph G c) (G.induce c.supp) label (fun x => s x.1)
        hsign hflip hmodel)

end


end Erdos85

#print axioms Erdos85.lowEightExteriorPairModelIso_of_cycleLabeling
