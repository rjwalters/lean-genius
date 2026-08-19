import Proofs.Erdos85EightEightLowExteriorModelCapstone

/-!
# Concrete checked terminal for the low eight-plus-eight model

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The structural exterior model is naturally stated using an arbitrary cyclic
labeling and an eigenline sign function.  Phase alignment turns those data
into the fixed graph isomorphism used by the owner certificate.  This file
checks that the same alignment also preserves the generator's internal
two-cycle table, then invokes the completed graph-to-LRAT contradiction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- The fixed graph used by cycle labelings and the Boolean cycle table used
by the owner generator are definitionally the same finite relation. -/
theorem eightEightCycleGraph_adj_iff_cycleAdj (u v : Fin 16) :
    eightEightCycleGraph.Adj u v ↔ eightEightCycleAdj u v = true := by
  revert u v
  decide

/-- Sign-phase alignment rotates each shore, hence preserves the internal
two-cycle adjacency table. -/
theorem eightEightAlignedVertexEquiv_cycleAdj
    {W : Type*} (H : SimpleGraph W)
    (label : EightEightCycleLabeling H) (s : W → ℤ)
    (x y : W) :
    H.Adj x y ↔
      eightEightCycleAdj
        (eightEightAlignedVertexEquiv label s x)
        (eightEightAlignedVertexEquiv label s y) = true := by
  rw [label.map_adj_iff, ← eightEightCycleGraph_adj_iff_cycleAdj]
  exact (eightEightParityShift_preserves_adj
    (!eightEightLabelSign label s 0) (!eightEightLabelSign label s 8)
    (label.toEquiv x) (label.toEquiv y)).symm

/-- End-to-end low-`8+8` contradiction in the exact intrinsic form emitted
by the structural shore analysis. -/
theorem lowEightExteriorPairModel_false_of_cycleLabeling
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
          eightEightLowExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1) : False := by
  let modelIso := lowEightExteriorPairModelIso_of_cycleLabeling
    G c label s hsign hflip hmodel
  apply lowEightExteriorPairModel_false
    G hfree c hcard hinc hqcard hRedges modelIso
  intro x y
  exact eightEightAlignedVertexEquiv_cycleAdj
    (G.induce c.supp) label (fun z ↦ s z.1) x y

end

end Erdos85

#print axioms Erdos85.eightEightAlignedVertexEquiv_cycleAdj
#print axioms Erdos85.lowEightExteriorPairModel_false_of_cycleLabeling
