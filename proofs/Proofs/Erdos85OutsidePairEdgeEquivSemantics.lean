import Proofs.Erdos85NegativeSignedJointOutsidePairEncoding

/-! # Semantic outside-owner equivalence with exterior edges -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An outside-to-exterior-edge equivalence retaining its essential endpoint
incidence semantics. -/
structure OutsidePairEdgeEquivSemantics
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) where
  equiv : {x : Fin 64 // x ∉ c.supp} ≃
    (exteriorPairGraph G c.supp).edgeFinset
  mem_edge_iff_adj : ∀ z u,
    u ∈ (equiv z).1.toFinset ↔ G.Adj u.1 z.1

/-- At regular order 64 the canonical outside-pair equivalence exists with
endpoint membership explicitly identified with ambient adjacency. -/
theorem exists_outsidePairEdgeEquivSemantics
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    Nonempty (OutsidePairEdgeEquivSemantics G c) := by
  classical
  obtain ⟨_label, hqcard, hcard, hinc, _himage, _hRreg, hRedges,
      _hCgReg, _hCgFree, _hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  let e := outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
    hcard hinc hqcard hRedges
  refine ⟨⟨e, ?_⟩⟩
  intro z u
  change u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset ↔
    G.Adj u.1 z.1
  exact mem_outsidePair_toFinset_iff_adj
    G (secondOrderDefectGraph G) c hcard z u

end

end Erdos85

#print axioms Erdos85.exists_outsidePairEdgeEquivSemantics
