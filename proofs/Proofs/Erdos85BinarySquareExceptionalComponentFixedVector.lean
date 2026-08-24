import Proofs.Erdos85BinarySquareExceptionalCoreFixedVector

/-!
# Exceptional component fixed vector

The exceptional-core hypotheses can be stated intrinsically: the union of
the full and empty centers is the support of a defect component of order
`q`.  Existing binary-square component rigidity makes that support a clique;
the saturated-core theorem then supplies the two-pole fixed vector.
-/

open SimpleGraph

namespace Erdos85

/-- Two empty vertices in an order-`q` second-order-defect component have a
sum indicator fixed by the binary defect adjacency matrix. -/
theorem binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcardV : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q)
    (full empty : Finset V) (hdisj : Disjoint full empty)
    (hsupport : (↑(full ∪ empty) : Set V) = c.supp)
    (pole₁ pole₂ : V) (hpole₁ : pole₁ ∈ empty) (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hcardCore : (full ∪ empty).card = q := by
    rw [← Set.ncard_coe_finset, hsupport, hc]
  have hclique : ∀ ⦃u v⦄, u ∈ full ∪ empty → v ∈ full ∪ empty →
      u ≠ v → (secondOrderDefectGraph G).Adj u v := by
    intro u v hu hv huv
    have huComp : (secondOrderDefectGraph G).connectedComponentMk u = c := by
      rw [← SimpleGraph.ConnectedComponent.mem_supp_iff, ← hsupport]
      exact hu
    have hvComp : (secondOrderDefectGraph G).connectedComponentMk v = c := by
      rw [← SimpleGraph.ConnectedComponent.mem_supp_iff, ← hsupport]
      exact hv
    exact binarySquare_regular_sizeQ_defectComponent_adj
      G hfree hq hreg hcardV c hc huComp hvComp huv
  exact binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore
    G hfree hq hreg hcardV full empty hdisj hcardCore hclique
    pole₁ pole₂ hpole₁ hpole₂ hpoles

end Erdos85

#print axioms Erdos85.binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalComponent
