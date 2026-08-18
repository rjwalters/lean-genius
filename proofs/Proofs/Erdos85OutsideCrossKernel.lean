import Proofs.Erdos85OutsideCrossEigenTransport
import Proofs.Erdos85OrderSixtyFourExteriorPairGraph

/-!
# Kernel of the order-64 inside--outside incidence transport

The distinguished size-sixteen block has incidence row Gram `6I + R`, where
`R` is its six-regular exterior-pair graph.  Thus a vector killed by the
outside incidence transpose must be a `-6` eigenvector of `R`.  This packages
the only exceptional case left open by centered cross-eigenvector transport.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- In the seven-component order-64 branch, the kernel of incidence transport
is contained in the bottom (`-6`) eigenspace of the exterior-pair graph. -/
theorem orderSixtyFour_seven_components_incidenceKernel_forces_pairEigenvalue_negSix
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
      let R := exteriorPairGraph G c.supp
      ∀ v : c.supp → ℂ,
        (Matrix.conjTranspose B).mulVec v = 0 →
        (R.adjMatrix ℂ).mulVec v = (-6 : ℂ) • v := by
  classical
  obtain ⟨c, hc, hgram, _hRreg⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  refine ⟨c, hc, ?_⟩
  dsimp only
  intro v hker
  exact rectangular_incidence_kernel_forces_negative_gram_residual
    ((G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
      (fun x ↦ ¬x ∈ c.supp))
    (Matrix.conjTranspose ((G.adjMatrix ℂ).toBlock
      (fun x ↦ x ∈ c.supp) (fun x ↦ ¬x ∈ c.supp)))
    ((exteriorPairGraph G c.supp).adjMatrix ℂ)
    (6 : ℂ) v hgram hker

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_seven_components_incidenceKernel_forces_pairEigenvalue_negSix
