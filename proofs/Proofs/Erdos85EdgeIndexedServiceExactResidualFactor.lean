import Proofs.Erdos85EightEightCenteredCharpoly
import Proofs.Erdos85EdgeIndexedServiceResidualMomentPackage

/-! # Exact integer quotient factor in the service residual split -/

open SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

/-- The graph-facing residual package with the centered shore factor replaced
by its exact integer polynomial. -/
theorem edgeIndexedService_exactResidualFactor_of_eightEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (label : EightEightCycleLabeling H)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hRinj : Function.Injective (edgeEndpointSumVector R))
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hCfree : ¬ containsC4 R.edgeFinset Cedge) :
    let I := (edgeEndpointIncidenceMatrix R).mulVecLin
    let T : Module.End ℂ (R.edgeFinset → ℂ) :=
      (Cedge.adjMatrix ℂ).mulVecLin
    let W := LinearMap.ker I
    let hW : W ≤ W.comap T := by
      intro x hx
      exact edgeIndexedService_incidenceKernel_invariant
        H R Cedge hservice x hx
    let p := (T.restrict hW).charpoly
    let q : ℂ[X] :=
      (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 * X ^ 4 * (X ^ 2 - C (2 : ℂ)) ^ 4
    p.Monic ∧ p.natDegree = 32 ∧
      (Cedge.adjMatrix ℂ).charpoly = p * q ∧
      complexRootPowerSum p 1 = -8 ∧
      complexRootPowerSum p 2 = 224 ∧
      complexRootPowerSum p 3 =
        Matrix.trace ((Cedge.adjMatrix ℂ) ^ 3) - 224 ∧
      complexRootPowerSum p 4 = 1792 := by
  classical
  dsimp only
  obtain ⟨hp, hpdeg, hfactor, h1, h2, h3, h4⟩ :=
    edgeIndexedService_residual_moment_package_of_eightEight
      H R Cedge hservice label hEcard hRinj hHreg hCreg hCfree
  have hB := eightEight_centeredCharpoly_eq_integerFactor
    H e hleft hright
  rw [hB] at hfactor
  exact ⟨hp, hpdeg, hfactor, h1, h2, h3, h4⟩

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_exactResidualFactor_of_eightEight
