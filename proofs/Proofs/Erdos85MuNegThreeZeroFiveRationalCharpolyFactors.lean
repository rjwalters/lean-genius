import Proofs.Erdos85EigenfamilyCharpolyFactor
import Proofs.Erdos85MuNegThreeZeroFiveExplicitEigenfamilies

/-! # Rational characteristic factors forced by the h305 endpoint -/

open Finset SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

/-- The explicit rational C8 modes force service eigenvalue multiplicities
`mult(0) ≥ 4`, `mult(2) ≥ 2`, and `mult(-2) ≥ 1`. -/
theorem h305_rational_service_charpoly_factors
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R
        (fun i ↦ e (Sum.inl i)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun i ↦ e (Sum.inl i)))
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R
        (fun j ↦ e (Sum.inr j)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j))) :
    (X - C (0 : ℂ)) ^ 4 ∣ (Cedge.adjMatrix ℂ).charpoly ∧
      (X - C (2 : ℂ)) ^ 2 ∣ (Cedge.adjMatrix ℂ).charpoly ∧
      (X - C (-2 : ℂ)) ^ 1 ∣ (Cedge.adjMatrix ℂ).charpoly := by
  obtain ⟨hzEig, hzLi⟩ := h305_zeroEigenfamily_transfer
    H R Cedge hservice e hleft hright hmodeu hmodev
  obtain ⟨haEig, haLi⟩ := h305_alternatingEigenfamily_transfer
    H R Cedge hservice e hleft hright hmodeu hmodev
  obtain ⟨hdEig, hdLi⟩ := h305_shoreDifference_transfer
    H R Cedge hservice e hleft hright hmodeu hmodev
  refine ⟨?_, ?_, ?_⟩
  · let f : Fin 4 → R.edgeFinset → ℂ := fun q ↦
      edgeEndpointSumVector R
        (h305ZeroEigenfamily e (finProdFinEquiv.symm q))
    apply matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
      (Cedge.adjMatrix ℂ) 0 4 f
    · intro q
      exact hzEig (finProdFinEquiv.symm q)
    · exact hzLi.comp _ finProdFinEquiv.symm.injective
  · exact matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
      (Cedge.adjMatrix ℂ) 2 2
      (fun q ↦ edgeEndpointSumVector R (h305AlternatingEigenfamily e q))
      haEig haLi
  · exact matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
      (Cedge.adjMatrix ℂ) (-2) 1
      (fun q ↦ edgeEndpointSumVector R (h305ShoreDifferenceFamily e q))
      hdEig hdLi

end

end Erdos85

#print axioms Erdos85.h305_rational_service_charpoly_factors
