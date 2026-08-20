import Proofs.Erdos85EdgeIndexedServiceEigenfamilyTransfer
import Proofs.Erdos85MuNegThreeZeroFiveGlobalEndpointSumInjective

/-! # Injective spectral transfer in the corrected h305 two-shore case -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every linearly independent zero-sum `mu`-eigenfamily of the two-cycle
internal graph transfers injectively to the service graph at eigenvalue
`-mu`. -/
theorem h305_correctShoreModes_eigenfamily_transfer
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (f : ι → V → ℂ) (mu : ℂ)
    (hsum : ∀ i, ∑ x, f i x = 0)
    (heigen : ∀ i, (H.adjMatrix ℂ).mulVec (f i) = mu • f i)
    (hli : LinearIndependent ℂ f) :
    (∀ i, (Cedge.adjMatrix ℂ).mulVec (edgeEndpointSumVector R (f i)) =
        (-mu) • edgeEndpointSumVector R (f i)) ∧
      LinearIndependent ℂ (fun i ↦ edgeEndpointSumVector R (f i)) := by
  apply edgeIndexedService_eigenfamily_transfer H R Cedge hservice
    (h305_two_correctShoreModes_endpointSum_injective
      R u v huinj hvinj hcover hmodeu hmodev)
    f mu hsum heigen hli

/-- Equivalence-coordinate form for an h305 support explicitly presented as
the disjoint union of its two labeled C8 shores. -/
theorem h305_equiv_correctShoreModes_eigenfamily_transfer
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R
        (fun i ↦ e (Sum.inl i)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun i ↦ e (Sum.inl i)))
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R
        (fun j ↦ e (Sum.inr j)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j)))
    (f : ι → V → ℂ) (mu : ℂ)
    (hsum : ∀ i, ∑ x, f i x = 0)
    (heigen : ∀ i, (H.adjMatrix ℂ).mulVec (f i) = mu • f i)
    (hli : LinearIndependent ℂ f) :
    (∀ i, (Cedge.adjMatrix ℂ).mulVec (edgeEndpointSumVector R (f i)) =
        (-mu) • edgeEndpointSumVector R (f i)) ∧
      LinearIndependent ℂ (fun i ↦ edgeEndpointSumVector R (f i)) := by
  apply edgeIndexedService_eigenfamily_transfer H R Cedge hservice
    (h305_equiv_correctShoreModes_endpointSum_injective R e hmodeu hmodev)
    f mu hsum heigen hli

end

end Erdos85

#print axioms Erdos85.h305_correctShoreModes_eigenfamily_transfer
#print axioms Erdos85.h305_equiv_correctShoreModes_eigenfamily_transfer
