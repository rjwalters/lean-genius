import Proofs.Erdos85EdgeIndexedServiceEigenvectorTransfer

/-! # Injective transfer of service eigenvector families -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- An injective endpoint-sum map preserves every linearly independent family. -/
theorem edgeEndpointSumVector_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*}
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hinj : Function.Injective (edgeEndpointSumVector R))
    (f : ι → V → ℂ) (hli : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun i ↦ edgeEndpointSumVector R (f i)) := by
  let T : (V → ℂ) →ₗ[ℂ] (R.edgeFinset → ℂ) :=
    (edgeEndpointIncidenceMatrix R).transpose.mulVecLin
  have hinjT : Function.Injective T := by
    intro x y hxy
    apply hinj
    exact hxy
  have hker : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr hinjT
  change LinearIndependent ℂ (T ∘ f)
  exact hli.map' T hker

/-- Under an injective endpoint-sum map, a linearly independent zero-sum
`mu`-eigenfamily of `H` transfers to a linearly independent `-mu`-eigenfamily
of the edge-indexed service graph. -/
theorem edgeIndexedService_eigenfamily_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*}
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hinj : Function.Injective (edgeEndpointSumVector R))
    (f : ι → V → ℂ) (mu : ℂ)
    (hsum : ∀ i, ∑ x, f i x = 0)
    (heigen : ∀ i, (H.adjMatrix ℂ).mulVec (f i) = mu • f i)
    (hli : LinearIndependent ℂ f) :
    (∀ i, (Cedge.adjMatrix ℂ).mulVec (edgeEndpointSumVector R (f i)) =
        (-mu) • edgeEndpointSumVector R (f i)) ∧
      LinearIndependent ℂ (fun i ↦ edgeEndpointSumVector R (f i)) := by
  constructor
  · intro i
    exact edgeIndexedService_eigenvector_transfer H R Cedge hservice
      (f i) mu (hsum i) (heigen i)
  · exact edgeEndpointSumVector_linearIndependent R hinj f hli

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_eigenfamily_transfer
