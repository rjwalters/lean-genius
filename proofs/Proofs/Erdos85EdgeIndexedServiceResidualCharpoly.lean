import Proofs.Erdos85EdgeIndexedServiceIncidenceKernel
import Proofs.Erdos85InvariantCharpolyDivisibility

/-!
# The residual characteristic factor of an edge-indexed service graph

The endpoint-incidence kernel is invariant under service adjacency.  In the
`h305` dimensions it therefore contributes a degree-32 characteristic factor
of the full service graph.
-/

open Finset SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

/-- The restriction of service adjacency to the endpoint-incidence kernel has
characteristic polynomial dividing the full service characteristic polynomial,
and in the `16`-vertex, `48`-edge case that factor has degree exactly `32`. -/
theorem edgeIndexedService_incidenceKernel_charpoly_dvd_and_natDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hVcard : Fintype.card V = 16)
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hinj : Function.Injective (edgeEndpointSumVector R)) :
    let I := edgeEndpointIncidenceMatrix R
    let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
    let U := LinearMap.ker I.mulVecLin
    let hU : ∀ x ∈ U, T x ∈ U := by
      intro x hx
      exact edgeIndexedService_incidenceKernel_invariant
        H R Cedge hservice x hx
    (T.restrict hU).charpoly ∣ (Cedge.adjMatrix ℂ).charpoly ∧
      (T.restrict hU).charpoly.natDegree = 32 := by
  classical
  dsimp only
  let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
  let U := LinearMap.ker (edgeEndpointIncidenceMatrix R).mulVecLin
  let hU : ∀ x ∈ U, T x ∈ U := by
    intro x hx
    exact edgeIndexedService_incidenceKernel_invariant
      H R Cedge hservice x hx
  have hdvd : (T.restrict hU).charpoly ∣ T.charpoly :=
    charpoly_restrict_dvd_of_invariant T U hU
  have hdegree : (T.restrict hU).charpoly.natDegree = 32 := by
    rw [LinearMap.charpoly_natDegree]
    simpa [U] using
      edgeEndpointIncidenceMatrix_kernel_finrank_thirtyTwo
        R hVcard hEcard hinj
  constructor
  · simpa [T, Matrix.charpoly_toLin'] using hdvd
  · exact hdegree

/-- Consumer-facing form: the full service characteristic polynomial has a
monic factor of degree exactly `32`, namely the characteristic polynomial of
the residual endpoint-incidence kernel. -/
theorem edgeIndexedService_exists_monic_residual_charpoly_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hVcard : Fintype.card V = 16)
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hinj : Function.Injective (edgeEndpointSumVector R)) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree = 32 ∧
      p ∣ (Cedge.adjMatrix ℂ).charpoly := by
  classical
  let I := edgeEndpointIncidenceMatrix R
  let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
  let U := LinearMap.ker I.mulVecLin
  let hU : ∀ x ∈ U, T x ∈ U := by
    intro x hx
    exact edgeIndexedService_incidenceKernel_invariant
      H R Cedge hservice x hx
  refine ⟨(T.restrict hU).charpoly, LinearMap.charpoly_monic _, ?_, ?_⟩
  · exact (edgeIndexedService_incidenceKernel_charpoly_dvd_and_natDegree
      H R Cedge hservice hVcard hEcard hinj).2
  · exact (edgeIndexedService_incidenceKernel_charpoly_dvd_and_natDegree
      H R Cedge hservice hVcard hEcard hinj).1

end

end Erdos85

#print axioms
  Erdos85.edgeIndexedService_incidenceKernel_charpoly_dvd_and_natDegree
#print axioms
  Erdos85.edgeIndexedService_exists_monic_residual_charpoly_factor
