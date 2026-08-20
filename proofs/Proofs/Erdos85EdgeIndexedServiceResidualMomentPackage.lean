import Proofs.Erdos85ServiceAmbientMoments
import Proofs.Erdos85EdgeIndexedServiceResidualCharpoly

/-! # Graph-facing residual moment package for the h305 service graph -/

open Finset SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

/-- The exact endpoint-incidence residual factor has degree `32` and the
fixed first, second, and fourth power sums.  Its cubic power sum retains the
ambient service triangle count. -/
theorem edgeIndexedService_residual_moment_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hVcard : Fintype.card V = 16)
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hRinj : Function.Injective (edgeEndpointSumVector R))
    (hHreg : ∀ x, H.degree x = 2)
    (hHthree : Matrix.trace ((H.adjMatrix ℂ) ^ 3) = 0)
    (hHfour : Matrix.trace ((H.adjMatrix ℂ) ^ 4) = 96)
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
    p.Monic ∧ p.natDegree = 32 ∧
      complexRootPowerSum p 1 = -8 ∧
      complexRootPowerSum p 2 = 224 ∧
      complexRootPowerSum p 3 =
        Matrix.trace ((Cedge.adjMatrix ℂ) ^ 3) - 224 ∧
      complexRootPowerSum p 4 = 1792 := by
  classical
  dsimp only
  let A := Cedge.adjMatrix ℂ
  let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
  let I := (edgeEndpointIncidenceMatrix R).mulVecLin
  let T : Module.End ℂ (R.edgeFinset → ℂ) := A.mulVecLin
  let W := LinearMap.ker I
  let hW : W ≤ W.comap T := by
    intro x hx
    exact edgeIndexedService_incidenceKernel_invariant
      H R Cedge hservice x hx
  let p := (T.restrict hW).charpoly
  have hpmonic : p.Monic := LinearMap.charpoly_monic _
  have hpdegree : p.natDegree = 32 := by
    simpa [p, T, A, I, W, hW] using
      (edgeIndexedService_incidenceKernel_charpoly_dvd_and_natDegree
        H R Cedge hservice hVcard hEcard hRinj).2
  have hfactorLin :=
    edgeIndexedService_charpoly_eq_residual_mul_centeredShore
      H R Cedge hservice hRinj
  change T.charpoly = p * B.mulVecLin.charpoly at hfactorLin
  have hfactor : A.charpoly = p * B.charpoly := by
    rw [← Matrix.charpoly_toLin', ← Matrix.charpoly_toLin']
    exact hfactorLin
  have hAherm : A.IsHermitian := by
    exact SimpleGraph.isHermitian_adjMatrix ℂ Cedge
  have hBherm : B.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [B, edgeIndexedVertexOnesMatrix,
      SimpleGraph.adjMatrix_apply, H.adj_comm]
  obtain ⟨hAone, hAtwo, hAfour⟩ :=
    serviceGraph_trace_moments_six_regular_fortyEight
      Cedge hEcard hCreg hCfree
  obtain ⟨hBone, hBtwo, hBthree, hBfour⟩ :=
    centeredShore_trace_moments H hVcard hHreg hHthree hHfour
  have hledger := h305_residualRootPowerSum_ledger_of_trace_moments
    A B p hAherm hBherm hpmonic.ne_zero hfactor
      hAone hAtwo hAfour hBone hBtwo hBthree hBfour
  exact ⟨hpmonic, hpdegree, hledger⟩

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_residual_moment_package
