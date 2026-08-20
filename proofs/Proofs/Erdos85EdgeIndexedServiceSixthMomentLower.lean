import Proofs.Erdos85CenteredShoreSixthMoment
import Proofs.Erdos85ResidualSixthMomentHankel
import Proofs.Erdos85EdgeIndexedServiceResidualMomentPackage

/-! # Sixth-moment lower bound for the h305 service graph -/

open SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

theorem complexRootPowerSum_re_eq_realParts
    (s : Multiset ℂ) (m : ℕ) (hreal : ∀ z ∈ s, z.im = 0) :
    (s.map fun z ↦ z ^ m).sum.re =
      ((s.map Complex.re).map fun x ↦ x ^ m).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      have hz : z.im = 0 := hreal z (by simp)
      have hs : ∀ w ∈ s, w.im = 0 := by
        intro w hw
        exact hreal w (by simp [hw])
      have hzeq : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hz]
      simp only [Multiset.map_cons, Multiset.sum_cons]
      change (z ^ m).re + (s.map fun w ↦ w ^ m).sum.re =
        z.re ^ m + ((s.map Complex.re).map fun x ↦ x ^ m).sum
      rw [ih hs, hzeq]
      rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]

/-- A real-rooted factor of a Hermitian characteristic polynomial inherits
the h305 Hankel lower bound from its second and fourth moments. -/
theorem hermitianResidual_sixthMoment_lower
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (B : Matrix Y Y ℂ) (p : ℂ[X])
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hp : p ≠ 0) (hfactor : A.charpoly = p * B.charpoly)
    (h2 : complexRootPowerSum p 2 = 224)
    (h4 : complexRootPowerSum p 4 = 1792)
    (hB6 : Matrix.trace (B ^ 6) = 46912) :
    61248 ≤ (Matrix.trace (A ^ 6)).re := by
  have hrootReal : ∀ z ∈ p.roots, z.im = 0 := by
    intro z hz
    have hzchar : z ∈ A.charpoly.roots := by
      rw [hfactor, roots_mul (mul_ne_zero hp B.charpoly_monic.ne_zero),
        Multiset.mem_add]
      exact Or.inl hz
    rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
    obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
    simp
  let s : Multiset ℝ := p.roots.map Complex.re
  have hineq := multiset_fourth_sq_le_second_mul_sixth s
  have hs2 : (s.map fun x ↦ x ^ 2).sum = 224 := by
    have hre := congrArg Complex.re h2
    rw [complexRootPowerSum] at hre
    rw [complexRootPowerSum_re_eq_realParts p.roots 2 hrootReal] at hre
    norm_num at hre
    simpa [s, Multiset.map_map] using hre
  have hs4 : (s.map fun x ↦ x ^ 4).sum = 1792 := by
    have hre := congrArg Complex.re h4
    rw [complexRootPowerSum] at hre
    rw [complexRootPowerSum_re_eq_realParts p.roots 4 hrootReal] at hre
    norm_num at hre
    simpa [s, Multiset.map_map] using hre
  have hs6 :
      (s.map fun x ↦ x ^ 6).sum = (complexRootPowerSum p 6).re := by
    rw [complexRootPowerSum]
    simpa [s, Multiset.map_map] using
      (complexRootPowerSum_re_eq_realParts p.roots 6 hrootReal).symm
  rw [hs2, hs4, hs6] at hineq
  have hres := residualRootPowerSum_eq_trace_sub_trace
    A B p hA hB hp hfactor 6
  have hresRe := congrArg Complex.re hres
  rw [hB6] at hresRe
  norm_num at hresRe
  nlinarith

/-- For the degree-six, 48-vertex h305 service graph with shore
`C8 ⊔ C8`, the ambient sixth spectral moment is at least `61248`. -/
theorem edgeIndexedService_trace_six_lower_of_eightEight
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
    61248 ≤ (Matrix.trace ((Cedge.adjMatrix ℂ) ^ 6)).re := by
  classical
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
  obtain ⟨hp, _hpdeg, hfactor, _h1, h2, _h3, h4⟩ :=
    edgeIndexedService_residual_moment_package_of_eightEight
      H R Cedge hservice label hEcard hRinj hHreg hCreg hCfree
  have hAherm : A.IsHermitian :=
    SimpleGraph.isHermitian_adjMatrix ℂ Cedge
  have hBherm : B.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [B, edgeIndexedVertexOnesMatrix,
      SimpleGraph.adjMatrix_apply, H.adj_comm]
  have hB6 : Matrix.trace (B ^ 6) = 46912 := by
    simpa [B] using eightEight_centeredShore_trace_six H e hleft hright
  simpa [A] using hermitianResidual_sixthMoment_lower
    A B p hAherm hBherm hp.ne_zero hfactor h2 h4 hB6

end

end Erdos85

#print axioms Erdos85.hermitianResidual_sixthMoment_lower
#print axioms Erdos85.edgeIndexedService_trace_six_lower_of_eightEight
