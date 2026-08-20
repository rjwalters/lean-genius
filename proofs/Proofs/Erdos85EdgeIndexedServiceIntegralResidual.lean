import Proofs.Erdos85EdgeIndexedServiceExactResidualFactor

/-! # Integral descent of the h305 service residual factor -/

open SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

def h305CenteredServiceFactorInt : ℤ[X] :=
  (X - C 6) * (X - C (-2)) * (X - C 2) ^ 2 * X ^ 4 *
    (X ^ 2 - C 2) ^ 4

theorem h305CenteredServiceFactorInt_monic :
    h305CenteredServiceFactorInt.Monic := by
  unfold h305CenteredServiceFactorInt
  monicity <;> norm_num

theorem h305CenteredServiceFactorInt_map_complex :
    h305CenteredServiceFactorInt.map (Int.castRingHom ℂ) =
      (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 * X ^ 4 * (X ^ 2 - C (2 : ℂ)) ^ 4 := by
  norm_num [h305CenteredServiceFactorInt]
  rw [show (6 : ℂ[X]) = C (6 : ℂ) by
        exact (Polynomial.C_eq_natCast 6).symm,
      show (2 : ℂ[X]) = C (2 : ℂ) by
        exact (Polynomial.C_eq_natCast 2).symm]

/-- A monic integral factor remains a factor before an injective scalar
extension; cancellation then identifies the complementary mapped factor. -/
theorem exists_monic_integral_residual_of_complex_factor
    (P F : ℤ[X]) (p : ℂ[X])
    (hP : P.Monic) (hF : F.Monic)
    (hfactor : P.map (Int.castRingHom ℂ) =
      p * F.map (Int.castRingHom ℂ)) :
    ∃ R : ℤ[X], R.Monic ∧ P = R * F ∧
      R.map (Int.castRingHom ℂ) = p := by
  let f := Int.castRingHom ℂ
  have hf : Function.Injective f := Int.cast_injective
  have hdivMap : F.map f ∣ P.map f := by
    refine ⟨p, ?_⟩
    rw [hfactor, mul_comm]
  have hdiv : F ∣ P :=
    (Polynomial.map_dvd_map f hf hF).mp hdivMap
  obtain ⟨R, hR⟩ := hdiv
  have hRmonic : R.Monic := by
    apply hF.of_mul_monic_left
    rw [← hR]
    exact hP
  have hmapped := congrArg (Polynomial.map f) hR
  rw [Polynomial.map_mul, hfactor] at hmapped
  have heq : F.map f * R.map f = F.map f * p := by
    calc
      F.map f * R.map f = p * F.map f := hmapped.symm
      _ = F.map f * p := mul_comm _ _
  have hRmap : R.map f = p :=
    mul_left_cancel₀ (hF.map f).ne_zero heq
  exact ⟨R, hRmonic, by rw [hR, mul_comm], hRmap⟩

/-- The degree-32 endpoint-incidence residual is the scalar extension of a
monic integer polynomial, and the full integer service characteristic
polynomial splits by the explicit centered `C8 ⊔ C8` factor. -/
theorem edgeIndexedService_exists_integralResidual_of_eightEight
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
    ∃ P : ℤ[X], P.Monic ∧ P.natDegree = 32 ∧
      (Cedge.adjMatrix ℤ).charpoly = P * h305CenteredServiceFactorInt ∧
      P.map (Int.castRingHom ℂ) = p := by
  classical
  dsimp only
  obtain ⟨hp, hpdeg, hfactor, _⟩ :=
    edgeIndexedService_exactResidualFactor_of_eightEight
      H R Cedge hservice label e hleft hright hEcard hRinj hHreg
        hCreg hCfree
  let P₀ := (Cedge.adjMatrix ℤ).charpoly
  have hadjMap : (Cedge.adjMatrix ℤ).map (Int.castRingHom ℂ) =
      Cedge.adjMatrix ℂ := by
    exact adjMatrix_map_intCast Cedge
  have hPmap : P₀.map (Int.castRingHom ℂ) =
      (Cedge.adjMatrix ℂ).charpoly := by
    dsimp [P₀]
    rw [← Matrix.charpoly_map, hadjMap]
  have hfactor' := hfactor
  rw [← hPmap, ← h305CenteredServiceFactorInt_map_complex] at hfactor'
  obtain ⟨P, hPmonic, hPfactor, hPmapResidual⟩ :=
    exists_monic_integral_residual_of_complex_factor
      P₀ h305CenteredServiceFactorInt _
        (Cedge.adjMatrix ℤ).charpoly_monic
        h305CenteredServiceFactorInt_monic hfactor'
  have hPdegree : P.natDegree = 32 := by
    have hf : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
    rw [← Polynomial.natDegree_map_eq_of_injective hf P,
      hPmapResidual, hpdeg]
  exact ⟨P, hPmonic, hPdegree, hPfactor, hPmapResidual⟩

end

end Erdos85

#print axioms Erdos85.exists_monic_integral_residual_of_complex_factor
#print axioms
  Erdos85.edgeIndexedService_exists_integralResidual_of_eightEight
