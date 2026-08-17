import Proofs.Erdos85PolynomialSecondNewtonIdentity
import Proofs.Erdos85OrderSixtyFourCyclePrimaryMomentTerminal
import Proofs.Erdos85HermitianFactorSecondMoment

/-! # Cycle-primary moments inside a Hermitian characteristic polynomial -/

/-!
These theorems consume the characteristic matrix of the 7-regular H16
defect block, for which `μ` is an actual eigenvalue and the nonprincipal raw
root-square trace is `63`.  This is distinct from the two-regular cycle
operator whose simultaneous eigenvalue `α` satisfies `μ = 7-α²`.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- The integer coefficient expression used by the cycle-primary ledger is
the actual complex root-square sum after base change. -/
theorem integerMonic_complexRootPowerSum_two
    {f : ℤ[X]} (hf : f.Monic) (hdeg : 2 ≤ f.natDegree) :
    complexRootPowerSum (f.map (Int.castRingHom ℂ)) 2 =
      (monicRootSquareMoment f f.natDegree : ℂ) := by
  have h := complexRootPowerSum_two_eq_coeff
    (p := f.map (Int.castRingHom ℂ)) (hf.map _) (by
      rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
      exact hdeg)
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective] at h
  simpa [monicRootSquareMoment, coeff_map] using h

theorem cycleDefectCubicSeven_complexRootPowerSum_two :
    complexRootPowerSum
      (cycleDefectCubicSeven.map (Int.castRingHom ℂ)) 2 = 90 := by
  rw [integerMonic_complexRootPowerSum_two cycleDefectCubicSeven_monic (by
    rw [cycleDefectCubicSeven_natDegree]
    norm_num)]
  rw [cycleDefectCubicSeven_natDegree, cycleDefectCubicSeven_squareMoment]
  norm_num

theorem cycleDefectCubicNine_complexRootPowerSum_two :
    complexRootPowerSum
      (cycleDefectCubicNine.map (Int.castRingHom ℂ)) 2 = 81 := by
  rw [integerMonic_complexRootPowerSum_two cycleDefectCubicNine_monic (by
    rw [cycleDefectCubicNine_natDegree]
    norm_num)]
  rw [cycleDefectCubicNine_natDegree, cycleDefectCubicNine_squareMoment]
  norm_num

theorem cycleDefectQuinticEleven_complexRootPowerSum_two :
    complexRootPowerSum
      (cycleDefectQuinticEleven.map (Int.castRingHom ℂ)) 2 = 144 := by
  rw [integerMonic_complexRootPowerSum_two cycleDefectQuinticEleven_monic (by
    rw [cycleDefectQuinticEleven_natDegree]
    norm_num)]
  rw [cycleDefectQuinticEleven_natDegree, cycleDefectQuinticEleven_squareMoment]
  norm_num

theorem cycleDefectSexticThirteen_complexRootPowerSum_two :
    complexRootPowerSum
      (cycleDefectSexticThirteen.map (Int.castRingHom ℂ)) 2 = 171 := by
  rw [integerMonic_complexRootPowerSum_two cycleDefectSexticThirteen_monic (by
    rw [cycleDefectSexticThirteen_natDegree]
    norm_num)]
  rw [cycleDefectSexticThirteen_natDegree, cycleDefectSexticThirteen_squareMoment]
  norm_num

/-- A characteristic factor whose second root moment exceeds `63` cannot
occur in a Hermitian matrix with square-trace budget at most `63`. -/
theorem false_of_large_secondMoment_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {f q : ℂ[X]} (hf : f ≠ 0) (hq : q ≠ 0)
    (hfactor : A.charpoly = f * q)
    (hmoment : 63 < (complexRootPowerSum f 2).re)
    (htrace : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  have hle := complexRootPowerSum_factor_two_re_le_trace_sq
    A hA hf hq hfactor
  linarith

/-- Rational divisibility is enough for the Hermitian moment terminal:
base change turns the rational cofactor into the required complex
characteristic factorization. -/
theorem false_of_large_secondMoment_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ)
    {f : ℤ[X]} (hfmonic : f.Monic)
    (hdvd : f.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (hmoment : 63 <
      (complexRootPowerSum (f.map (Int.castRingHom ℂ)) 2).re)
    (htrace : (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    False := by
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact D.charpoly_monic.ne_zero hq
  have hqmap0 : q.map (algebraMap ℚ ℂ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hq0
  have hfactor :
      (D.map (algebraMap ℚ ℂ)).charpoly =
        f.map (Int.castRingHom ℂ) * q.map (algebraMap ℚ ℂ) := by
    rw [Matrix.charpoly_map, hq, Polynomial.map_mul, Polynomial.map_map]
    congr 1
  exact false_of_large_secondMoment_charpoly_factor
    (D.map (algebraMap ℚ ℂ)) hD (hfmonic.map _).ne_zero hqmap0
      hfactor hmoment htrace

theorem false_of_cycleDefectCubicSeven_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ)
    (hdvd : cycleDefectCubicSeven.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    False := by
  apply false_of_large_secondMoment_dvd_rational_charpoly D
    cycleDefectCubicSeven_monic hdvd hD
  · rw [cycleDefectCubicSeven_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectCubicNine_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ)
    (hdvd : cycleDefectCubicNine.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    False := by
  apply false_of_large_secondMoment_dvd_rational_charpoly D
    cycleDefectCubicNine_monic hdvd hD
  · rw [cycleDefectCubicNine_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectQuinticEleven_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ)
    (hdvd : cycleDefectQuinticEleven.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    False := by
  apply false_of_large_secondMoment_dvd_rational_charpoly D
    cycleDefectQuinticEleven_monic hdvd hD
  · rw [cycleDefectQuinticEleven_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectSexticThirteen_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ)
    (hdvd : cycleDefectSexticThirteen.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) :
    False := by
  apply false_of_large_secondMoment_dvd_rational_charpoly D
    cycleDefectSexticThirteen_monic hdvd hD
  · rw [cycleDefectSexticThirteen_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectCubicSeven_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {q : ℂ[X]} (hq : q ≠ 0)
    (hfactor : A.charpoly =
      cycleDefectCubicSeven.map (Int.castRingHom ℂ) * q)
    (htrace : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  apply false_of_large_secondMoment_charpoly_factor A hA
    (cycleDefectCubicSeven_monic.map _).ne_zero hq hfactor
  · rw [cycleDefectCubicSeven_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectCubicNine_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {q : ℂ[X]} (hq : q ≠ 0)
    (hfactor : A.charpoly =
      cycleDefectCubicNine.map (Int.castRingHom ℂ) * q)
    (htrace : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  apply false_of_large_secondMoment_charpoly_factor A hA
    (cycleDefectCubicNine_monic.map _).ne_zero hq hfactor
  · rw [cycleDefectCubicNine_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectQuinticEleven_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {q : ℂ[X]} (hq : q ≠ 0)
    (hfactor : A.charpoly =
      cycleDefectQuinticEleven.map (Int.castRingHom ℂ) * q)
    (htrace : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  apply false_of_large_secondMoment_charpoly_factor A hA
    (cycleDefectQuinticEleven_monic.map _).ne_zero hq hfactor
  · rw [cycleDefectQuinticEleven_complexRootPowerSum_two]
    norm_num
  · exact htrace

theorem false_of_cycleDefectSexticThirteen_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {q : ℂ[X]} (hq : q ≠ 0)
    (hfactor : A.charpoly =
      cycleDefectSexticThirteen.map (Int.castRingHom ℂ) * q)
    (htrace : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  apply false_of_large_secondMoment_charpoly_factor A hA
    (cycleDefectSexticThirteen_monic.map _).ne_zero hq hfactor
  · rw [cycleDefectSexticThirteen_complexRootPowerSum_two]
    norm_num
  · exact htrace

end

end Erdos85
