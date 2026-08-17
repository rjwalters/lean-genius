import Proofs.Erdos85PolynomialSecondNewtonIdentity
import Proofs.Erdos85OrderSixtyFourCyclePrimaryMomentTerminal
import Proofs.Erdos85HermitianFactorSecondMoment

/-! # Cycle-primary moments inside a Hermitian characteristic polynomial -/

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
