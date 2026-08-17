import Proofs.Erdos85CycleDefectFactorIrreducibility

/-! # Minimal-polynomial registry for H16 cycle defect roots -/

open Polynomial

namespace Erdos85

noncomputable section

theorem cycleDefectQuadraticFive_eq_minpoly
    (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ 2 - 11 * μ + 29 = 0) :
    cycleDefectQuadraticFive.map (Int.castRingHom ℚ) = minpoly ℚ μ := by
  apply minpoly.eq_of_irreducible_of_monic
    cycleDefectQuadraticFive_irreducible_rat
  · simpa [cycleDefectQuadraticFive, Polynomial.aeval_def] using hμ
  · exact cycleDefectQuadraticFive_monic.map _

theorem cycleDefectQuadraticSixteen_eq_minpoly
    (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ 2 - 10 * μ + 23 = 0) :
    cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ) = minpoly ℚ μ := by
  apply minpoly.eq_of_irreducible_of_monic
    cycleDefectQuadraticSixteen_irreducible_rat
  · simpa [cycleDefectQuadraticSixteen, Polynomial.aeval_def] using hμ
  · exact cycleDefectQuadraticSixteen_monic.map _

theorem cycleDefectCubicSeven_eq_minpoly
    (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ 3 - 16 * μ ^ 2 + 83 * μ - 139 = 0) :
    cycleDefectCubicSeven.map (Int.castRingHom ℚ) = minpoly ℚ μ := by
  apply minpoly.eq_of_irreducible_of_monic
    cycleDefectCubicSeven_irreducible_rat
  · simpa [cycleDefectCubicSeven, Polynomial.aeval_def] using hμ
  · exact cycleDefectCubicSeven_monic.map _

theorem cycleDefectCubicNine_eq_minpoly
    (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ 3 - 15 * μ ^ 2 + 72 * μ - 111 = 0) :
    cycleDefectCubicNine.map (Int.castRingHom ℚ) = minpoly ℚ μ := by
  apply minpoly.eq_of_irreducible_of_monic
    cycleDefectCubicNine_irreducible_rat
  · simpa [cycleDefectCubicNine, Polynomial.aeval_def] using hμ
  · exact cycleDefectCubicNine_monic.map _

theorem cycleDefectQuinticEleven_eq_minpoly
    (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ 5 - 26 * μ ^ 4 + 266 * μ ^ 3 - 1337 * μ ^ 2
      + 3298 * μ - 3191 = 0) :
    cycleDefectQuinticEleven.map (Int.castRingHom ℚ) = minpoly ℚ μ := by
  apply minpoly.eq_of_irreducible_of_monic
    cycleDefectQuinticEleven_irreducible_rat
  · simpa [cycleDefectQuinticEleven, Polynomial.aeval_def] using hμ
  · exact cycleDefectQuinticEleven_monic.map _

theorem cycleDefectSexticThirteen_eq_minpoly
    (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ 6 - 31 * μ ^ 5 + 395 * μ ^ 4 - 2646 * μ ^ 3
      + 9821 * μ ^ 2 - 19138 * μ + 15289 = 0) :
    cycleDefectSexticThirteen.map (Int.castRingHom ℚ) = minpoly ℚ μ := by
  apply minpoly.eq_of_irreducible_of_monic
    cycleDefectSexticThirteen_irreducible_rat
  · simpa [cycleDefectSexticThirteen, Polynomial.aeval_def] using hμ
  · exact cycleDefectSexticThirteen_monic.map _

end

end Erdos85
