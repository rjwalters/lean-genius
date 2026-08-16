import Proofs.Erdos85OrderFortyNineResidualRootMoments
import Proofs.Erdos85ResidualNewtonCoefficients
import Proofs.Erdos85OrderFortyNineIncidence

/-!
# Exact coefficients of the order-49 residual factor

The certified residual root moments determine its second and fourth
coefficients.  The formulas below remain denominator-free over `ℚ`.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

theorem exists_orderFortyNineSeven_residualCharpoly_coefficients
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    ∃ Q : ℚ[X],
      Q.Monic ∧
      (G.adjMatrix ℚ).charpoly =
        (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1) * Q ∧
      Q.natDegree = 49 - 2 * ((squareOrderHighVertices G 7).card - 1) ∧
      Q.nextCoeff = 0 ∧
      2 * Q.coeff (Q.natDegree - 2) =
        -(357 - 13 * ((squareOrderHighVertices G 7).card : ℚ)) ∧
      8 * Q.coeff (Q.natDegree - 4) =
        169 * ((squareOrderHighVertices G 7).card : ℚ) ^ 2 -
          9144 * ((squareOrderHighVertices G 7).card : ℚ) + 118335 := by
  let H := squareOrderHighVertices G 7
  obtain ⟨Q, hQmonic, hfactor, hdegree, hnext, hrootTwo, hrootFour⟩ :=
    exists_orderFortyNineSeven_residualCharpoly_rootMoments
      G hfree hmin hcover hcard ha
  have hHle : H.card ≤ 9 := by
    simpa [H, squareOrderHighVertices, orderFortyNineHighVertices] using
      orderFortyNine_card_high_le_nine G hfree hmin hcard
  have hdegreeH : Q.natDegree = 49 - 2 * (H.card - 1) := by
    simpa [H] using hdegree
  have hQdegree : 4 ≤ Q.natDegree := by
    rw [hdegreeH]
    omega
  let QC : ℂ[X] := Q.map (algebraMap ℚ ℂ)
  have hQCmonic : QC.Monic := hQmonic.map (algebraMap ℚ ℂ)
  have hQCdegree : QC.natDegree = Q.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℚ ℂ).injective Q
  have hQCnext : QC.nextCoeff = 0 := by
    dsimp [QC]
    rw [Polynomial.nextCoeff_map (algebraMap ℚ ℂ).injective, hnext]
    simp
  have hnewton := monic_coeff_even_newton_of_nextCoeff_zero
    QC hQCmonic (by omega) hQCnext
  have hcoeffTwoC :
      2 * (Q.coeff (Q.natDegree - 2) : ℂ) =
        -(357 - 13 * (H.card : ℂ)) := by
    have hrootTwoH : complexRootPowerSum QC 2 =
        357 - 13 * (H.card : ℂ) := by
      simpa [QC, H] using hrootTwo
    rw [hrootTwoH] at hnewton
    simpa [QC, hQCdegree] using hnewton.1
  have hcoeffFourC :
      8 * (Q.coeff (Q.natDegree - 4) : ℂ) =
        169 * (H.card : ℂ) ^ 2 - 9144 * (H.card : ℂ) + 118335 := by
    have hrootTwoH : complexRootPowerSum QC 2 =
        357 - 13 * (H.card : ℂ) := by
      simpa [QC, H] using hrootTwo
    have hrootFourH : complexRootPowerSum QC 4 =
        4557 - 69 * (H.card : ℂ) := by
      simpa [QC, H] using hrootFour
    rw [hrootTwoH, hrootFourH] at hnewton
    have hfour := hnewton.2
    simp [QC, hQCdegree] at hfour
    linear_combination 2 * hfour -
      (357 - 13 * (H.card : ℂ)) * hcoeffTwoC
  refine ⟨Q, hQmonic, hfactor, hdegree, hnext, ?_, ?_⟩
  · dsimp [H] at hcoeffTwoC ⊢
    exact_mod_cast hcoeffTwoC
  · dsimp [H] at hcoeffFourC ⊢
    exact_mod_cast hcoeffFourC

end

end Erdos85
