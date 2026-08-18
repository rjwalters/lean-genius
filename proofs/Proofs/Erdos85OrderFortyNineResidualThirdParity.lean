import Proofs.Erdos85OrderFortyNineIntegralResidual
import Proofs.Erdos85AdjacencyCharpolyThirdParity

/-!
# Third-coefficient parity of the integral residual

The quadratic high-sector factor has only even offsets from its leading
term.  Since both factors have zero next coefficient, the third coefficient
of the ambient characteristic polynomial is exactly the third coefficient
of the residual.  The ambient parity theorem therefore descends to the
integral residual factor.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

private theorem coeff_one_and_three_pow_eq_zero
    {R : Type*} [CommRing R] (p : R[X])
    (h₁ : p.coeff 1 = 0) (h₃ : p.coeff 3 = 0) (k : ℕ) :
    (p ^ k).coeff 1 = 0 ∧ (p ^ k).coeff 3 = 0 := by
  induction k with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
      rw [pow_succ]
      constructor
      · rw [coeff_mul]
        have ha : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
        rw [ha]
        simp [ih.1, h₁]
      · rw [coeff_mul]
        have ha : Finset.antidiagonal 3 =
            {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
        rw [ha]
        simp [ih.1, ih.2, h₁, h₃]

private theorem reverse_quadratic_pow_coeff_one_three_zero (k : ℕ) :
    let F : ℤ[X] := (X ^ 2 - C 7) ^ k
    F.reverse.coeff 1 = 0 ∧ F.reverse.coeff 3 = 0 := by
  dsimp only
  have hbase : (X ^ 2 - C (7 : ℤ)).Monic :=
    ((isMonicOfDegree_X_pow ℤ 2).sub (by simp)).monic
  have hreverse : ((X ^ 2 - C (7 : ℤ)) ^ k).reverse =
      ((X ^ 2 - C (7 : ℤ)).reverse) ^ k := by
    induction k with
    | zero => simp [Polynomial.reverse]
    | succ k ih =>
        rw [pow_succ, reverse_mul_of_domain, ih]
        simp [pow_succ]
  rw [hreverse]
  apply coeff_one_and_three_pow_eq_zero
  · have hd : (X ^ 2 - C (7 : ℤ)).natDegree = 2 :=
      ((isMonicOfDegree_X_pow ℤ 2).sub (by simp)).natDegree_eq
    rw [coeff_reverse, revAt_le (by omega), hd]
    simp
  · have hd : (X ^ 2 - C (7 : ℤ)).natDegree = 2 :=
      ((isMonicOfDegree_X_pow ℤ 2).sub (by simp)).natDegree_eq
    rw [coeff_reverse]
    rw [revAt_eq_self_of_lt (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem exists_monic_integral_orderFortyNineSeven_residualCharpoly_thirdParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    ∃ R : ℤ[X],
      R.Monic ∧
      (G.adjMatrix ℤ).charpoly =
        (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1) * R ∧
      R.natDegree = 49 - 2 * ((squareOrderHighVertices G 7).card - 1) ∧
      R.nextCoeff = 0 ∧
      (2 : ℤ) ∣ R.coeff (R.natDegree - 3) := by
  obtain ⟨R, hRmonic, hfactor, hdegree, hnext, _hc₂, _hc₄⟩ :=
    exists_monic_integral_orderFortyNineSeven_residualCharpoly
      G hfree hmin hcover hcard ha
  let P : ℤ[X] := (G.adjMatrix ℤ).charpoly
  let F : ℤ[X] :=
    (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1)
  have hPmonic : P.Monic := (G.adjMatrix ℤ).charpoly_monic
  have hFbase : (X ^ 2 - C (7 : ℤ)).Monic :=
    ((isMonicOfDegree_X_pow ℤ 2).sub (by simp)).monic
  have hFmonic : F.Monic := hFbase.pow _
  have hrevFactor : P.reverse = F.reverse * R.reverse := by
    have hfactorPF : P = F * R := by simpa [P, F] using hfactor
    rw [hfactorPF]
    apply reverse_mul
    rw [hFmonic.leadingCoeff, hRmonic.leadingCoeff]
    norm_num
  have hFcoeff := reverse_quadratic_pow_coeff_one_three_zero
    ((squareOrderHighVertices G 7).card - 1)
  change F.reverse.coeff 1 = 0 ∧ F.reverse.coeff 3 = 0 at hFcoeff
  have hRrevOne : R.reverse.coeff 1 = 0 := by simpa using hnext
  have hcoeffReverse : P.reverse.coeff 3 = R.reverse.coeff 3 := by
    have hc := congrArg (fun p : ℤ[X] => p.coeff 3) hrevFactor
    rw [coeff_mul] at hc
    have ha : Finset.antidiagonal 3 =
        {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
    rw [ha] at hc
    simp [hFcoeff.1, hFcoeff.2, hRrevOne,
      hFmonic.leadingCoeff] at hc
    simpa [hRmonic.leadingCoeff] using hc
  have hPdegree : P.natDegree = 49 := by
    dsimp [P]
    simpa [hcard] using (G.adjMatrix ℤ).charpoly_natDegree_eq_dim
  have hHle : (squareOrderHighVertices G 7).card ≤ 9 := by
    simpa [squareOrderHighVertices, orderFortyNineHighVertices] using
      orderFortyNine_card_high_le_nine G hfree hmin hcard
  have hRdegreeThree : 3 ≤ R.natDegree := by
    rw [hdegree]
    omega
  have hcoeff : P.coeff (49 - 3) = R.coeff (R.natDegree - 3) := by
    rw [coeff_reverse, coeff_reverse,
      revAt_le hRdegreeThree, revAt_le (by omega : 3 ≤ P.natDegree),
      hPdegree] at hcoeffReverse
    exact hcoeffReverse
  refine ⟨R, hRmonic, hfactor, hdegree, hnext, ?_⟩
  rw [← hcoeff]
  simpa [P, hcard] using
    two_dvd_adjMatrix_charpoly_thirdCoeff G (by omega : 3 ≤ Fintype.card V)

end

end Erdos85
