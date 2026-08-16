import Proofs.Erdos85AdjacencySquareRayleigh
import Proofs.Erdos85EuclideanMatrixEigenroot
import Proofs.Erdos85OrderFortyNineResidualRootMoments
import Proofs.Erdos85QuadraticFactorRootTransfer

/-!
# A large real root of the order-49 residual polynomial
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

theorem exists_orderFortyNineSeven_residual_largeRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    ∃ (Q : ℚ[X]) (lambda : ℝ),
      Q.Monic ∧
      (G.adjMatrix ℚ).charpoly =
        (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1) * Q ∧
      Q.natDegree = 49 - 2 * ((squareOrderHighVertices G 7).card - 1) ∧
      Q.nextCoeff = 0 ∧
      complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 =
        357 - 13 * ((squareOrderHighVertices G 7).card : ℂ) ∧
      complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 =
        4557 - 69 * ((squareOrderHighVertices G 7).card : ℂ) ∧
      (Q.map (algebraMap ℚ ℝ)).IsRoot lambda ∧
      (Q.map (algebraMap ℚ ℝ)).Splits ∧
      lambda ∈ (Q.map (algebraMap ℚ ℝ)).roots ∧
      ((2401 : ℝ) + 15 * (squareOrderHighVertices G 7).card) / 49 ≤
        lambda ^ 2 := by
  obtain ⟨Q, hQmonic, hfactor, hdegree, hnext, hsecond, hfourth⟩ :=
    exists_orderFortyNineSeven_residualCharpoly_rootMoments
      G hfree hmin hcover hcard ha
  obtain ⟨lambda, hlambdaEig, hlambdaLower⟩ :=
    exists_orderFortyNine_adjMatrix_eigenvalue_sq_ge
      G hfree hmin hcover hcard
  have hroot : (G.adjMatrix ℝ).charpoly.IsRoot lambda :=
    Matrix.isRoot_charpoly_of_toEuclideanLin_hasEigenvalue
      (G.adjMatrix ℝ) lambda hlambdaEig
  have hadj : (G.adjMatrix ℚ).map (algebraMap ℚ ℝ) = G.adjMatrix ℝ := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  have hfactorR :
      (G.adjMatrix ℝ).charpoly =
        (X ^ 2 - C (7 : ℝ)) ^
          ((squareOrderHighVertices G 7).card - 1) *
            Q.map (algebraMap ℚ ℝ) := by
    have hm := congrArg (fun p : ℚ[X] => p.map (algebraMap ℚ ℝ)) hfactor
    rw [← Matrix.charpoly_map, hadj] at hm
    simpa using hm
  have hHpos : 1 ≤ (squareOrderHighVertices G 7).card :=
    Finset.one_le_card.mpr ⟨a, ha⟩
  have hlambdaNe : lambda ^ 2 ≠ (7 : ℝ) := by
    intro heq
    rw [heq] at hlambdaLower
    have : ((2416 : ℝ) / 49) ≤ 7 := by
      calc
        (2416 : ℝ) / 49 ≤
            ((2401 : ℝ) +
              15 * (squareOrderHighVertices G 7).card) / 49 := by
          have hn : 2416 ≤
              2401 + 15 * (squareOrderHighVertices G 7).card := by
            omega
          have hnR : (2416 : ℝ) ≤
              2401 + 15 * (squareOrderHighVertices G 7).card := by
            exact_mod_cast hn
          exact div_le_div_of_nonneg_right hnR (by norm_num)
        _ ≤ 7 := hlambdaLower
    norm_num at this
  have hQroot : (Q.map (algebraMap ℚ ℝ)).IsRoot lambda :=
    isRoot_residual_of_quadratic_pow_mul
      (P := (G.adjMatrix ℝ).charpoly)
      (Q := Q.map (algebraMap ℚ ℝ)) 7 lambda
      ((squareOrderHighVertices G 7).card - 1)
      hfactorR hroot hlambdaNe
  have hQmapNe : Q.map (algebraMap ℚ ℝ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective (algebraMap ℚ ℝ)
        (algebraMap ℚ ℝ).injective).ne hQmonic.ne_zero
  have hAherm : (G.adjMatrix ℝ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hQsplits : (Q.map (algebraMap ℚ ℝ)).Splits := by
    have hcharSplits := hAherm.splits_charpoly
    rw [hfactorR] at hcharSplits
    exact ((Polynomial.splits_mul
      (pow_ne_zero _ (X_pow_sub_C_ne_zero (by norm_num) (7 : ℝ)))
      hQmapNe).mp hcharSplits).2
  have hlambdaMem : lambda ∈ (Q.map (algebraMap ℚ ℝ)).roots :=
    (mem_roots hQmapNe).mpr hQroot
  exact ⟨Q, lambda, hQmonic, hfactor, hdegree, hnext,
    hsecond, hfourth, hQroot, hQsplits, hlambdaMem, hlambdaLower⟩

end

end Erdos85
