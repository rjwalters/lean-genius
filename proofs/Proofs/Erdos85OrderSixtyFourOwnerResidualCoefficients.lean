import Proofs.Erdos85OrderSixtyFourOwnerCharpolyFactor
import Proofs.Erdos85AdjacencyCharpolySecondCoeff

/-!
# Leading coefficients of the order-64 owner residual

For a normalized size-two owner, write
`charpoly(O) = (X+2)^48 r`, with `r` monic of degree 16.  The zero adjacency
trace and the exact edge count of the 14-regular owner determine the first
two residual coefficients:

* `r.coeff 15 = -96`;
* `r.coeff 14 = 4256`.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- The complete leading-coefficient ledger for the degree-16 owner
residual. -/
theorem orderSixtyFour_sizeSixteen_componentOwnerGraph_exists_residual_coefficients
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    ∃ r : ℝ[X], r.Monic ∧ r.natDegree = 16 ∧
      ((componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ).charpoly =
          (X + C (2 : ℝ)) ^ 48 * r ∧
      r.coeff 15 = -96 ∧ r.coeff 14 = 4256 := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  obtain ⟨r, hrMonic, hrDegree, hr⟩ :=
    orderSixtyFour_sizeSixteen_componentOwnerGraph_exists_residual_charpoly
      G hfree hreg hcard c hc
  have hfactorMonic : ((X + C (2 : ℝ)) ^ 48).Monic :=
    (monic_X_add_C 2).pow 48
  have hcharNext : (O.adjMatrix ℝ).charpoly.nextCoeff = 0 := by
    rw [← neg_eq_zero, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
    simp [Matrix.trace]
  have hfactorNext : ((X + C (2 : ℝ)) ^ 48).nextCoeff = 96 := by
    rw [(monic_X_add_C 2).nextCoeff_pow, nextCoeff_X_add_C]
    norm_num
  have hrNext : r.nextCoeff = -96 := by
    have hnext := congrArg Polynomial.nextCoeff hr
    rw [hcharNext, hfactorMonic.nextCoeff_mul hrMonic,
      hfactorNext] at hnext
    linarith
  have hrCoeff15 : r.coeff 15 = -96 := by
    simpa [Polynomial.nextCoeff, hrDegree] using hrNext
  have hOreg : ∀ x, O.degree x = 14 := by
    intro x
    have hx := binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by omega) hreg (by simpa using hcard)
        c (m_c := 2) (by simpa using hc) x
    simpa [O] using hx
  have hcharCoeffQ : (O.adjMatrix ℚ).charpoly.coeff 62 = -448 := by
    have htwo := twice_adjMatrix_charpoly_secondCoeff_eq_neg_sum_degrees
      O (by simpa [hcard] : 2 ≤ Fintype.card V)
    have hsum : (∑ x : V, (O.degree x : ℚ)) = 896 := by
      simp_rw [hOreg]
      simp only [Finset.sum_const, Finset.card_univ, hcard]
      norm_num
    rw [hsum] at htwo
    rw [hcard] at htwo
    norm_num at htwo
    linarith
  have hadjMap : (O.adjMatrix ℚ).map (Rat.castHom ℝ) = O.adjMatrix ℝ := by
    ext x y
    by_cases hxy : O.Adj x y <;>
      simp [SimpleGraph.adjMatrix_apply, hxy]
  have hcharMap := Matrix.charpoly_map (O.adjMatrix ℚ) (Rat.castHom ℝ)
  rw [hadjMap] at hcharMap
  have hcharCoeffReal : (O.adjMatrix ℝ).charpoly.coeff 62 = -448 := by
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 62) hcharMap
    rw [Polynomial.coeff_map, hcharCoeffQ] at hcoeff
    norm_num at hcoeff
    exact hcoeff
  have hproductCoeff : (((X + C (2 : ℝ)) ^ 48) * r).coeff 62 =
      4512 + 96 * r.coeff 15 + r.coeff 14 := by
    have hlead : r.coeff 16 = 1 := by
      rw [← hrDegree]
      exact hrMonic.coeff_natDegree
    have hchoose : Nat.choose 48 46 = 1128 := by decide
    rw [Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Polynomial.coeff_X_add_C_pow,
      Polynomial.coeff_eq_zero_of_natDegree_lt, hrDegree,
      Finset.sum_range_succ, hlead, hchoose]
  have hrCoeff14 : r.coeff 14 = 4256 := by
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 62) hr
    rw [hcharCoeffReal, hproductCoeff, hrCoeff15] at hcoeff
    linarith
  exact ⟨r, hrMonic, hrDegree, hr, hrCoeff15, hrCoeff14⟩

end

end Erdos85
