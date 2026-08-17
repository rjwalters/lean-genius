import Proofs.Erdos85OrderSixtyFourOwnerResidualCoefficients

/-!
# Third coefficient of the order-64 owner residual

A three-vertex principal adjacency minor is `2` exactly for a triangle and
zero otherwise.  This gives an exact, reusable third characteristic
coefficient formula.  Applied to the owner factorization, it identifies the
degree-13 residual coefficient as an affine function of the owner triangle
count.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- Three-vertex sets whose rational principal adjacency minor is `2`.
These are exactly the triangles; the minor-based definition makes the
characteristic-coefficient interface immediate. -/
def adjacencyTriangleMinorFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  (Finset.univ.powersetCard 3).filter fun s =>
    ((G.adjMatrix ℚ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V)).det = 2

private theorem det_adjMatrix_submatrix_card_three_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : s.card = 3) :
    ((G.adjMatrix ℚ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V)).det = 0 ∨
    ((G.adjMatrix ℚ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V)).det = 2 := by
  classical
  let e : s ≃ Fin 3 := s.equivFinOfCardEq hs
  rw [← Matrix.det_reindex_self e
    ((G.adjMatrix ℚ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V))]
  rw [Matrix.det_fin_three]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    SimpleGraph.adjMatrix_apply]
  by_cases h₀₁ : G.Adj (e.symm 0).1 (e.symm 1).1 <;>
    by_cases h₀₂ : G.Adj (e.symm 0).1 (e.symm 2).1 <;>
    by_cases h₁₂ : G.Adj (e.symm 1).1 (e.symm 2).1 <;>
    simp [h₀₁, h₀₂, h₁₂, G.adj_comm] <;> norm_num

/-- Exact third adjacency coefficient: minus twice the number of
three-vertex principal minors equal to `2` (equivalently, triangles). -/
theorem adjMatrix_charpoly_thirdCoeff_eq_neg_two_mul_triangleMinorCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V) :
    (G.adjMatrix ℚ).charpoly.coeff (Fintype.card V - 3) =
      -2 * (adjacencyTriangleMinorFinset G).card := by
  rw [Matrix.charpoly_coeff_eq_sum_minors (G.adjMatrix ℚ) 3 hcard]
  norm_num
  have hminor :
      (∑ s ∈ Finset.univ.powersetCard 3,
          ((G.adjMatrix ℚ).submatrix
            (Subtype.val : s → V) (Subtype.val : s → V)).det) =
        ∑ s ∈ Finset.univ.powersetCard 3,
          if s ∈ adjacencyTriangleMinorFinset G then (2 : ℚ) else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    have hcardS := (Finset.mem_powersetCard.mp hs).2
    have hcases := det_adjMatrix_submatrix_card_three_eq_zero_or_two
      G s hcardS
    rcases hcases with hzero | htwo
    · have hnot : s ∉ adjacencyTriangleMinorFinset G := by
        simp [adjacencyTriangleMinorFinset, hs, hzero]
      simp [hzero, hnot]
    · have hmem : s ∈ adjacencyTriangleMinorFinset G := by
        simp [adjacencyTriangleMinorFinset, hs, htwo]
      simp [htwo, hmem]
  rw [hminor]
  have hfilter : (Finset.univ.powersetCard 3).filter
      (fun s => s ∈ adjacencyTriangleMinorFinset G) =
      adjacencyTriangleMinorFinset G := by
    ext s
    simp [adjacencyTriangleMinorFinset]
  rw [show (∑ s ∈ Finset.univ.powersetCard 3,
      if s ∈ adjacencyTriangleMinorFinset G then (2 : ℚ) else 0) =
      2 * (adjacencyTriangleMinorFinset G).card by
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp
    ring]

/-- For `charpoly(O)=(X+2)^48 r`, the third residual coefficient is
`-113792 - 2T`, where `T` is the owner triangle count. -/
theorem orderSixtyFour_sizeSixteen_componentOwnerGraph_exists_residual_thirdCoefficient
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
      r.coeff 15 = -96 ∧ r.coeff 14 = 4256 ∧
      r.coeff 13 = -113792 - 2 *
        (adjacencyTriangleMinorFinset
          (componentOwnerGraph G (secondOrderDefectGraph G) c)).card := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  obtain ⟨r, hrMonic, hrDegree, hr, hr15, hr14⟩ :=
    orderSixtyFour_sizeSixteen_componentOwnerGraph_exists_residual_coefficients
      G hfree hreg hcard c hc
  have hcharCoeffQ : (O.adjMatrix ℚ).charpoly.coeff 61 =
      -2 * (adjacencyTriangleMinorFinset O).card := by
    have h := adjMatrix_charpoly_thirdCoeff_eq_neg_two_mul_triangleMinorCount
      O (by simpa [hcard] : 3 ≤ Fintype.card V)
    rw [hcard] at h
    norm_num at h
    ring_nf at h ⊢
    exact h
  have hadjMap : (O.adjMatrix ℚ).map (Rat.castHom ℝ) = O.adjMatrix ℝ := by
    ext x y
    by_cases hxy : O.Adj x y <;>
      simp [SimpleGraph.adjMatrix_apply, hxy]
  have hcharMap := Matrix.charpoly_map (O.adjMatrix ℚ) (Rat.castHom ℝ)
  rw [hadjMap] at hcharMap
  have hcharCoeffReal : (O.adjMatrix ℝ).charpoly.coeff 61 =
      -2 * (adjacencyTriangleMinorFinset O).card := by
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 61) hcharMap
    rw [Polynomial.coeff_map, hcharCoeffQ] at hcoeff
    exact_mod_cast hcoeff
  have hproductCoeff : (((X + C (2 : ℝ)) ^ 48) * r).coeff 61 =
      138368 + 4512 * r.coeff 15 + 96 * r.coeff 14 + r.coeff 13 := by
    have hlead : r.coeff 16 = 1 := by
      rw [← hrDegree]
      exact hrMonic.coeff_natDegree
    have hchoose : Nat.choose 48 45 = 17296 := by decide
    have hchoose' : Nat.choose 48 46 = 1128 := by decide
    rw [Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Polynomial.coeff_X_add_C_pow,
      Polynomial.coeff_eq_zero_of_natDegree_lt, hrDegree,
      Finset.sum_range_succ, hlead, hchoose, hchoose']
  have hr13 : r.coeff 13 = -113792 - 2 *
      (adjacencyTriangleMinorFinset O).card := by
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 61) hr
    rw [hcharCoeffReal, hproductCoeff, hr15, hr14] at hcoeff
    norm_num at hcoeff ⊢
    linarith
  exact ⟨r, hrMonic, hrDegree, hr, hr15, hr14, hr13⟩

end

end Erdos85
