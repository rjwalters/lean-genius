import Proofs.Erdos85SevenRegularNearTwinCommutingPropagation
import Proofs.Erdos85BinarySquareRegularParity

/-! # Aggregate owner-overlap identity at a near-twin pair -/

namespace Erdos85

noncomputable section

/-- Abstract aggregate identity behind the four owner-color sign patterns.
If the owner matrices resolve `J-I-D` and `x,y` are a sparse-row pair for
`D`, then their total owner-overlap imbalance at `z` is supported only on
`x,y` and the private pair `p,q`. -/
theorem ownerResolution_sparseRow_aggregate
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (O : I → Matrix V V ℤ) (D J : Matrix V V ℤ)
    (x y p q : V)
    (hresolve : ∑ c, O c = J - 1 - D)
    (hJrows : ∀ z : V, (J * D) x z = (J * D) y z)
    (hrow : ∀ w : V,
      D x w - D y w = (if w = p then 1 else 0) - (if w = q then 1 else 0)) :
    ∀ z : V,
      (∑ c : I, ((O c * D) x z - (O c * D) y z)) =
        -(D x z - D y z) - (D p z - D q z) := by
  intro z
  have hDD : (D * D) x z - (D * D) y z = D p z - D q z := by
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, hrow]
    have hsigned :
        (∑ w : V,
          ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * D w z) =
          D p z - D q z := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    exact hsigned
  calc
    (∑ c : I, ((O c * D) x z - (O c * D) y z)) =
        (∑ c : I, (O c * D) x z) - (∑ c : I, (O c * D) y z) := by
      rw [Finset.sum_sub_distrib]
    _ = ((∑ c : I, O c) * D) x z - ((∑ c : I, O c) * D) y z := by
      rw [Finset.sum_mul]
      simp only [Matrix.sum_apply]
    _ = ((J - 1 - D) * D) x z - ((J - 1 - D) * D) y z := by
      rw [hresolve]
    _ = ((J * D - D - D * D) x z) -
        ((J * D - D - D * D) y z) := by
      rw [sub_mul, sub_mul, Matrix.one_mul]
    _ = -(D x z - D y z) - (D p z - D q z) := by
      simp only [Matrix.sub_apply]
      rw [hJrows z]
      linarith

/-- Graph-facing aggregate for the order-64 branch.  The total imbalance over
all owner colors is an explicit sum of two signed Boolean defect differences. -/
theorem orderSixtyFour_nearTwin_sum_ownerOverlapDifference
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    {x y : Fin 64}
    (hcommon : ((secondOrderDefectGraph G).neighborFinset x ∩
      (secondOrderDefectGraph G).neighborFinset y).card = 6) :
    ∃ p q : Fin 64, p ≠ q ∧ ∀ z : Fin 64,
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
            (secondOrderDefectGraph G).adjMatrix ℤ) x z -
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
            (secondOrderDefectGraph G).adjMatrix ℤ) y z)) =
        -((secondOrderDefectGraph G).adjMatrix ℤ x z -
            (secondOrderDefectGraph G).adjMatrix ℤ y z) -
          ((secondOrderDefectGraph G).adjMatrix ℤ p z -
            (secondOrderDefectGraph G).adjMatrix ℤ q z) := by
  let D := secondOrderDefectGraph G
  obtain ⟨p, q, hpq, hrow⟩ :=
    sevenRegular_nearTwin_exists_sparse_adjMatrix_rowDifference
      D (by
        intro z
        have hcensus : Fintype.card (Fin 64) = 8 * (8 - 1) + 3 + (8 - 3) := by
          norm_num
        have h := secondOrderDefectGraph_degree_eq_excess_add_two
          G hfree hreg hcensus z
        change D.degree z = (8 - 3) + 2 at h
        norm_num at h ⊢
        exact h) hcommon
  refine ⟨p, q, hpq, ?_⟩
  apply ownerResolution_sparseRow_aggregate
    (fun c => (componentOwnerGraph G D c).adjMatrix ℤ)
    (D.adjMatrix ℤ) (Matrix.of fun _ _ => (1 : ℤ)) x y p q
  · exact sum_componentOwnerGraph_adjMatrix_eq_ones_sub_one_sub_secondOrderDefect
      G hfree
  · intro z
    simp [Matrix.mul_apply]
  · exact hrow

end

end Erdos85
