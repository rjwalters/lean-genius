import Proofs.Erdos85MooreFriendship
import Proofs.Erdos85OrderSixtyFourComponentComplexGram

/-! # Zero mixed trace separates two graph relations -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If `tr(A_H² A_R)=0`, every edge of `R` joins vertices with no common
`H`-neighbor.  This is the pointwise combinatorial content of the vanishing
mixed trace produced by the H16 Gram ledger. -/
theorem no_commonNeighbor_of_trace_adj_sq_mul_adj_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (htrace : Matrix.trace
      ((H.adjMatrix ℤ * H.adjMatrix ℤ) * R.adjMatrix ℤ) = 0)
    {x y : V} (hRxy : R.Adj x y) :
    (H.neighborFinset x ∩ H.neighborFinset y).card = 0 := by
  have hsum :
      Matrix.trace ((H.adjMatrix ℤ * H.adjMatrix ℤ) * R.adjMatrix ℤ) =
        ∑ i : V, ∑ j : V,
          ((H.neighborFinset i ∩ H.neighborFinset j).card : ℤ) *
            R.adjMatrix ℤ j i := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [adjMatrix_sq_apply_eq_card_common]
  rw [hsum] at htrace
  have houterNonneg : ∀ i ∈ (Finset.univ : Finset V),
      0 ≤ ∑ j : V,
        ((H.neighborFinset i ∩ H.neighborFinset j).card : ℤ) *
          R.adjMatrix ℤ j i := by
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hji : R.Adj j i <;>
      simp [SimpleGraph.adjMatrix_apply, hji]
  have houter := (Finset.sum_eq_zero_iff_of_nonneg houterNonneg).mp htrace
    x (Finset.mem_univ x)
  have hinnerNonneg : ∀ j ∈ (Finset.univ : Finset V),
      0 ≤ ((H.neighborFinset x ∩ H.neighborFinset j).card : ℤ) *
        R.adjMatrix ℤ j x := by
    intro j _
    by_cases hjx : R.Adj j x <;>
      simp [SimpleGraph.adjMatrix_apply, hjx]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hinnerNonneg).mp houter
    y (Finset.mem_univ y)
  have hRyx : R.Adj y x := (R.adj_comm y x).mpr hRxy
  have hcardZ :
      ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) = 0 := by
    simpa [SimpleGraph.adjMatrix_apply, hRyx] using hterm
  omega

/-- Complex-matrix wrapper matching the H16 spectral calculation. -/
theorem no_commonNeighbor_of_trace_complex_adj_sq_mul_adj_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (htrace : Matrix.trace
      ((H.adjMatrix ℂ * H.adjMatrix ℂ) * R.adjMatrix ℂ) = 0)
    {x y : V} (hRxy : R.Adj x y) :
    (H.neighborFinset x ∩ H.neighborFinset y).card = 0 := by
  have hmap :
      (((H.adjMatrix ℤ * H.adjMatrix ℤ) * R.adjMatrix ℤ).map
          (Int.castRingHom ℂ)) =
        (H.adjMatrix ℂ * H.adjMatrix ℂ) * R.adjMatrix ℂ := by
    simp only [Matrix.map_mul, adjMatrix_map_intCast]
  have htmap := congrArg Matrix.trace hmap
  have htzero :
      Matrix.trace ((H.adjMatrix ℤ * H.adjMatrix ℤ) * R.adjMatrix ℤ) = 0 := by
    have hc :
        ((Matrix.trace
          ((H.adjMatrix ℤ * H.adjMatrix ℤ) * R.adjMatrix ℤ) : ℤ) : ℂ) = 0 := by
      rw [← htrace]
      simpa [Matrix.trace, Matrix.diag] using htmap
    exact_mod_cast hc
  exact no_commonNeighbor_of_trace_adj_sq_mul_adj_eq_zero
    H R htzero hRxy

end

end Erdos85
