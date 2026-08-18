import Proofs.Erdos85SevenRegularCodegreeFourNormalization
import Proofs.Erdos85SevenRegularNearTwinLiteCommutingBalance

/-! # Commuting balance for codegree-four pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_mem_indicator_mul_codegreeFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (f : V → ℤ) :
    (∑ w : V, (if w ∈ P then 1 else 0) * f w) = ∑ w ∈ P, f w := by
  calc
    (∑ w : V, (if w ∈ P then 1 else 0) * f w) =
        ∑ w : V, if w ∈ P then f w else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      split <;> simp_all
    _ = ∑ w ∈ P, f w := by
      rw [← Finset.sum_filter]
      simp

/-- Exact integral adjacency-row form of the private-triple normalization. -/
theorem sevenRegular_codegreeFour_exists_sparse_adjMatrix_rowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 4) :
    ∃ P Q : Finset V,
      P.card = 3 ∧ Q.card = 3 ∧ Disjoint P Q ∧ ∀ w : V,
      D.adjMatrix ℤ x w - D.adjMatrix ℤ y w =
        (if w ∈ P then 1 else 0) - (if w ∈ Q then 1 else 0) := by
  obtain ⟨P, Q, hP, hQ, hPeq, hQeq, hdisj, _⟩ :=
    sevenRegular_codegreeFour_privateTriple_normalization D hreg hcommon
  refine ⟨P, Q, hP, hQ, hdisj, ?_⟩
  intro w
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  have hPmem : w ∈ P ↔ D.Adj x w ∧ ¬D.Adj y w := by
    rw [hPeq, Finset.mem_sdiff]
    simp only [SimpleGraph.mem_neighborFinset]
  have hQmem : w ∈ Q ↔ D.Adj y w ∧ ¬D.Adj x w := by
    rw [hQeq, Finset.mem_sdiff]
    simp only [SimpleGraph.mem_neighborFinset]
  by_cases hx : D.Adj x w <;> by_cases hy : D.Adj y w <;>
    simp_all

/-- Private-triple sum form of codegree-four commutation. -/
theorem sevenRegular_codegreeFour_commuting_privateSums
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 4) :
    ∃ P Q : Finset V,
      P.card = 3 ∧ Q.card = 3 ∧ Disjoint P Q ∧
      ∀ (A : Matrix V V ℤ), D.adjMatrix ℤ * A = A * D.adjMatrix ℤ →
        ∀ z : V,
          (∑ p ∈ P, A p z) - (∑ q ∈ Q, A q z) =
            ∑ w : V, (A x w - A y w) * D.adjMatrix ℤ w z := by
  obtain ⟨P, Q, hP, hQ, hdisj, hrow⟩ :=
    sevenRegular_codegreeFour_exists_sparse_adjMatrix_rowDifference
      D hreg hcommon
  refine ⟨P, Q, hP, hQ, hdisj, ?_⟩
  intro A hcomm z
  have h := finiteSparseRowDifference_of_matrix_comm
    (D.adjMatrix ℤ) A x y P Q hcomm hrow z
  have hprivate :
      (∑ w : V,
        ((if w ∈ P then 1 else 0) - (if w ∈ Q then 1 else 0)) * A w z) =
        (∑ p ∈ P, A p z) - (∑ q ∈ Q, A q z) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,
      sum_mem_indicator_mul_codegreeFour P (fun w => A w z),
      sum_mem_indicator_mul_codegreeFour Q (fun w => A w z)]
  rw [hprivate] at h
  exact h

end

end Erdos85
