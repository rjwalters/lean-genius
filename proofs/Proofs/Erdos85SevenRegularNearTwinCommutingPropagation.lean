import Proofs.Erdos85SevenRegularNearTwinNormalization

/-! # Propagation of a near-twin row through a commuting operator -/

namespace Erdos85

noncomputable section

/-- The graph-theoretic near-twin normalization expressed as an exact signed
row identity in the integral adjacency matrix. -/
theorem sevenRegular_nearTwin_exists_sparse_adjMatrix_rowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6) :
    ∃ p q : V, p ≠ q ∧ ∀ w : V,
      D.adjMatrix ℤ x w - D.adjMatrix ℤ y w =
        (if w = p then 1 else 0) - (if w = q then 1 else 0) := by
  obtain ⟨p, q, hp, hq, hpq, _⟩ :=
    sevenRegular_nearTwin_privateNeighbor_normalization D hreg hcommon
  refine ⟨p, q, hpq, ?_⟩
  intro w
  have hpiff : (w ∈ D.neighborFinset x ∧ w ∉ D.neighborFinset y) ↔ w = p := by
    rw [← Finset.mem_sdiff, hp]
    simp
  have hqiff : (w ∈ D.neighborFinset y ∧ w ∉ D.neighborFinset x) ↔ w = q := by
    rw [← Finset.mem_sdiff, hq]
    simp
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  by_cases hx : D.Adj x w <;> by_cases hy : D.Adj y w <;>
    simp_all [SimpleGraph.mem_neighborFinset]

/-- A two-coordinate row difference for `D` propagates across every operator
commuting with `D`.  This is the entrywise form used to turn a near-twin pair
into signed neighbor-balance constraints for owner/selector matrices. -/
theorem sparseRowDifference_of_matrix_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A : Matrix V V ℤ) (x y p q : V)
    (hcomm : D * A = A * D)
    (hrow : ∀ w : V,
      D x w - D y w = (if w = p then 1 else 0) - (if w = q then 1 else 0)) :
    ∀ z : V,
      (∑ w : V, ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * A w z) =
        ∑ w : V, (A x w - A y w) * D w z := by
  intro z
  have hentry : (D * A) x z - (D * A) y z =
      (A * D) x z - (A * D) y z := by rw [hcomm]
  rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply] at hentry
  have hleft :
      (∑ w : V, D x w * A w z) - (∑ w : V, D y w * A w z) =
        ∑ w : V, ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * A w z := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _hw
    rw [← sub_mul, hrow]
  have hright :
      (∑ w : V, A x w * D w z) - (∑ w : V, A y w * D w z) =
        ∑ w : V, (A x w - A y w) * D w z := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [sub_mul]
  exact hleft.symm.trans (hentry.trans hright)

/-- Combined near-twin propagation package.  The same private pair `p,q`
works simultaneously for every integral matrix commuting with the graph
adjacency matrix. -/
theorem sevenRegular_nearTwin_commuting_signed_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6) :
    ∃ p q : V, p ≠ q ∧ ∀ (A : Matrix V V ℤ),
      D.adjMatrix ℤ * A = A * D.adjMatrix ℤ → ∀ z : V,
        (∑ w : V,
          ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * A w z) =
        ∑ w : V, (A x w - A y w) * D.adjMatrix ℤ w z := by
  obtain ⟨p, q, hpq, hrow⟩ :=
    sevenRegular_nearTwin_exists_sparse_adjMatrix_rowDifference D hreg hcommon
  refine ⟨p, q, hpq, ?_⟩
  intro A hcomm z
  exact sparseRowDifference_of_matrix_comm
    (D.adjMatrix ℤ) A x y p q hcomm hrow z

end

end Erdos85
