import Proofs.Erdos85SevenRegularNearTwinCommutingPropagation

/-! # Equal owner rows propagate to the unique near-twin private pair -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If an integral matrix commuting with a seven-regular graph has equal rows
on a codegree-six pair, then it has equal rows on that pair's unique private
neighbors.  The witnesses are returned with their graph-theoretic private-side
memberships, making the propagation iterable. -/
theorem sevenRegular_nearTwin_equal_commutingRows_propagate_private
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6)
    (A : Matrix V V ℤ)
    (hcomm : D.adjMatrix ℤ * A = A * D.adjMatrix ℤ)
    (hrows : ∀ z, A x z = A y z) :
    ∃ p q : V, p ≠ q ∧
      p ∈ D.neighborFinset x \ D.neighborFinset y ∧
      q ∈ D.neighborFinset y \ D.neighborFinset x ∧
      ∀ z, A p z = A q z := by
  classical
  obtain ⟨p, q, hpq, hrow⟩ :=
    sevenRegular_nearTwin_exists_sparse_adjMatrix_rowDifference
      D hreg hcommon
  have hpMem : p ∈ D.neighborFinset x \ D.neighborFinset y := by
    apply Finset.mem_sdiff.mpr
    have hp := hrow p
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply] at hp
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      by_contra hxp
      by_cases hyp : D.Adj y p <;> simp [hxp, hyp, hpq] at hp
    · rw [SimpleGraph.mem_neighborFinset]
      intro hyp
      by_cases hxp : D.Adj x p <;> simp [hxp, hyp, hpq] at hp
  have hqMem : q ∈ D.neighborFinset y \ D.neighborFinset x := by
    apply Finset.mem_sdiff.mpr
    have hq := hrow q
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply] at hq
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      by_contra hyq
      by_cases hxq : D.Adj x q <;> simp [hxq, hyq, Ne.symm hpq] at hq
    · rw [SimpleGraph.mem_neighborFinset]
      intro hxq
      by_cases hyq : D.Adj y q <;> simp [hxq, hyq, Ne.symm hpq] at hq
  refine ⟨p, q, hpq, hpMem, hqMem, ?_⟩
  intro z
  have hbalance := sparseRowDifference_of_matrix_comm
    (D.adjMatrix ℤ) A x y p q hcomm hrow z
  have hzero : (∑ w : V,
      (A x w - A y w) * D.adjMatrix ℤ w z) = 0 := by
    apply Finset.sum_eq_zero
    intro w _hw
    rw [hrows w, sub_self, zero_mul]
  have hlhs : (∑ w : V,
      ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * A w z) =
      A p z - A q z := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hzero] at hbalance
  rw [hlhs] at hbalance
  omega

end

end Erdos85
