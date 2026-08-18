import Proofs.Erdos85ConflictRegular
import Proofs.Erdos85MooreFriendship
import Proofs.Erdos85FrequencyPairTransport

/-!
# The conflict graph as a polynomial in adjacency

For a regular `C₄`-free graph, two distinct vertices have either zero or one
common neighbor.  Consequently the square of the adjacency matrix records
the conflict graph off the diagonal, while regularity supplies the diagonal:

`A(G)² = d I + A(commonNeighborConflict G)`.

In particular the original graph and its conflict graph commute and have a
common eigenspace decomposition.  This is the spectral structure unavailable
to a generic graph with the same conflict degree.
-/

namespace Erdos85

open SimpleGraph

/-- **Conflict polynomial identity.**  The conflict adjacency matrix of a
regular `C₄`-free graph is `A² - dI`. -/
theorem adjMatrix_sq_eq_degree_add_conflict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      (d : ℤ) • (1 : Matrix V V ℤ) +
        (commonNeighborConflict G).adjMatrix ℤ := by
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    rw [G.adjMatrix_mul_self_apply_self, hreg x]
    simp [SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common]
    have hle := common_le_one_of_not_containsC4 hfree x y hxy
    by_cases hnonempty :
        (G.neighborFinset x ∩ G.neighborFinset y).Nonempty
    · have hpos : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
        Finset.card_pos.mpr hnonempty
      have hone : (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
        omega
      simp [SimpleGraph.adjMatrix_apply, hxy, hnonempty, hone]
    · have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)
      simp [SimpleGraph.adjMatrix_apply, hxy, hnonempty, hzero]

/-- The conflict adjacency matrix commutes with the original adjacency
matrix, since it is a polynomial in that matrix. -/
theorem adjMatrix_comm_commonNeighborConflict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℤ * (commonNeighborConflict G).adjMatrix ℤ =
      (commonNeighborConflict G).adjMatrix ℤ * G.adjMatrix ℤ := by
  have hpoly := adjMatrix_sq_eq_degree_add_conflict G hfree hreg
  have hconflict : (commonNeighborConflict G).adjMatrix ℤ =
      G.adjMatrix ℤ * G.adjMatrix ℤ -
        (d : ℤ) • (1 : Matrix V V ℤ) := by
    rw [hpoly]
    abel
  rw [hconflict]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- Field-valued form of the conflict polynomial identity, suitable for
spectral arguments. -/
theorem adjMatrix_sq_eq_degree_add_conflict_field
    {K : Type*} [Field K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix K * G.adjMatrix K =
      (d : K) • (1 : Matrix V V K) +
        (commonNeighborConflict G).adjMatrix K := by
  have hz := adjMatrix_sq_eq_degree_add_conflict G hfree hreg
  have h := congrArg (fun M ↦ M.map (Int.castRingHom K)) hz
  simp only [Matrix.map_mul, adjMatrix_map_intCast] at h
  rw [h]
  ext x y
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, SimpleGraph.adjMatrix_apply, smul_eq_mul]
  split_ifs <;> simp only [eq_intCast] <;> push_cast <;> ring

/-- Field-valued commutation, obtained from the same polynomial identity. -/
theorem adjMatrix_comm_commonNeighborConflict_field
    {K : Type*} [Field K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix K * (commonNeighborConflict G).adjMatrix K =
      (commonNeighborConflict G).adjMatrix K * G.adjMatrix K := by
  have hpoly := adjMatrix_sq_eq_degree_add_conflict_field
    (K := K) G hfree hreg
  have hconflict : (commonNeighborConflict G).adjMatrix K =
      G.adjMatrix K * G.adjMatrix K -
        (d : K) • (1 : Matrix V V K) := by
    rw [hpoly]
    abel
  rw [hconflict]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

end Erdos85
