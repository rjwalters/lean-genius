import Proofs.Erdos85C4FreeRegularAdjacencyCube

/-! # Pointwise upper bound for cubic entries at nonneighbors -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- In a `d`-regular C4-free graph, a length-three walk between nonadjacent
vertices is determined by its first step: two possible last steps would
form a four-cycle. Hence every such cubic adjacency entry is at most `d`. -/
theorem c4Free_regular_adjMatrix_cube_apply_of_not_adj_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d)
    {a b : V} (hab : ¬ G.Adj a b) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b ≤ d := by
  classical
  let A := G.adjMatrix ℤ
  have hcommon : ∀ k ∈ G.neighborFinset b,
      (G.neighborFinset a ∩ G.neighborFinset k).card ≤ 1 := by
    intro k hk
    have hak : a ≠ k := by
      intro h
      subst k
      exact hab ((G.mem_neighborFinset b a).mp hk).symm
    exact common_le_one_of_not_containsC4 hfree a k hak
  have hsum :
      (∑ k ∈ G.neighborFinset b,
        ((G.neighborFinset a ∩ G.neighborFinset k).card : ℤ)) ≤ d := by
    calc
      _ ≤ ∑ _k ∈ G.neighborFinset b, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact_mod_cast hcommon k hk
      _ = d := by simp [G.card_neighborFinset_eq_degree, hreg]
  change (A * A * A) a b ≤ _
  rw [Matrix.mul_apply]
  simp only [A, SimpleGraph.adjMatrix_apply]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun k ↦ G.Adj k b) =
      G.neighborFinset b := by
    ext k
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilter]
  have hentry : ∀ k,
      (G.adjMatrix ℤ * G.adjMatrix ℤ) a k =
        ((G.neighborFinset a ∩ G.neighborFinset k).card : ℤ) := by
    intro k
    exact adjMatrix_sq_apply_eq_card_common G a k
  simpa only [hentry, mul_one] using hsum

/-- Degree-six specialization used by the h305 service row ledger. -/
theorem c4Free_sixRegular_adjMatrix_cube_apply_of_not_adj_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    {a b : V} (hab : ¬ G.Adj a b) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) a b ≤ 6 :=
  c4Free_regular_adjMatrix_cube_apply_of_not_adj_le
    G hfree 6 hreg hab

end

end Erdos85

#print axioms Erdos85.c4Free_regular_adjMatrix_cube_apply_of_not_adj_le
#print axioms
  Erdos85.c4Free_sixRegular_adjMatrix_cube_apply_of_not_adj_le_six
