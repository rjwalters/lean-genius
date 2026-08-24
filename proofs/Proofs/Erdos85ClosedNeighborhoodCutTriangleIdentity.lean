import Proofs.Erdos85DefectCutLaplacianSupport

/-!
# Closed-neighborhood cuts and local triangles

We first record the addition-shaped degree decomposition of a regular graph
cut.  Its closed-neighborhood specialization is the arithmetic core of the
identity relating incidence-row energy to the number of local triangles.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In a regular graph, cut incidences plus twice-counted internal incidences
equal shore size times the common degree. -/
theorem finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ x, D.degree x = r) (S : Finset V) :
    finsetGraphCutSize D S +
        ∑ x ∈ S, (D.neighborFinset x ∩ S).card = S.card * r := by
  rw [finsetGraphCutSize, ← Finset.sum_add_distrib]
  calc
    (∑ x ∈ S, ((D.neighborFinset x \ S).card +
        (D.neighborFinset x ∩ S).card)) =
        ∑ x ∈ S, D.degree x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← D.card_neighborFinset_eq_degree]
          have hpartition : (D.neighborFinset x \ S) ∪
              (D.neighborFinset x ∩ S) = D.neighborFinset x := by
            ext y
            by_cases hy : y ∈ S <;> simp [hy]
          have hdisj : Disjoint (D.neighborFinset x \ S)
              (D.neighborFinset x ∩ S) := by
            rw [Finset.disjoint_left]
            intro y hyout hyin
            exact (Finset.mem_sdiff.mp hyout).2 (Finset.mem_inter.mp hyin).2
          rw [← Finset.card_union_of_disjoint hdisj, hpartition]
    _ = ∑ _x ∈ S, r := by
      apply Finset.sum_congr rfl
      intro x _
      exact hreg x
    _ = S.card * r := by simp

/-- Closed-neighborhood form of the regular cut degree decomposition. -/
theorem closedNeighborhood_cut_add_internal_eq_degree_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ x, D.degree x = r) (x : V) :
    let S := insert x (D.neighborFinset x)
    finsetGraphCutSize D S +
        ∑ u ∈ S, (D.neighborFinset u ∩ S).card = (r + 1) * r := by
  dsimp only
  have h := finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular
    D hreg (insert x (D.neighborFinset x))
  have hxnot : x ∉ D.neighborFinset x := by simp
  rw [Finset.card_insert_of_notMem hxnot,
    D.card_neighborFinset_eq_degree, hreg x] at h
  exact h

/-- Expanded closed-neighborhood identity: the internal incidence term is
the two star orientations plus the ordered local-triangle incidences. -/
theorem closedNeighborhood_cut_add_two_mul_degree_add_common_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ x, D.degree x = r) (x : V) :
    finsetGraphCutSize D (insert x (D.neighborFinset x)) +
        (2 * r + ∑ u ∈ D.neighborFinset x,
          (D.neighborFinset u ∩ D.neighborFinset x).card) =
      (r + 1) * r := by
  have hbase := closedNeighborhood_cut_add_internal_eq_degree_product
    D hreg x
  dsimp only at hbase
  have hxnot : x ∉ D.neighborFinset x := by simp
  rw [Finset.sum_insert hxnot] at hbase
  have hxterm : (D.neighborFinset x ∩
      insert x (D.neighborFinset x)).card = r := by
    have hinter : D.neighborFinset x ∩ insert x (D.neighborFinset x) =
        D.neighborFinset x := by
      ext y
      simp
    rw [hinter, D.card_neighborFinset_eq_degree, hreg x]
  rw [hxterm] at hbase
  have hu : ∀ u ∈ D.neighborFinset x,
      (D.neighborFinset u ∩ insert x (D.neighborFinset x)).card =
        1 + (D.neighborFinset u ∩ D.neighborFinset x).card := by
    intro u hux
    have hxu : x ∈ D.neighborFinset u := by
      exact (D.mem_neighborFinset u x).mpr
        ((D.adj_comm x u).mp ((D.mem_neighborFinset x u).mp hux))
    have hset : D.neighborFinset u ∩ insert x (D.neighborFinset x) =
        insert x (D.neighborFinset u ∩ D.neighborFinset x) := by
      ext y
      by_cases hyx : y = x
      · subst y
        simp [hxu]
      · simp [hyx, and_comm]
    have hxcommon : x ∉ D.neighborFinset u ∩ D.neighborFinset x := by simp
    rw [hset, Finset.card_insert_of_notMem hxcommon]
    omega
  have hsum : (∑ u ∈ D.neighborFinset x,
      (D.neighborFinset u ∩ insert x (D.neighborFinset x)).card) =
      r + ∑ u ∈ D.neighborFinset x,
        (D.neighborFinset u ∩ D.neighborFinset x).card := by
    calc
      _ = ∑ u ∈ D.neighborFinset x,
          (1 + (D.neighborFinset u ∩ D.neighborFinset x).card) := by
            apply Finset.sum_congr rfl
            exact hu
      _ = (D.neighborFinset x).card + ∑ u ∈ D.neighborFinset x,
          (D.neighborFinset u ∩ D.neighborFinset x).card := by
            rw [Finset.sum_add_distrib]
            simp
      _ = r + _ := by rw [D.card_neighborFinset_eq_degree, hreg x]
  rw [hsum] at hbase
  omega

end

end Erdos85

#print axioms Erdos85.finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular
#print axioms Erdos85.closedNeighborhood_cut_add_internal_eq_degree_product
#print axioms Erdos85.closedNeighborhood_cut_add_two_mul_degree_add_common_sum
