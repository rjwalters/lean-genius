import Proofs.Erdos85C4FreeNeighborBlockPartition

/-! # Cross-block orthogonality in C4-free graphs

The mixed matrix identity used in the order-81 row-cover argument is in fact
parameter-free.  For two disjoint vertex blocks `T` and `U`, a cross-block
pair `(t,b)` cannot have both a common neighbor in `T` and a common neighbor
in `U`: those would be two distinct common neighbors and hence a 4-cycle.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Fundamental pointwise orthogonality.  For any distinct endpoints, common
neighbors restricted to two disjoint blocks cannot both be present. -/
theorem c4Free_disjointBlocks_common_card_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {x y : V} (hxy : x ≠ y) :
    (((G.neighborFinset x ∩ T) ∩ G.neighborFinset y).card *
      ((G.neighborFinset x ∩ U) ∩ G.neighborFinset y).card) = 0 := by
  classical
  let A := (G.neighborFinset x ∩ T) ∩ G.neighborFinset y
  let C := (G.neighborFinset x ∩ U) ∩ G.neighborFinset y
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro w hwA hwC
    exact (Finset.disjoint_left.mp hTU
      (Finset.mem_inter.mp (Finset.mem_inter.mp hwA).1).2
      (Finset.mem_inter.mp (Finset.mem_inter.mp hwC).1).2)
  have hsub : A ∪ C ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwA | hwC
    · exact Finset.mem_inter.mpr ⟨
        (Finset.mem_inter.mp (Finset.mem_inter.mp hwA).1).1,
        (Finset.mem_inter.mp hwA).2⟩
    · exact Finset.mem_inter.mpr ⟨
        (Finset.mem_inter.mp (Finset.mem_inter.mp hwC).1).1,
        (Finset.mem_inter.mp hwC).2⟩
  have hle : A.card + C.card ≤ 1 := by
    rw [← Finset.card_union_of_disjoint hAC]
    exact (Finset.card_le_card hsub).trans
      ((not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy)
  change A.card * C.card = 0
  have hz : A.card = 0 ∨ C.card = 0 := by omega
  rcases hz with hA | hC
  · simp [hA]
  · simp [hC]

/-- Cross-block endpoint specialization of the fundamental pointwise law. -/
theorem c4Free_crossBlock_common_card_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {t b : V} (ht : t ∈ T) (hb : b ∈ U) :
    (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card *
      ((G.neighborFinset t ∩ U) ∩ G.neighborFinset b).card) = 0 := by
  have htb : t ≠ b := by
    intro h
    subst b
    exact Finset.disjoint_left.mp hTU ht hb
  exact c4Free_disjointBlocks_common_card_mul_eq_zero G hfree T U hTU htb

/-- Summed algebraic form: the residual-block product has zero total mass.
In incidence-matrix notation this is the support orthogonality behind
`trace (Qᵀ A Q K) = 0`, with no degree, order, or parity hypothesis. -/
theorem c4Free_crossBlock_trace_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U) :
    (∑ t ∈ T, ∑ b ∈ U,
      (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card *
        ((G.neighborFinset t ∩ U) ∩ G.neighborFinset b).card)) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro b hb
  exact c4Free_crossBlock_common_card_mul_eq_zero G hfree T U hTU ht hb

/-- Off-diagonal same-block Gram form.  For distinct endpoints in `T`, their
common-neighbor counts in `T` and in the disjoint block `U` have disjoint
support. -/
theorem c4Free_sameBlock_offDiagonal_gram_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U) :
    (∑ t ∈ T, ∑ u ∈ T.filter (fun u => u ≠ t),
      (((G.neighborFinset t ∩ U) ∩ G.neighborFinset u).card *
        ((G.neighborFinset t ∩ T) ∩ G.neighborFinset u).card)) = 0 := by
  apply Finset.sum_eq_zero
  intro t _ht
  apply Finset.sum_eq_zero
  intro u hu
  have htu : t ≠ u := (Finset.mem_filter.mp hu).2.symm
  simpa [Nat.mul_comm] using
    (c4Free_disjointBlocks_common_card_mul_eq_zero G hfree T U hTU htu)

/-- Exact cross-block saturation ledger.  Every ordered pair `(t, u)` in
disjoint blocks is accounted for either by its (necessarily unique) common
neighbor or by an edge of the second-order defect graph.  This is the scalar,
parameter-free ancestor of the defect-component cross-block matrix equation. -/
theorem c4Free_crossBlock_twoWalk_add_defect_eq_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U) :
    (∑ t ∈ T, ∑ w ∈ G.neighborFinset t,
        (G.neighborFinset w ∩ U).card) +
      (∑ t ∈ T,
        ((secondOrderDefectGraph G).neighborFinset t ∩ U).card) =
      T.card * U.card := by
  classical
  rw [← Finset.sum_add_distrib]
  calc
    (∑ t ∈ T, ((∑ w ∈ G.neighborFinset t,
          (G.neighborFinset w ∩ U).card) +
        ((secondOrderDefectGraph G).neighborFinset t ∩ U).card)) =
        ∑ _t ∈ T, U.card := by
      apply Finset.sum_congr rfl
      intro t ht
      have htU : t ∉ U := by
        intro ht'
        exact Finset.disjoint_left.mp hTU ht ht'
      rw [c4Free_sum_neighbor_block_cards_eq_defect_complement
        G hfree t U htU]
      simpa [Finset.inter_comm] using
        Finset.card_sdiff_add_card_inter U
          ((secondOrderDefectGraph G).neighborFinset t)
    _ = T.card * U.card := by simp

end

end Erdos85

#print axioms Erdos85.c4Free_crossBlock_common_card_mul_eq_zero
#print axioms Erdos85.c4Free_crossBlock_trace_zero
#print axioms Erdos85.c4Free_sameBlock_offDiagonal_gram_zero
#print axioms Erdos85.c4Free_crossBlock_twoWalk_add_defect_eq_card_mul
