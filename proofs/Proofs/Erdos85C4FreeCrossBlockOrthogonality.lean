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

/-- Pointwise cross-block orthogonality.  The two restricted common-neighbor
counts cannot both be positive in a C4-free graph. -/
theorem c4Free_crossBlock_common_card_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {t b : V} (ht : t ∈ T) (hb : b ∈ U) :
    (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card *
      ((G.neighborFinset t ∩ U) ∩ G.neighborFinset b).card) = 0 := by
  classical
  let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let C := (G.neighborFinset t ∩ U) ∩ G.neighborFinset b
  have htb : t ≠ b := by
    intro h
    subst b
    exact (Finset.disjoint_left.mp hTU ht hb)
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro w hwA hwC
    exact (Finset.disjoint_left.mp hTU
      (Finset.mem_inter.mp (Finset.mem_inter.mp hwA).1).2
      (Finset.mem_inter.mp (Finset.mem_inter.mp hwC).1).2)
  have hsub : A ∪ C ⊆ G.neighborFinset t ∩ G.neighborFinset b := by
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
      ((not_containsC4_iff_forall_common_le_one G).mp hfree t b htb)
  change A.card * C.card = 0
  have hz : A.card = 0 ∨ C.card = 0 := by omega
  rcases hz with hA | hC
  · simp [hA]
  · simp [hC]

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

end

end Erdos85

#print axioms Erdos85.c4Free_crossBlock_common_card_mul_eq_zero
#print axioms Erdos85.c4Free_crossBlock_trace_zero
