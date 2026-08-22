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

/-- Rows in one cross-block incidence fiber have pairwise-disjoint
neighborhoods inside the row block.  A shared row neighbor together with the
fiber point would otherwise give two common neighbors. -/
theorem c4Free_shared_crossBlock_fiber_neighborFinsets_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {b t u : V} (hb : b ∈ U) (ht : t ∈ G.neighborFinset b ∩ T)
    (hu : u ∈ G.neighborFinset b ∩ T) (htu : t ≠ u) :
    Disjoint (G.neighborFinset t ∩ T) (G.neighborFinset u ∩ T) := by
  rw [Finset.disjoint_left]
  intro v hvt hvu
  have htParts := Finset.mem_inter.mp ht
  have huParts := Finset.mem_inter.mp hu
  have hvtParts := Finset.mem_inter.mp hvt
  have hvuParts := Finset.mem_inter.mp hvu
  have hbCommon : b ∈ G.neighborFinset t ∩ G.neighborFinset u :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset t b).mpr
        ((G.adj_comm b t).mp ((G.mem_neighborFinset b t).mp htParts.1)),
      (G.mem_neighborFinset u b).mpr
        ((G.adj_comm b u).mp ((G.mem_neighborFinset b u).mp huParts.1))⟩
  have hvCommon : v ∈ G.neighborFinset t ∩ G.neighborFinset u :=
    Finset.mem_inter.mpr ⟨hvtParts.1, hvuParts.1⟩
  have hbv : b ≠ v := by
    intro h
    subst v
    exact Finset.disjoint_left.mp hTU hvtParts.2 hb
  have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree t u htu
  exact hbv (Finset.card_le_one.mp hle b hbCommon v hvCommon)

/-- Fibers over the endpoints of an internal edge of `U` are anticomplete
inside `T`.  The four alleged edges would be a cross-block 4-cycle. -/
theorem c4Free_internalEdge_crossBlock_fibers_anticomplete
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {b c t u : V} (hbc : G.Adj b c)
    (hb : b ∈ U) (hc : c ∈ U)
    (ht : t ∈ G.neighborFinset b ∩ T)
    (hu : u ∈ G.neighborFinset c ∩ T) :
    ¬ G.Adj t u := by
  intro htu
  have hbu : b ≠ u := by
    intro h
    subst u
    exact Finset.disjoint_left.mp hTU (Finset.mem_inter.mp hu).2 hb
  have htc : t ≠ c := by
    intro h
    subst t
    exact Finset.disjoint_left.mp hTU (Finset.mem_inter.mp ht).2 hc
  have htCommon : t ∈ G.neighborFinset b ∩ G.neighborFinset u :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ht).1,
      (G.mem_neighborFinset u t).mpr ((G.adj_comm t u).mp htu)⟩
  have hcCommon : c ∈ G.neighborFinset b ∩ G.neighborFinset u :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b c).mpr hbc,
      (G.mem_neighborFinset u c).mpr
        ((G.adj_comm c u).mp
          ((G.mem_neighborFinset c u).mp (Finset.mem_inter.mp hu).1))⟩
  have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree b u hbu
  exact htc (Finset.card_le_one.mp hle t htCommon c hcCommon)

/-- Rowwise two-block mass bound.  For disjoint vertex blocks `T,U`, the
total `U`-degrees of the neighbors of `t ∈ T` which lie in `T ∪ U` cannot
exceed `|U|`.  The omitted neighbors outside the two blocks only strengthen
the inequality.  This is the parameter-free packing inequality behind the
rowwise `A Q` versus `Q K` support obstruction. -/
theorem c4Free_crossBlock_row_neighbor_mass_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {t : V} (ht : t ∈ T) :
    (∑ w ∈ G.neighborFinset t ∩ T,
        (G.neighborFinset w ∩ U).card) +
      (∑ w ∈ G.neighborFinset t ∩ U,
        (G.neighborFinset w ∩ U).card) ≤ U.card := by
  classical
  let N := G.neighborFinset t
  let f := fun w => (G.neighborFinset w ∩ U).card
  have htU : t ∉ U := by
    intro ht'
    exact Finset.disjoint_left.mp hTU ht ht'
  have hparts : Disjoint (N ∩ T) (N ∩ U) :=
    hTU.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsub : (N ∩ T) ∪ (N ∩ U) ⊆ N :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcover := c4Free_sum_neighbor_block_cards_eq_defect_complement
    G hfree t U htU
  dsimp only at hcover
  change (∑ w ∈ N, f w) =
    (U \ (secondOrderDefectGraph G).neighborFinset t).card at hcover
  calc
    (∑ w ∈ N ∩ T, f w) + (∑ w ∈ N ∩ U, f w) =
        ∑ w ∈ (N ∩ T) ∪ (N ∩ U), f w := by
          rw [Finset.sum_union hparts]
    _ ≤ ∑ w ∈ N, f w := Finset.sum_le_sum_of_subset hsub
    _ = (U \ (secondOrderDefectGraph G).neighborFinset t).card := hcover
    _ ≤ U.card := Finset.card_le_card Finset.sdiff_subset

/-- Uniform-degree consequence of the rowwise mass bound.  If every
`T`-neighbor of `t` has at least `r` neighbors in `U`, and every
`U`-neighbor of `t` has at least `k` neighbors in `U`, their two center
classes obey the sharp packing inequality below. -/
theorem c4Free_crossBlock_row_degree_packing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (T U : Finset V) (hTU : Disjoint T U)
    {t : V} (ht : t ∈ T) (r k : ℕ)
    (hr : ∀ w ∈ G.neighborFinset t ∩ T,
      r ≤ (G.neighborFinset w ∩ U).card)
    (hk : ∀ w ∈ G.neighborFinset t ∩ U,
      k ≤ (G.neighborFinset w ∩ U).card) :
    r * (G.neighborFinset t ∩ T).card +
      k * (G.neighborFinset t ∩ U).card ≤ U.card := by
  have hT : r * (G.neighborFinset t ∩ T).card ≤
      ∑ w ∈ G.neighborFinset t ∩ T,
        (G.neighborFinset w ∩ U).card := by
    calc
      r * (G.neighborFinset t ∩ T).card =
          ∑ _w ∈ G.neighborFinset t ∩ T, r := by
            simp [Nat.mul_comm]
      _ ≤ ∑ w ∈ G.neighborFinset t ∩ T,
          (G.neighborFinset w ∩ U).card := by
            apply Finset.sum_le_sum
            intro w hw
            exact hr w hw
  have hU : k * (G.neighborFinset t ∩ U).card ≤
      ∑ w ∈ G.neighborFinset t ∩ U,
        (G.neighborFinset w ∩ U).card := by
    calc
      k * (G.neighborFinset t ∩ U).card =
          ∑ _w ∈ G.neighborFinset t ∩ U, k := by
            simp [Nat.mul_comm]
      _ ≤ ∑ w ∈ G.neighborFinset t ∩ U,
          (G.neighborFinset w ∩ U).card := by
            apply Finset.sum_le_sum
            intro w hw
            exact hk w hw
  exact (Nat.add_le_add hT hU).trans
    (c4Free_crossBlock_row_neighbor_mass_le G hfree T U hTU ht)

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
#print axioms Erdos85.c4Free_shared_crossBlock_fiber_neighborFinsets_disjoint
#print axioms Erdos85.c4Free_internalEdge_crossBlock_fibers_anticomplete
#print axioms Erdos85.c4Free_crossBlock_row_neighbor_mass_le
#print axioms Erdos85.c4Free_crossBlock_row_degree_packing
#print axioms Erdos85.c4Free_crossBlock_twoWalk_add_defect_eq_card_mul
