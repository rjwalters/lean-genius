import Proofs.Erdos85UniqueNeighborMulVecSupport

/-!
# Integer unique-neighbor image support

The centered defect-cut vector naturally lives over `ℤ`. The generic
unique-neighbor image theorem was initially exposed only over fields, although
its proof uses no division. This file supplies the exact integer interface
needed by the maximal-connectivity capstone.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A unique neighbor in an integer vector's support gives a nonzero adjacency
image coordinate. -/
theorem adjMatrix_mulVec_int_ne_zero_of_card_neighbor_inter_support_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → ℤ) (v : V)
    (hone : (G.neighborFinset v ∩ finiteVectorSupport y).card = 1) :
    (G.adjMatrix ℤ).mulVec y v ≠ 0 := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
  have hwmem : w ∈ G.neighborFinset v ∩ finiteVectorSupport y := by
    rw [hw]
    simp
  have hwN := (Finset.mem_inter.mp hwmem).1
  have hwy : y w ≠ 0 :=
    (mem_finiteVectorSupport y w).mp (Finset.mem_inter.mp hwmem).2
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hsum : ∑ z ∈ G.neighborFinset v, y z = y w := by
    apply Finset.sum_eq_single w
    · intro z hzN hzw
      have hznot : z ∉ finiteVectorSupport y := by
        intro hzS
        have hzInter : z ∈ G.neighborFinset v ∩ finiteVectorSupport y :=
          Finset.mem_inter.mpr ⟨hzN, hzS⟩
        rw [hw] at hzInter
        exact hzw (Finset.mem_singleton.mp hzInter)
      exact not_ne_iff.mp ((mem_finiteVectorSupport y z).not.mp hznot)
    · intro hwNot
      exact (hwNot hwN).elim
  rw [hsum]
  exact hwy

/-- C4-free regular unique-neighbor support lower bound over `ℤ`. -/
theorem c4Free_regular_int_mulVecSupport_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (y : V → ℤ)
    (hSq : (finiteVectorSupport y).card ≤ q) :
    (finiteVectorSupport y).card *
        (q - (finiteVectorSupport y).card + 1) ≤
      (finiteVectorSupport ((G.adjMatrix ℤ).mulVec y)).card := by
  have hsub :
      (Finset.univ.filter fun v =>
        (G.neighborFinset v ∩ finiteVectorSupport y).card = 1) ⊆
        finiteVectorSupport ((G.adjMatrix ℤ).mulVec y) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact (mem_finiteVectorSupport _ _).mpr
      (adjMatrix_mulVec_int_ne_zero_of_card_neighbor_inter_support_eq_one
        G y v hv.2)
  exact (c4Free_regular_card_one_supportNeighbor_lower
    G hfree hreg (finiteVectorSupport y) hSq).trans (Finset.card_le_card hsub)

#print axioms adjMatrix_mulVec_int_ne_zero_of_card_neighbor_inter_support_eq_one
#print axioms c4Free_regular_int_mulVecSupport_lower

end

end Erdos85
