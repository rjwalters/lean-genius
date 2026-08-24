import Proofs.Erdos85C4FreeSupportUniqueNeighborLowerBound

/-!
# Unique neighbors survive in an adjacency image

If a vertex has exactly one graph neighbor in the support of a vector `y`,
then its coordinate in `A y` is exactly that unique nonzero coordinate of
`y`.  Thus all unique-support-neighbor vertices lie in `support(Ay)`.  This
turns the C4-free unique-neighbor count into the image-support lower bound
used by the maximal defect-connectivity sandwich.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Finite support of a vector on a finite type. -/
def finiteVectorSupport {V R : Type*} [Fintype V] [DecidableEq V]
    [Zero R] [DecidableEq R] (y : V → R) : Finset V :=
  Finset.univ.filter fun v => y v ≠ 0

@[simp] theorem mem_finiteVectorSupport
    {V R : Type*} [Fintype V] [DecidableEq V]
    [Zero R] [DecidableEq R] (y : V → R) (v : V) :
    v ∈ finiteVectorSupport y ↔ y v ≠ 0 := by
  simp [finiteVectorSupport]

/-- A unique neighbor in the support of `y` gives a nonzero coordinate of
the adjacency image. -/
theorem adjMatrix_mulVec_ne_zero_of_card_neighbor_inter_support_eq_one
    {V K : Type*} [Fintype V] [DecidableEq V]
    [Field K] [DecidableEq K] (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → K) (v : V)
    (hone : (G.neighborFinset v ∩ finiteVectorSupport y).card = 1) :
    (G.adjMatrix K).mulVec y v ≠ 0 := by
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

/-- Every unique-support-neighbor vertex belongs to the support of `Ay`. -/
theorem uniqueSupportNeighbor_subset_mulVecSupport
    {V K : Type*} [Fintype V] [DecidableEq V]
    [Field K] [DecidableEq K] (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → K) :
    (Finset.univ.filter fun v =>
      (G.neighborFinset v ∩ finiteVectorSupport y).card = 1) ⊆
      finiteVectorSupport ((G.adjMatrix K).mulVec y) := by
  intro v hv
  rw [Finset.mem_filter] at hv
  exact (mem_finiteVectorSupport _ _).mpr
    (adjMatrix_mulVec_ne_zero_of_card_neighbor_inter_support_eq_one
      G y v hv.2)

/-- C4-free regular support lower bound transferred to `support(Ay)`. -/
theorem c4Free_regular_mulVecSupport_lower
    {V K : Type*} [Fintype V] [DecidableEq V]
    [Field K] [DecidableEq K] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (y : V → K)
    (hSq : (finiteVectorSupport y).card ≤ q) :
    (finiteVectorSupport y).card *
        (q - (finiteVectorSupport y).card + 1) ≤
      (finiteVectorSupport ((G.adjMatrix K).mulVec y)).card := by
  exact (c4Free_regular_card_one_supportNeighbor_lower
    G hfree hreg (finiteVectorSupport y) hSq).trans
      (Finset.card_le_card (uniqueSupportNeighbor_subset_mulVecSupport G y))

end

end Erdos85

#print axioms Erdos85.adjMatrix_mulVec_ne_zero_of_card_neighbor_inter_support_eq_one
#print axioms Erdos85.uniqueSupportNeighbor_subset_mulVecSupport
#print axioms Erdos85.c4Free_regular_mulVecSupport_lower
