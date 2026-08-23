import Proofs.Erdos85C4FreeNeighborBlockPartition

/-! # Exact defect-cut identity in a C4-free graph

For a shore `S` and its complement `T`, every ordered pair in `S × T`
either has no common neighbor (and is a second-order defect edge) or has its
unique common neighbor in a C4-free graph.  This module packages that exact
partition in an addition-shaped natural-number identity, avoiding subtraction
until the later integer cut-variance layer.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Weighted adjacency incidences restricted to a shore, counted from the
shore first or from the weighted endpoint first. -/
theorem sum_subset_neighbor_weight_eq_sum_inter_card_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (weight : V → ℕ) :
    (∑ x ∈ S, ∑ w ∈ G.neighborFinset x, weight w) =
      ∑ w : V, (G.neighborFinset w ∩ S).card * weight w := by
  classical
  calc
    (∑ x ∈ S, ∑ w ∈ G.neighborFinset x, weight w) =
        ∑ x : V, if x ∈ S then
          (∑ w ∈ G.neighborFinset x, weight w) else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ x : V, ∑ w : V,
          if x ∈ S ∧ w ∈ G.neighborFinset x then weight w else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S
      · simp only [if_pos hx]
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext w
          simp [hx, SimpleGraph.mem_neighborFinset]
        · intro w _
          rfl
      · simp [hx]
    _ = ∑ w : V, ∑ x : V,
          if x ∈ S ∧ w ∈ G.neighborFinset x then weight w else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ w : V, (G.neighborFinset w ∩ S).card * weight w := by
      apply Finset.sum_congr rfl
      intro w _
      calc
        (∑ x : V, if x ∈ S ∧ w ∈ G.neighborFinset x then weight w else 0) =
            ∑ _x ∈ G.neighborFinset w ∩ S, weight w := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext x
            simp [SimpleGraph.mem_neighborFinset, G.adj_comm, and_comm]
          · intro x _
            rfl
        _ = (G.neighborFinset w ∩ S).card * weight w := by simp

/-- Exact cross-shore partition.  The first summand counts oriented defect
edges from `S` to `T`; the second counts ordered cross pairs by their unique
common-neighbor center.  Their sum is `|S| |T|`.

The statement allows any disjoint shore `T`, rather than requiring it to be
the whole complement; this is the reusable rectangular form. -/
theorem c4Free_defect_cut_add_twoWalk_eq_card_mul_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (S T : Finset V) (hST : Disjoint S T) :
    (∑ x ∈ S,
        ((secondOrderDefectGraph G).neighborFinset x ∩ T).card) +
      (∑ w : V, (G.neighborFinset w ∩ S).card *
        (G.neighborFinset w ∩ T).card) =
      S.card * T.card := by
  classical
  have hxT : ∀ x ∈ S, x ∉ T := by
    intro x hxS hxT
    exact Finset.disjoint_left.mp hST hxS hxT
  have hpoint : ∀ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩ T).card +
        (∑ w ∈ G.neighborFinset x,
          (G.neighborFinset w ∩ T).card) = T.card := by
    intro x hxS
    have hcover := c4Free_sum_neighbor_block_cards_eq_defect_complement
      G hfree x T (hxT x hxS)
    dsimp only at hcover
    rw [Finset.card_sdiff] at hcover
    have hle := Finset.card_le_card
      (Finset.inter_subset_right :
        (secondOrderDefectGraph G).neighborFinset x ∩ T ⊆ T)
    have hinter :
        (T ∩ (secondOrderDefectGraph G).neighborFinset x).card =
          ((secondOrderDefectGraph G).neighborFinset x ∩ T).card := by
      rw [Finset.inter_comm]
    omega
  have hsum := Finset.sum_congr rfl hpoint
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [sum_subset_neighbor_weight_eq_sum_inter_card_mul G S
    (fun w => (G.neighborFinset w ∩ T).card)] at hsum
  simpa [mul_comm] using hsum

/-- Complement-shore form of the exact cut identity.  If
`b w = |N_G(w) ∩ S|`, the centered two-walk contribution is exactly
`b w * (deg_G(w) - b w)`.  This is the first equality in the near-regular
cut-variance formula. -/
theorem c4Free_defect_cut_add_degree_product_eq_complete_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V) :
    let T := Finset.univ \ S
    let b := fun w => (G.neighborFinset w ∩ S).card
    (∑ x ∈ S,
        ((secondOrderDefectGraph G).neighborFinset x ∩ T).card) +
      (∑ w : V, b w * (G.degree w - b w)) =
      S.card * (Fintype.card V - S.card) := by
  classical
  dsimp only
  let T : Finset V := Finset.univ \ S
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact (Finset.mem_sdiff.mp hxT).2 hxS
  have hcut := c4Free_defect_cut_add_twoWalk_eq_card_mul_card
    G hfree S T hST
  have hTcard : T.card = Fintype.card V - S.card := by
    dsimp only [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
  rw [hTcard] at hcut
  dsimp only [T] at hcut
  rw [← hcut]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [← G.card_neighborFinset_eq_degree w]
  have hset : G.neighborFinset w ∩ (Finset.univ \ S) =
      G.neighborFinset w \ S := by
    ext y
    simp
  rw [hset, Finset.card_sdiff]
  congr 2
  ext y
  simp [and_comm]

#print axioms sum_subset_neighbor_weight_eq_sum_inter_card_mul
#print axioms c4Free_defect_cut_add_twoWalk_eq_card_mul_card
#print axioms c4Free_defect_cut_add_degree_product_eq_complete_cut

end

end Erdos85
