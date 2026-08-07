import Proofs.Erdos85OrderFortyNineHighBranchGeometry

/-!
# Parametric zero-slack geometry at square order

At order `d²`, a root of degree `d+1` with tight degree-`d` neighbors and a
1-regular induced neighborhood has `d+1` pairwise-disjoint second-layer
branches of size `d-2`.  They exactly exhaust the complement of the closed
neighborhood.  This is the general mechanism exposed by the order-49
laboratory.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Each branch at a zero-slack square-order high root has size `d-2`. -/
theorem card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 2 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (secondLayerBranch G v s).card = d - 2 := by
  have hcommon := hlocal s
  rw [degree_induce_neighborSet_eq_card_common] at hcommon
  have haccount := card_secondLayerBranch_add_common_add_one G v s
  have hsdegree := hneigh s.1 s.2
  omega

/-- The full second layer has cardinality `(d+1)(d-2)`. -/
theorem card_secondLayer_eq_mul_sub_two_of_squareOrder_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1) :
    (secondLayer G v).card = (d + 1) * (d - 2) := by
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
  rw [secondLayer, Finset.card_biUnion hdisj]
  calc
    (∑ s : {z : V // z ∈ G.neighborSet v},
        (secondLayerBranch G v s).card) =
        ∑ _s : {z : V // z ∈ G.neighborSet v}, (d - 2) := by
      apply Finset.sum_congr rfl
      intro s _
      exact card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
        G hd hv hneigh hlocal s
    _ = (d + 1) * (d - 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
          G.neighborFinset v := by ext z; simp
      rw [heq, G.card_neighborFinset_eq_degree, hv]
      rw [nsmul_eq_mul]
      norm_num

/-- At square order there is no vertex beyond distance two from such a high
root: the branch count has zero slack. -/
theorem externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1) :
    externalRepairCandidates G v = ∅ := by
  have hpartition :=
    card_externalRepairCandidates_add_card_secondLayer_add_degree_add_one G v
  rw [card_secondLayer_eq_mul_sub_two_of_squareOrder_highRoot
      G hfree hd hv hneigh hlocal, hv, hcard] at hpartition
  apply Finset.card_eq_zero.mp
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 :=
    ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  norm_num at hpartition
  nlinarith

end

end Erdos85
