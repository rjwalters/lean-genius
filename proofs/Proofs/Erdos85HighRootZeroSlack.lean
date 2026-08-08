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

/-- In a square-order `C₄`-free graph, local excess conservation supplies
all zero-slack high-root hypotheses automatically at every degree-`d+1`
vertex. -/
theorem squareOrder_degree_succ_highRoot_structure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1) :
    (secondOrderDefectGraph G).degree v = 0 ∧
      (∀ y, G.Adj v y → G.degree y = d) ∧
      (∀ s : {z : V // z ∈ G.neighborSet v},
        (G.induce (G.neighborSet v)).degree s = 1) := by
  have hcard' : Fintype.card V = d * (d - 1) + 1 + (d - 1) := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 :=
      ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
    norm_num
    ring
  have hbudget :=
    secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
      G hfree (d := d) (q := d - 1) (by omega) hmin hcard' v
  have hvsub : G.degree v - d = 1 := by omega
  have hDzero : (secondOrderDefectGraph G).degree v = 0 := by
    rw [hvsub] at hbudget
    omega
  have hExzero : neighborDegreeExcess G d v = 0 := by
    rw [hvsub] at hbudget
    omega
  have hneigh : ∀ y, G.Adj v y → G.degree y = d := by
    intro y hvy
    rw [neighborDegreeExcess_eq_sum_neighborFinset] at hExzero
    have hterms : ∀ z ∈ G.neighborFinset v, 0 ≤ G.degree z - d := by
      intro z _
      omega
    have hyMem : y ∈ G.neighborFinset v :=
      (G.mem_neighborFinset v y).mpr hvy
    have hyzero :=
      (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hExzero y hyMem
    have := hmin y
    omega
  have hDempty : (secondOrderDefectGraph G).neighborFinset v = ∅ := by
    rw [← Finset.card_eq_zero,
      (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDzero]
  have hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1 := by
    intro s
    have hle : (G.induce (G.neighborSet v)).degree s ≤ 1 := by
      rw [degree_induce_neighborSet_eq_card_common]
      exact common_le_one_of_not_containsC4 hfree v s.1
        (G.ne_of_adj s.2)
    have hne : (G.induce (G.neighborSet v)).degree s ≠ 0 := by
      intro hzero
      have hcommonzero :
          (G.neighborFinset v ∩ G.neighborFinset s.1).card = 0 := by
        rwa [degree_induce_neighborSet_eq_card_common] at hzero
      have hsTF : s.1 ∈ triangleFreeNeighbors G v :=
        (mem_triangleFreeNeighbors G v s.1).mpr ⟨s.2, hcommonzero⟩
      have hsD : s.1 ∈ (secondOrderDefectGraph G).neighborFinset v := by
        rw [secondOrderDefectGraph_neighborFinset G v]
        exact Finset.mem_union_right _ hsTF
      rw [hDempty] at hsD
      exact Finset.notMem_empty s.1 hsD
    omega
  exact ⟨hDzero, hneigh, hlocal⟩

/-- **Square-order high-root saturation.**  Every degree-`d+1` vertex in a
square-order minimum-degree-`d` `C₄`-free graph sees the entire graph within
distance two. -/
theorem externalRepairCandidates_eq_empty_of_squareOrder_degree_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1) :
    externalRepairCandidates G v = ∅ := by
  rcases squareOrder_degree_succ_highRoot_structure
    G hfree hd hmin hcard hv with ⟨_, hneigh, hlocal⟩
  exact externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    G hfree hd hcard hv hneigh hlocal

/-- Under the tight-edge cover supplied by an edge-minimal witness, square
order admits only degrees `d` and `d+1`. -/
theorem squareOrder_degree_eq_or_succ_of_tightEdgeCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (x : V) :
    G.degree x = d ∨ G.degree x = d + 1 := by
  have hcard' : Fintype.card V = d * (d - 1) + 1 + (d - 1) := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 :=
      ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
    norm_num
    ring
  have hupper := degree_le_succ_of_order_excess_lt_two_mul_pred
    G hfree hmin hcover hcard' (by omega) x
  have hlower := hmin x
  omega

/-- Two degree-`d+1` vertices are nonadjacent under the tight-edge cover. -/
theorem squareOrder_not_adj_degree_succ_of_tightEdgeCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = d ∨ G.degree v = d)
    {x y : V} (hx : G.degree x = d + 1) (hy : G.degree y = d + 1) :
    ¬ G.Adj x y := by
  intro hxy
  rcases hcover hxy with hx' | hy' <;> omega

/-- Distinct high vertices at square order have exactly one common neighbor.
Thus their low-neighborhood incidence matrix has Gram matrix `d I + J`. -/
theorem squareOrder_card_common_degree_succ_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x y : V}
    (hx : G.degree x = d + 1) (hy : G.degree y = d + 1)
    (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  have hnadj := squareOrder_not_adj_degree_succ_of_tightEdgeCover
    G hcover hx hy
  have hle := common_le_one_of_not_containsC4 hfree x y hxy
  have hDzero :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree hd hmin hcard hx).1
  have hDempty : (secondOrderDefectGraph G).neighborFinset x = ∅ := by
    rw [← Finset.card_eq_zero,
      (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDzero]
  have hpos : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card := by
    by_contra hzero
    have hzero' : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
      omega
    have hyAnti : y ∈ antipodalNeighbors G x :=
      (mem_antipodalNeighbors G x y).mpr ⟨hxy.symm, hnadj, hzero'⟩
    have hyD : y ∈ (secondOrderDefectGraph G).neighborFinset x := by
      rw [secondOrderDefectGraph_neighborFinset G x]
      exact Finset.mem_union_left _ hyAnti
    rw [hDempty] at hyD
    exact Finset.notMem_empty y hyD
  omega

end

end Erdos85
