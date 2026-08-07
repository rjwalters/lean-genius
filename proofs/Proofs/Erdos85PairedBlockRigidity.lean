import Proofs.Erdos85OrderFortyNineOuterDefect

/-!
# Equality closure for paired branch defect bounds

The order-49 outer-graph argument produces six far-block inequalities and one
paired-block inequality.  Their upper bounds add to the already-known exact
cross-defect degree.  Consequently every inequality is an equality.  This file
isolates that arithmetic closure, so the graph-facing path count need only
provide the local inequalities and row-sum identities.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Ordered endpoint pairs in two outer branches which are adjacent in the
outer second-order defect graph. -/
def orderFortyNineOuterDefectBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    Finset ({x : V // x ∈ secondLayer G v} ×
      {x : V // x ∈ secondLayer G v}) :=
  (orderFortyNineOuterBranch G v s ×ˢ orderFortyNineOuterBranch G v t).filter
    fun xy ↦ (secondOrderDefectGraph (squareOrderOuterGraph G v)).Adj xy.1 xy.2

/-- The complementary ordered endpoint pairs in two outer branches.  Under
C4-freeness and for distinct branches, these are precisely the pairs having
one common neighbor in the outer graph. -/
def orderFortyNineOuterNondefectBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    Finset ({x : V // x ∈ secondLayer G v} ×
      {x : V // x ∈ secondLayer G v}) :=
  (orderFortyNineOuterBranch G v s ×ˢ orderFortyNineOuterBranch G v t).filter
    fun xy ↦ ¬(secondOrderDefectGraph (squareOrderOuterGraph G v)).Adj xy.1 xy.2

/-- Every ordered pair of five-point outer branches is either a defect pair or
a nondefect pair, so their block cardinalities add to 25. -/
theorem orderFortyNine_outerBlock_defect_add_nondefect_eq_twentyFive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    (orderFortyNineOuterDefectBlock G v s t).card +
        (orderFortyNineOuterNondefectBlock G v s t).card = 25 := by
  classical
  rw [orderFortyNineOuterDefectBlock, orderFortyNineOuterNondefectBlock]
  rw [Finset.card_filter_add_card_filter_not, Finset.card_product,
    card_orderFortyNineOuterBranch_eq_five G hfree hmin hcard hv s,
    card_orderFortyNineOuterBranch_eq_five G hfree hmin hcard hv t]

/-- On two distinct outer branches, membership in the nondefect block is
equivalent to having exactly one common neighbor in the outer graph. -/
theorem mem_orderFortyNineOuterNondefectBlock_iff_common_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t)
    (x y : {z : V // z ∈ secondLayer G v}) :
    (x, y) ∈ orderFortyNineOuterNondefectBlock G v s t ↔
      x.1 ∈ secondLayerBranch G v s ∧
      y.1 ∈ secondLayerBranch G v t ∧
      ((squareOrderOuterGraph G v).neighborFinset x ∩
        (squareOrderOuterGraph G v).neighborFinset y).card = 1 := by
  classical
  let R := squareOrderOuterGraph G v
  have hRfree : ¬ containsC4 _ R :=
    squareOrderOuterGraph_not_containsC4 G hfree
  have hxy_of_mem : x.1 ∈ secondLayerBranch G v s →
      y.1 ∈ secondLayerBranch G v t → x ≠ y := by
    intro hx hy hxy
    have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) hst
    apply (Finset.disjoint_left.mp hdisj) hx
    have hval : x.1 = y.1 := congrArg Subtype.val hxy
    simpa [hval] using hy
  constructor
  · intro hmem
    have hm := Finset.mem_filter.mp hmem
    have hp := Finset.mem_product.mp hm.1
    have hx := (Finset.mem_filter.mp hp.1).2
    have hy := (Finset.mem_filter.mp hp.2).2
    have hxy : x ≠ y := hxy_of_mem hx hy
    have hnotmem : y ∉ (secondOrderDefectGraph R).neighborFinset x := by
      simpa [SimpleGraph.mem_neighborFinset, R] using hm.2
    have hc := card_common_eq_if_secondOrderDefect R hRfree x y hxy
    rw [if_neg hnotmem] at hc
    exact ⟨hx, hy, by simpa [R] using hc⟩
  · rintro ⟨hx, hy, hc⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    · intro hD
      have hxy : x ≠ y := hxy_of_mem hx hy
      have hmem : y ∈ (secondOrderDefectGraph R).neighborFinset x := by
        simpa [SimpleGraph.mem_neighborFinset, R] using hD
      have hz := card_common_eq_if_secondOrderDefect R hRfree x y hxy
      rw [if_pos hmem] at hz
      have hz' :
          ((squareOrderOuterGraph G v).neighborFinset x ∩
            (squareOrderOuterGraph G v).neighborFinset y).card = 0 := by
        simpa [R] using hz
      omega

/-- Six local bounds of the form `dᵢ + aᵢ + bᵢ ≤ 5`, together with the paired
bound and the exact total `25`, are all sharp.  In the graph application, `dᵢ`
is a far defect-block cardinality and `aᵢ,bᵢ` are the two crossed miss counts. -/
theorem six_far_bounds_rigid_of_cross_total
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (d a b : ι → ℕ) (paired M N : ℕ)
    (hIcard : I.card = 6)
    (ha : ∑ i ∈ I, a i = M)
    (hb : ∑ i ∈ I, b i = N)
    (hfar : ∀ i ∈ I, d i + a i + b i ≤ 5)
    (hpaired : paired + 5 ≤ M + N)
    (htotal : paired + ∑ i ∈ I, d i = 25) :
    paired + 5 = M + N ∧ ∀ i ∈ I, d i + a i + b i = 5 := by
  have hsumLe :
      (∑ i ∈ I, (d i + a i + b i)) ≤ ∑ _i ∈ I, 5 :=
    Finset.sum_le_sum fun i hi => hfar i hi
  have hconst : (∑ _i ∈ I, 5) = 30 := by
    simp [hIcard]
  have hsplit :
      (∑ i ∈ I, (d i + a i + b i)) =
        (∑ i ∈ I, d i) + (∑ i ∈ I, a i) + (∑ i ∈ I, b i) := by
    simp only [Finset.sum_add_distrib]
  have hreverse : M + N ≤ paired + 5 := by
    rw [hsplit, ha, hb, hconst] at hsumLe
    omega
  have hpairedEq : paired + 5 = M + N := by omega
  have hsumEq :
      (∑ i ∈ I, (d i + a i + b i)) = ∑ _i ∈ I, 5 := by
    rw [hsplit, ha, hb, hconst]
    omega
  refine ⟨hpairedEq, ?_⟩
  exact (Finset.sum_eq_sum_iff_of_le hfar).mp hsumEq

/-- Path-count form of `six_far_bounds_rigid_of_cross_total`.  Every pair of
five-point branches splits into `common` and `defect` endpoint pairs.  Four
intermediate branches and the two endpoint branches give the far lower bound
`20 + aᵢ + bᵢ`; the six intermediate branches give the paired lower bound.
If the cross-defect total is 25, all these path lower bounds are exact. -/
theorem six_branch_path_counts_rigid
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (defect common a b : ι → ℕ) (pairedDefect pairedCommon M N : ℕ)
    (hIcard : I.card = 6)
    (ha : ∑ i ∈ I, a i = M)
    (hb : ∑ i ∈ I, b i = N)
    (hfarPartition : ∀ i ∈ I, defect i + common i = 25)
    (hfarPaths : ∀ i ∈ I, 20 + a i + b i ≤ common i)
    (hpairedPartition : pairedDefect + pairedCommon = 25)
    (hpairedPaths : 30 ≤ pairedCommon + M + N)
    (htotal : pairedDefect + ∑ i ∈ I, defect i = 25) :
    pairedDefect + 5 = M + N ∧
      pairedCommon + M + N = 30 ∧
      ∀ i ∈ I,
        defect i + a i + b i = 5 ∧ common i = 20 + a i + b i := by
  have hfar : ∀ i ∈ I, defect i + a i + b i ≤ 5 := by
    intro i hi
    have hp := hfarPartition i hi
    have hl := hfarPaths i hi
    omega
  have hpaired : pairedDefect + 5 ≤ M + N := by omega
  obtain ⟨hpairedEq, hfarEq⟩ := six_far_bounds_rigid_of_cross_total
    I defect a b pairedDefect M N hIcard ha hb hfar hpaired htotal
  refine ⟨hpairedEq, ?_, ?_⟩
  · omega
  · intro i hi
    refine ⟨hfarEq i hi, ?_⟩
    have hp := hfarPartition i hi
    have he := hfarEq i hi
    omega

end

end Erdos85
