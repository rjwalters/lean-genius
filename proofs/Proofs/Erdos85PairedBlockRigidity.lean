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

/-- Inclusion-exclusion in the form used for a two-step branch composition.
If `a` elements fail the first predicate and `b` fail the second, the elements
satisfying both predicates, together with those two deficits, cover `S`. -/
theorem card_le_card_filter_and_add_filter_not_add_filter_not
    {α : Type*} [DecidableEq α]
    (S : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    S.card ≤ (S.filter fun x ↦ P x ∧ Q x).card +
      (S.filter fun x ↦ ¬P x).card + (S.filter fun x ↦ ¬Q x).card := by
  let A := S.filter P
  have hP := Finset.card_filter_add_card_filter_not (s := S) (p := P)
  have hQ := Finset.card_filter_add_card_filter_not (s := A) (p := Q)
  have hA : A.card + (S.filter fun x ↦ ¬P x).card = S.card := by
    simpa [A] using hP
  have hsub : (A.filter fun x ↦ ¬Q x) ⊆ S.filter fun x ↦ ¬Q x := by
    intro x hx
    have hm := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm.1).1, hm.2⟩
  have hle := Finset.card_le_card hsub
  have hgood : A.filter Q = S.filter fun x ↦ P x ∧ Q x := by
    ext x
    simp [A, and_assoc]
  rw [hgood] at hQ
  omega

/-- Middle-branch vertices which have a neighbor in each of two specified
outer branches.  The branch matching property makes both neighbors unique. -/
def twoSidedMiddleVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (u s t : {z : V // z ∈ G.neighborSet v}) : Finset V :=
  (secondLayerBranch G v u).filter fun q ↦
    (G.neighborFinset q ∩ secondLayerBranch G v s).card = 1 ∧
    (G.neighborFinset q ∩ secondLayerBranch G v t).card = 1

/-- A five-point middle branch supplies at least `5 - m_us - m_ut`
two-sided middle vertices, expressed without truncated subtraction. -/
theorem five_le_twoSidedMiddle_add_misses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (u s t : {z : V // z ∈ G.neighborSet v}) :
    5 ≤ (twoSidedMiddleVertices G v u s t).card +
      highBranchMissCount G v u s + highBranchMissCount G v u t := by
  classical
  let B := secondLayerBranch G v u
  let P : V → Prop := fun q ↦
    (G.neighborFinset q ∩ secondLayerBranch G v s).card = 1
  let Q : V → Prop := fun q ↦
    (G.neighborFinset q ∩ secondLayerBranch G v t).card = 1
  have hnotP : B.filter (fun q ↦ ¬P q) =
      B.filter fun q ↦
        (G.neighborFinset q ∩ secondLayerBranch G v s).card = 0 := by
    ext q
    simp only [Finset.mem_filter]
    refine and_congr_right fun hq ↦ ?_
    have hqs : q ≠ s.1 := by
      intro h
      have hout := (Finset.mem_sdiff.mp hq).2
      apply hout
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      apply Or.inr
      rw [h]
      exact s.2
    have hle := card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v q s hqs
    omega
  have hnotQ : B.filter (fun q ↦ ¬Q q) =
      B.filter fun q ↦
        (G.neighborFinset q ∩ secondLayerBranch G v t).card = 0 := by
    ext q
    simp only [Finset.mem_filter]
    refine and_congr_right fun hq ↦ ?_
    have hqt : q ≠ t.1 := by
      intro h
      have hout := (Finset.mem_sdiff.mp hq).2
      apply hout
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      apply Or.inr
      rw [h]
      exact t.2
    have hle := card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v q t hqt
    omega
  have hcover :=
    card_le_card_filter_and_add_filter_not_add_filter_not B P Q
  have hBcard : B.card = 5 := by
    exact orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
      G hfree hmin hcard hv u
  rw [hnotP, hnotQ, hBcard] at hcover
  simpa [B, P, Q, twoSidedMiddleVertices,
    highBranchMissCount] using hcover

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

/-- Any finset of outer vertices having unique neighbors in two distinct
branches injects into the corresponding nondefect endpoint block. -/
theorem card_middleSelectors_le_nondefectBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (W : Finset V) (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t)
    (hWSecond : ∀ q ∈ W, q ∈ secondLayer G v)
    (hleftCard : ∀ q ∈ W,
      (G.neighborFinset q ∩ secondLayerBranch G v s).card = 1)
    (hrightCard : ∀ q ∈ W,
      (G.neighborFinset q ∩ secondLayerBranch G v t).card = 1) :
    W.card ≤
      (orderFortyNineOuterNondefectBlock G v s t).card := by
  classical
  let R := squareOrderOuterGraph G v
  let K := {q : V // q ∈ W}
  have hleftPos : ∀ q : K,
      0 < (G.neighborFinset q.1 ∩ secondLayerBranch G v s).card := by
    intro q
    have hq := hleftCard q.1 q.2
    rw [hq]
    norm_num
  have hrightPos : ∀ q : K,
      0 < (G.neighborFinset q.1 ∩ secondLayerBranch G v t).card := by
    intro q
    have hq := hrightCard q.1 q.2
    rw [hq]
    norm_num
  let left : K → V := fun q ↦
    (Finset.card_pos.mp (hleftPos q)).choose
  let right : K → V := fun q ↦
    (Finset.card_pos.mp (hrightPos q)).choose
  have hleftMem : ∀ q : K,
      left q ∈ G.neighborFinset q.1 ∩ secondLayerBranch G v s := by
    intro q
    exact (Finset.card_pos.mp (hleftPos q)).choose_spec
  have hrightMem : ∀ q : K,
      right q ∈ G.neighborFinset q.1 ∩ secondLayerBranch G v t := by
    intro q
    exact (Finset.card_pos.mp (hrightPos q)).choose_spec
  have hleftSecond : ∀ q : K, left q ∈ secondLayer G v := by
    intro q
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_univ _, (Finset.mem_inter.mp (hleftMem q)).2⟩
  have hrightSecond : ∀ q : K, right q ∈ secondLayer G v := by
    intro q
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr
      ⟨t, Finset.mem_univ _, (Finset.mem_inter.mp (hrightMem q)).2⟩
  let leftOuter : K → {z : V // z ∈ secondLayer G v} := fun q ↦
    ⟨left q, hleftSecond q⟩
  let rightOuter : K → {z : V // z ∈ secondLayer G v} := fun q ↦
    ⟨right q, hrightSecond q⟩
  let endpoint : K →
      {p // p ∈ orderFortyNineOuterNondefectBlock G v s t} := fun q ↦
    ⟨(leftOuter q, rightOuter q), by
      apply (mem_orderFortyNineOuterNondefectBlock_iff_common_eq_one
        G hfree s t hst (leftOuter q) (rightOuter q)).mpr
      refine ⟨(Finset.mem_inter.mp (hleftMem q)).2,
        (Finset.mem_inter.mp (hrightMem q)).2, ?_⟩
      have hqSecond : q.1 ∈ secondLayer G v := hWSecond q.1 q.2
      let qOuter : {z : V // z ∈ secondLayer G v} := ⟨q.1, hqSecond⟩
      have hqLeft : R.Adj (leftOuter q) qOuter := by
        exact ((G.mem_neighborFinset q.1 (left q)).mp
          (Finset.mem_inter.mp (hleftMem q)).1).symm
      have hqRight : R.Adj (rightOuter q) qOuter := by
        exact ((G.mem_neighborFinset q.1 (right q)).mp
          (Finset.mem_inter.mp (hrightMem q)).1).symm
      have hmem : qOuter ∈ R.neighborFinset (leftOuter q) ∩
          R.neighborFinset (rightOuter q) :=
        Finset.mem_inter.mpr
          ⟨(R.mem_neighborFinset (leftOuter q) qOuter).mpr hqLeft,
            (R.mem_neighborFinset (rightOuter q) qOuter).mpr hqRight⟩
      have hxy : leftOuter q ≠ rightOuter q := by
        intro h
        have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
          (by simp) (by simp) hst
        apply (Finset.disjoint_left.mp hdisj)
          (Finset.mem_inter.mp (hleftMem q)).2
        have hv : left q = right q := congrArg Subtype.val h
        simpa [hv] using (Finset.mem_inter.mp (hrightMem q)).2
      have hle := common_le_one_of_not_containsC4
        (squareOrderOuterGraph_not_containsC4 G hfree)
        (leftOuter q) (rightOuter q) hxy
      have hpos : 0 < (R.neighborFinset (leftOuter q) ∩
          R.neighborFinset (rightOuter q)).card :=
        Finset.card_pos.mpr ⟨qOuter, hmem⟩
      exact Nat.le_antisymm hle hpos⟩
  have hinj : Function.Injective endpoint := by
    intro q₁ q₂ heq
    apply Subtype.ext
    change q₁.1 = q₂.1
    have hp := congrArg (fun z ↦ z.1) heq
    have hl : leftOuter q₁ = leftOuter q₂ := congrArg Prod.fst hp
    have hr : rightOuter q₁ = rightOuter q₂ := congrArg Prod.snd hp
    have hq₁Second : q₁.1 ∈ secondLayer G v := hWSecond q₁.1 q₁.2
    have hq₂Second : q₂.1 ∈ secondLayer G v := hWSecond q₂.1 q₂.2
    let z₁ : {z : V // z ∈ secondLayer G v} := ⟨q₁.1, hq₁Second⟩
    let z₂ : {z : V // z ∈ secondLayer G v} := ⟨q₂.1, hq₂Second⟩
    have hz₁ : z₁ ∈ R.neighborFinset (leftOuter q₁) ∩
        R.neighborFinset (rightOuter q₁) := by
      apply Finset.mem_inter.mpr
      constructor
      · exact (R.mem_neighborFinset (leftOuter q₁) z₁).mpr
          (((G.mem_neighborFinset q₁.1 (left q₁)).mp
            (Finset.mem_inter.mp (hleftMem q₁)).1).symm)
      · exact (R.mem_neighborFinset (rightOuter q₁) z₁).mpr
          (((G.mem_neighborFinset q₁.1 (right q₁)).mp
            (Finset.mem_inter.mp (hrightMem q₁)).1).symm)
    have hz₂ : z₂ ∈ R.neighborFinset (leftOuter q₁) ∩
        R.neighborFinset (rightOuter q₁) := by
      apply Finset.mem_inter.mpr
      constructor
      · rw [hl]
        exact (R.mem_neighborFinset (leftOuter q₂) z₂).mpr
          (((G.mem_neighborFinset q₂.1 (left q₂)).mp
            (Finset.mem_inter.mp (hleftMem q₂)).1).symm)
      · rw [hr]
        exact (R.mem_neighborFinset (rightOuter q₂) z₂).mpr
          (((G.mem_neighborFinset q₂.1 (right q₂)).mp
            (Finset.mem_inter.mp (hrightMem q₂)).1).symm)
    have hcard : (R.neighborFinset (leftOuter q₁) ∩
        R.neighborFinset (rightOuter q₁)).card = 1 :=
      (mem_orderFortyNineOuterNondefectBlock_iff_common_eq_one
        G hfree s t hst (leftOuter q₁) (rightOuter q₁)).mp
          (endpoint q₁).2 |>.2.2
    have hz : z₁ = z₂ :=
      (Finset.card_le_one.mp (by omega)) z₁ hz₁ z₂ hz₂
    exact congrArg (fun z : {w : V // w ∈ secondLayer G v} ↦ z.1) hz
  simpa [K] using
    Fintype.card_le_of_injective endpoint hinj

/-- Two-sided vertices from one middle branch are a special case of the
selector injection. -/
theorem card_twoSidedMiddleVertices_le_nondefectBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (u s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t) :
    (twoSidedMiddleVertices G v u s t).card ≤
      (orderFortyNineOuterNondefectBlock G v s t).card := by
  apply card_middleSelectors_le_nondefectBlock G hfree
    (twoSidedMiddleVertices G v u s t) s t hst
  · intro q hq
    have hqBranch := (Finset.mem_filter.mp hq).1
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hqBranch⟩
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.2

/-- A single middle branch contributes the expected deficient-matching lower
bound to the nondefect endpoint block. -/
theorem five_le_nondefectBlock_add_middle_misses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (u s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t) :
    5 ≤ (orderFortyNineOuterNondefectBlock G v s t).card +
      highBranchMissCount G v u s + highBranchMissCount G v u t := by
  have hlower := five_le_twoSidedMiddle_add_misses
    G hfree hmin hcard hv u s t
  have hinj := card_twoSidedMiddleVertices_le_nondefectBlock
    G hfree u s t hst
  omega

/-- The union of two-sided middle vertices over a collection of branches. -/
def twoSidedMiddleVerticesAcross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (U : Finset {z : V // z ∈ G.neighborSet v})
    (s t : {z : V // z ∈ G.neighborSet v}) : Finset V :=
  U.biUnion fun u ↦ twoSidedMiddleVertices G v u s t

/-- Contributions from distinct middle branches are disjoint and jointly
inject into the nondefect endpoint block.  Summing the five-point
inclusion-exclusion bound gives the multi-branch path inequality. -/
theorem five_mul_card_le_nondefectBlock_add_sum_middle_misses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (U : Finset {z : V // z ∈ G.neighborSet v})
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t) :
    5 * U.card ≤
      (orderFortyNineOuterNondefectBlock G v s t).card +
      (∑ u ∈ U, highBranchMissCount G v u s) +
      (∑ u ∈ U, highBranchMissCount G v u t) := by
  classical
  have hdisj : (↑U : Set {z : V // z ∈ G.neighborSet v}).PairwiseDisjoint
      (fun u ↦ twoSidedMiddleVertices G v u s t) := by
    intro u hu w hw huw
    change Disjoint (twoSidedMiddleVertices G v u s t)
      (twoSidedMiddleVertices G v w s t)
    rw [Finset.disjoint_left]
    intro q hqu hqw
    have hquBranch := (Finset.mem_filter.mp hqu).1
    have hqwBranch := (Finset.mem_filter.mp hqw).1
    have hbranches := secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) huw
    exact (Finset.disjoint_left.mp hbranches) hquBranch hqwBranch
  have hunionCard : (twoSidedMiddleVerticesAcross G v U s t).card =
      ∑ u ∈ U, (twoSidedMiddleVertices G v u s t).card := by
    exact Finset.card_biUnion hdisj
  have hselector : (twoSidedMiddleVerticesAcross G v U s t).card ≤
      (orderFortyNineOuterNondefectBlock G v s t).card := by
    apply card_middleSelectors_le_nondefectBlock G hfree
      (twoSidedMiddleVerticesAcross G v U s t) s t hst
    · intro q hq
      rcases Finset.mem_biUnion.mp hq with ⟨u, hu, hqu⟩
      have hqBranch := (Finset.mem_filter.mp hqu).1
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hqBranch⟩
    · intro q hq
      rcases Finset.mem_biUnion.mp hq with ⟨u, _hu, hqu⟩
      exact (Finset.mem_filter.mp hqu).2.1
    · intro q hq
      rcases Finset.mem_biUnion.mp hq with ⟨u, _hu, hqu⟩
      exact (Finset.mem_filter.mp hqu).2.2
  have hsum : (∑ _u ∈ U, 5) ≤
      ∑ u ∈ U, ((twoSidedMiddleVertices G v u s t).card +
        highBranchMissCount G v u s + highBranchMissCount G v u t) := by
    apply Finset.sum_le_sum
    intro u hu
    exact five_le_twoSidedMiddle_add_misses G hfree hmin hcard hv u s t
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hsum
  omega

/-- For a paired root-branch pair, all six remaining branches contribute.
The two miss-column sums are the matched counts of the paired branches, so
the paired nondefect block has the required `30 - M_s - M_t` lower bound. -/
theorem thirty_le_paired_nondefectBlock_add_matchedCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    30 ≤ (orderFortyNineOuterNondefectBlock G v s t).card +
      highBranchMatchedCount G v s + highBranchMatchedCount G v t := by
  classical
  let U : Finset {z : V // z ∈ G.neighborSet v} :=
    (Finset.univ.erase s).erase t
  have hstne : s ≠ t := by
    intro h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ hst)
  have hIndexCard : Fintype.card {z : V // z ∈ G.neighborSet v} = 8 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hUcard : U.card = 6 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (by simp [hstne.symm] :
      t ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}).erase s)]
    rw [Finset.card_erase_of_mem (by simp :
      s ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}))]
    rw [Finset.card_univ, hIndexCard]
  have hsymm : ∀ a b : {z : V // z ∈ G.neighborSet v},
      highBranchMissCount G v a b = highBranchMissCount G v b a := by
    intro a b
    apply highBranchMissCount_comm_of_equal_card G hfree a b
    rw [orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv a,
      orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv b]
  have hrowS : (∑ u ∈ U, highBranchMissCount G v u s) =
      highBranchMatchedCount G v s := by
    calc
      (∑ u ∈ U, highBranchMissCount G v u s) =
          ∑ u ∈ U, highBranchMissCount G v s u := by
        apply Finset.sum_congr rfl
        intro u _
        exact hsymm u s
      _ = highBranchMatchedCount G v s := by
        exact sum_far_highBranchMissCount_eq_matchedCount
          G hfree hv hexternal s t hst (by
            intro a ha
            apply houterDegree
            rw [secondLayer]
            exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, ha⟩)
  have hrowT : (∑ u ∈ U, highBranchMissCount G v u t) =
      highBranchMatchedCount G v t := by
    have hUcomm : ((Finset.univ.erase t).erase s) = U := by
      ext u
      simp [U, and_comm]
    calc
      (∑ u ∈ U, highBranchMissCount G v u t) =
          ∑ u ∈ U, highBranchMissCount G v t u := by
        apply Finset.sum_congr rfl
        intro u _
        exact hsymm u t
      _ = highBranchMatchedCount G v t := by
        rw [← hUcomm]
        exact sum_far_highBranchMissCount_eq_matchedCount
          G hfree hv hexternal t s hst.symm (by
            intro a ha
            apply houterDegree
            rw [secondLayer]
            exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ha⟩)
  have hpaths := five_mul_card_le_nondefectBlock_add_sum_middle_misses
    G hfree hmin hcard hv U s t hstne
  rw [hUcard, hrowS, hrowT] at hpaths
  norm_num at hpaths ⊢
  exact hpaths

/-- In a five-point branch, the vertices missed by its internal matching and
the vertices covered by that matching partition the branch. -/
theorem selfMiss_add_matchedCount_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    highBranchMissCount G v s s + highBranchMatchedCount G v s = 5 := by
  classical
  let B := secondLayerBranch G v s
  let P : V → Prop := fun q ↦
    (G.neighborFinset q ∩ B).card = 1
  have hnot : B.filter (fun q ↦ ¬P q) =
      B.filter fun q ↦ (G.neighborFinset q ∩ B).card = 0 := by
    ext q
    simp only [Finset.mem_filter]
    refine and_congr_right fun hq ↦ ?_
    have hqs : q ≠ s.1 := by
      intro h
      exact (Finset.mem_sdiff.mp hq).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr (h ▸ s.2))
    have hle := card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v q s hqs
    dsimp [B, P]
    omega
  have hpartition := Finset.card_filter_add_card_filter_not (s := B) (p := P)
  rw [hnot] at hpartition
  have hBcard : B.card = 5 :=
    orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
      G hfree hmin hcard hv s
  rw [hBcard] at hpartition
  simpa [B, P, highBranchMissCount, highBranchMatchedCount, add_comm]
    using hpartition

/-- Uniform far-block lower bound once the two six-branch miss-column sums
are identified.  The subsequent graph lemma supplies these identities from
the row-sum theorem and the two omitted mate branches. -/
theorem twenty_add_cross_misses_le_far_nondefectBlock_of_column_sums
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (U : Finset {z : V // z ∈ G.neighborSet v})
    (s t sCross tCross : {z : V // z ∈ G.neighborSet v})
    (hst : s ≠ t) (hUcard : U.card = 6)
    (hcolS : (∑ u ∈ U, highBranchMissCount G v u s) +
      highBranchMissCount G v s sCross = 5)
    (hcolT : (∑ u ∈ U, highBranchMissCount G v u t) +
      highBranchMissCount G v t tCross = 5) :
    20 + highBranchMissCount G v s sCross +
        highBranchMissCount G v t tCross ≤
      (orderFortyNineOuterNondefectBlock G v s t).card := by
  have hpaths := five_mul_card_le_nondefectBlock_add_sum_middle_misses
    G hfree hmin hcard hv U s t hst
  rw [hUcard] at hpaths
  norm_num at hpaths
  omega

/-- Remove a branch's mate and one additional branch from the index set.  The
remaining miss column, plus the crossed miss to the additionally omitted
branch, has total five. -/
theorem sum_omit_mate_omit_cross_add_crossMiss_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (s mate cross : {z : V // z ∈ G.neighborSet v})
    (hsmate : G.Adj s.1 mate.1) (hcrossmate : cross ≠ mate) :
    (∑ u ∈ ((Finset.univ.erase mate).erase cross),
        highBranchMissCount G v u s) +
      highBranchMissCount G v s cross = 5 := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let f : P → ℕ := fun u ↦ highBranchMissCount G v s u
  have hsmateNe : s ≠ mate := by
    intro h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ hsmate)
  have hsymm : ∀ u : P,
      highBranchMissCount G v u s = highBranchMissCount G v s u := by
    intro u
    apply highBranchMissCount_comm_of_equal_card G hfree u s
    rw [orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv u,
      orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv s]
  have hrow : (∑ u ∈ ((Finset.univ.erase s).erase mate), f u) =
      highBranchMatchedCount G v s := by
    exact sum_far_highBranchMissCount_eq_matchedCount
      G hfree hv hexternal s mate hsmate (by
        intro a ha
        apply houterDegree
        rw [secondLayer]
        exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, ha⟩)
  have hself := selfMiss_add_matchedCount_eq_five
    G hfree hmin hcard hv s
  have hcrossMem : cross ∈ (Finset.univ : Finset P).erase mate := by
    simp [hcrossmate]
  have hsMem : s ∈ (Finset.univ : Finset P).erase mate := by
    simp [hsmateNe]
  have hcrossErase := Finset.sum_erase_add
    ((Finset.univ : Finset P).erase mate) f hcrossMem
  have hsErase := Finset.sum_erase_add
    ((Finset.univ : Finset P).erase mate) f hsMem
  have hrowSet : ((Finset.univ : Finset P).erase mate).erase s =
      (Finset.univ.erase s).erase mate := by
    ext u
    simp [and_comm]
  rw [hrowSet, hrow] at hsErase
  have hcol : (∑ u ∈ ((Finset.univ.erase mate).erase cross),
      highBranchMissCount G v u s) =
      ∑ u ∈ ((Finset.univ.erase mate).erase cross), f u := by
    apply Finset.sum_congr rfl
    intro u _
    exact hsymm u
  rw [hcol]
  change f s + highBranchMatchedCount G v s = 5 at hself
  calc
    (∑ u ∈ ((Finset.univ.erase mate).erase cross), f u) + f cross =
        ∑ u ∈ (Finset.univ : Finset P).erase mate, f u := hcrossErase
    _ = highBranchMatchedCount G v s + f s := hsErase.symm
    _ = f s + highBranchMatchedCount G v s := Nat.add_comm _ _
    _ = 5 := hself

/-- **Far-block path lower bound.**  If `s,t` have distinct mates, the six
branches other than those mates give at least
`20 + m_{s,bar t} + m_{t,bar s}` nondefect endpoint pairs. -/
theorem twenty_add_cross_misses_le_far_nondefectBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (s t mateS mateT : {z : V // z ∈ G.neighborSet v})
    (hst : s ≠ t)
    (hsMate : G.Adj s.1 mateS.1) (htMate : G.Adj t.1 mateT.1)
    (hmates : mateS ≠ mateT) :
    20 + highBranchMissCount G v s mateT +
        highBranchMissCount G v t mateS ≤
      (orderFortyNineOuterNondefectBlock G v s t).card := by
  classical
  let U : Finset {z : V // z ∈ G.neighborSet v} :=
    (Finset.univ.erase mateS).erase mateT
  have hIndexCard : Fintype.card {z : V // z ∈ G.neighborSet v} = 8 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hUcard : U.card = 6 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (by simp [hmates.symm] :
      mateT ∈ (Finset.univ :
        Finset {z : V // z ∈ G.neighborSet v}).erase mateS)]
    rw [Finset.card_erase_of_mem (by simp :
      mateS ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}))]
    rw [Finset.card_univ, hIndexCard]
  have hcolS := sum_omit_mate_omit_cross_add_crossMiss_eq_five
    G hfree hmin hcard hv hexternal houterDegree
      s mateS mateT hsMate hmates.symm
  have hcolT := sum_omit_mate_omit_cross_add_crossMiss_eq_five
    G hfree hmin hcard hv hexternal houterDegree
      t mateT mateS htMate hmates
  have hUcomm : ((Finset.univ.erase mateT).erase mateS) = U := by
    ext u
    simp [U, and_comm]
  rw [hUcomm] at hcolT
  exact twenty_add_cross_misses_le_far_nondefectBlock_of_column_sums
    G hfree hmin hcard hv U s t mateT mateS hst hUcard hcolS hcolT

private theorem six_far_bounds_rigid_core
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (d a b : ι → ℕ) (paired M N : ℕ)
    (hIcard : I.card = 6)
    (ha : ∑ i ∈ I, a i = M)
    (hb : ∑ i ∈ I, b i = N)
    (hfar : ∀ i ∈ I, d i + a i + b i ≤ 5)
    (hpaired : paired + 5 ≤ M + N)
    (htotal : paired + ∑ i ∈ I, d i = 25) :
    paired + 5 = M + N ∧ ∀ i ∈ I, d i + a i + b i = 5 := by
  have hsumLe : (∑ i ∈ I, (d i + a i + b i)) ≤ ∑ _i ∈ I, 5 :=
    Finset.sum_le_sum fun i hi => hfar i hi
  have hconst : (∑ _i ∈ I, 5) = 30 := by simp [hIcard]
  have hsplit : (∑ i ∈ I, (d i + a i + b i)) =
      (∑ i ∈ I, d i) + (∑ i ∈ I, a i) + (∑ i ∈ I, b i) := by
    simp only [Finset.sum_add_distrib]
  have hreverse : M + N ≤ paired + 5 := by
    rw [hsplit, ha, hb, hconst] at hsumLe
    omega
  have hpairedEq : paired + 5 = M + N := by omega
  have hsumEq : (∑ i ∈ I, (d i + a i + b i)) = ∑ _i ∈ I, 5 := by
    rw [hsplit, ha, hb, hconst]
    omega
  exact ⟨hpairedEq, (Finset.sum_eq_sum_iff_of_le hfar).mp hsumEq⟩

private theorem six_branch_path_counts_rigid_core
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
  obtain ⟨hpairedEq, hfarEq⟩ := six_far_bounds_rigid_core
    I defect a b pairedDefect M N hIcard ha hb hfar hpaired htotal
  refine ⟨hpairedEq, ?_, ?_⟩
  · omega
  · intro i hi
    refine ⟨hfarEq i hi, ?_⟩
    have hp := hfarPartition i hi
    have he := hfarEq i hi
    omega

/-- **Exact block rigidity with an explicit mate involution.**  Once the
six far defect blocks and the paired defect block have the known total 25,
the graph-facing path bounds force every block formula to be an equality. -/
theorem exact_outerDefectBlocks_of_mate_involution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (htotal :
      (orderFortyNineOuterDefectBlock G v s (mate s)).card +
        (∑ u ∈ ((Finset.univ.erase s).erase (mate s)),
          (orderFortyNineOuterDefectBlock G v s u).card) = 25) :
    (orderFortyNineOuterDefectBlock G v s (mate s)).card + 5 =
        highBranchMatchedCount G v s +
          highBranchMatchedCount G v (mate s) ∧
      ∀ u ∈ ((Finset.univ.erase s).erase (mate s)),
        (orderFortyNineOuterDefectBlock G v s u).card +
          highBranchMissCount G v s (mate u) +
          highBranchMissCount G v u (mate s) = 5 := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let U : Finset P := (Finset.univ.erase s).erase (mate s)
  have hmateNe : s ≠ mate s := by
    intro h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ hmateAdj s)
  have hIndexCard : Fintype.card P = 8 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hUcard : U.card = 6 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (by simp [hmateNe.symm] :
      mate s ∈ (Finset.univ : Finset P).erase s)]
    rw [Finset.card_erase_of_mem (by simp : s ∈ (Finset.univ : Finset P))]
    rw [Finset.card_univ, hIndexCard]
  have hmateInj : Function.Injective mate := hmateInv.injective
  have hmateMem : ∀ u ∈ U, mate u ∈ U := by
    intro u hu
    have huRaw : u ≠ mate s ∧ u ≠ s := by simpa [U] using hu
    have hu' : u ≠ s ∧ u ≠ mate s := ⟨huRaw.2, huRaw.1⟩
    have hmus : mate u ≠ s := by
      intro h
      have hh := congrArg mate h
      rw [hmateInv u] at hh
      exact hu'.2 hh
    have hmums : mate u ≠ mate s := by
      intro h
      exact hu'.1 (hmateInj h)
    simp [U, hmus, hmums]
  have hmateSum :
      (∑ u ∈ U, highBranchMissCount G v s (mate u)) =
        ∑ u ∈ U, highBranchMissCount G v s u := by
    apply Finset.sum_bij (fun u _ ↦ mate u)
    · intro u hu
      exact hmateMem u hu
    · intro a _ha b _hb hab
      exact hmateInj hab
    · intro z hz
      refine ⟨mate z, hmateMem z hz, ?_⟩
      exact hmateInv z
    · intro u _
      rfl
  have hrowS : (∑ u ∈ U, highBranchMissCount G v s u) =
      highBranchMatchedCount G v s := by
    exact sum_far_highBranchMissCount_eq_matchedCount
      G hfree hv hexternal s (mate s) (hmateAdj s) (by
        intro a ha
        apply houterDegree
        rw [secondLayer]
        exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, ha⟩)
  have hsymm : ∀ a b : P,
      highBranchMissCount G v a b = highBranchMissCount G v b a := by
    intro a b
    apply highBranchMissCount_comm_of_equal_card G hfree a b
    rw [orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv a,
      orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
        G hfree hmin hcard hv b]
  have hrowMate : (∑ u ∈ U, highBranchMissCount G v u (mate s)) =
      highBranchMatchedCount G v (mate s) := by
    have hUcomm : ((Finset.univ.erase (mate s)).erase s) = U := by
      ext u
      simp [U, and_comm]
    calc
      (∑ u ∈ U, highBranchMissCount G v u (mate s)) =
          ∑ u ∈ U, highBranchMissCount G v (mate s) u := by
        apply Finset.sum_congr rfl
        intro u _
        exact hsymm u (mate s)
      _ = highBranchMatchedCount G v (mate s) := by
        rw [← hUcomm]
        exact sum_far_highBranchMissCount_eq_matchedCount
          G hfree hv hexternal (mate s) s
            (by simpa [hmateInv s] using hmateAdj (mate s)) (by
              intro a ha
              apply houterDegree
              rw [secondLayer]
              exact Finset.mem_biUnion.mpr
                ⟨mate s, Finset.mem_univ _, ha⟩)
  have hpairedPartition :=
    orderFortyNine_outerBlock_defect_add_nondefect_eq_twentyFive
      G hfree hmin hcard hv s (mate s)
  have hpairedPaths := thirty_le_paired_nondefectBlock_add_matchedCounts
    G hfree hmin hcard hv hexternal houterDegree s (mate s) (hmateAdj s)
  have hfarPartition : ∀ u ∈ U,
      (orderFortyNineOuterDefectBlock G v s u).card +
        (orderFortyNineOuterNondefectBlock G v s u).card = 25 := by
    intro u _
    exact orderFortyNine_outerBlock_defect_add_nondefect_eq_twentyFive
      G hfree hmin hcard hv s u
  have hfarPaths : ∀ u ∈ U,
      20 + highBranchMissCount G v s (mate u) +
          highBranchMissCount G v u (mate s) ≤
        (orderFortyNineOuterNondefectBlock G v s u).card := by
    intro u hu
    have huRaw : u ≠ mate s ∧ u ≠ s := by simpa [U] using hu
    have hu' : u ≠ s ∧ u ≠ mate s := ⟨huRaw.2, huRaw.1⟩
    have hmatedist : mate s ≠ mate u := by
      intro h
      exact hu'.1 (hmateInj h.symm)
    exact twenty_add_cross_misses_le_far_nondefectBlock
      G hfree hmin hcard hv hexternal houterDegree
        s u (mate s) (mate u) hu'.1.symm
          (hmateAdj s) (hmateAdj u) hmatedist
  have hr := six_branch_path_counts_rigid_core U
    (fun u ↦ (orderFortyNineOuterDefectBlock G v s u).card)
    (fun u ↦ (orderFortyNineOuterNondefectBlock G v s u).card)
    (fun u ↦ highBranchMissCount G v s (mate u))
    (fun u ↦ highBranchMissCount G v u (mate s))
    (orderFortyNineOuterDefectBlock G v s (mate s)).card
    (orderFortyNineOuterNondefectBlock G v s (mate s)).card
    (highBranchMatchedCount G v s)
    (highBranchMatchedCount G v (mate s))
    hUcard (hmateSum.trans hrowS) hrowMate hfarPartition hfarPaths
    hpairedPartition hpairedPaths (by simpa [U] using htotal)
  exact ⟨hr.1, fun u hu ↦ (hr.2.2 u hu).1⟩

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
