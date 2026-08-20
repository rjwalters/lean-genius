import Proofs.Erdos85OddSquareOrderNineThreeHighRootNeighborhoodProfile

/-! # Local matching consequences in the q = 9 three-high profiles

Node: B.3 / GAP B-CLASSIFY.  In the second three-high profile, the unique
bin-three vertex lies in all three high-root neighborhoods.  The perfect
matching in each such neighborhood gives it one distinct bin-one partner
per high root.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the `(53,27,0,1,0)` three-high profile, the unique bin-three vertex
has exactly three original-graph neighbors in bin one. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1).card = 3 := by
  classical
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hkx : k x = 3 := (Finset.mem_filter.mp hx).2
  have hxAll : G.neighborFinset x ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · change H.card ≤ (G.neighborFinset x ∩ H).card
      change H.card ≤ k x
      rw [hkx, hhigh]
  have hrootCommon : ∀ a ∈ H,
      (G.neighborFinset a ∩ G.neighborFinset x).card = 1 := by
    intro a ha
    have ha10 : G.degree a = 10 := (Finset.mem_filter.mp ha).2
    have hxa : x ∈ G.neighborSet a := by
      have hax : a ∈ G.neighborFinset x := by
        have : a ∈ G.neighborFinset x ∩ H := by rw [hxAll]; exact ha
        exact (Finset.mem_inter.mp this).1
      exact (G.adj_comm x a).mp ((G.mem_neighborFinset x a).mp hax)
    have hlocal := (squareOrder_degree_succ_highRoot_structure
      G hfree (by norm_num) hmin hcard ha10).2.2 ⟨x, hxa⟩
    rw [degree_induce_neighborSet_eq_card_common] at hlocal
    simpa [Finset.inter_comm] using hlocal
  have hsum : (∑ y ∈ G.neighborFinset x, k y) = 3 := by
    have hswap := sum_card_neighborFinset_inter_comm G (G.neighborFinset x) H
    change (∑ y ∈ G.neighborFinset x, k y) =
      ∑ a ∈ H, (G.neighborFinset a ∩ G.neighborFinset x).card at hswap
    rw [hswap]
    calc
      (∑ a ∈ H, (G.neighborFinset a ∩ G.neighborFinset x).card) =
          ∑ _a ∈ H, 1 := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hrootCommon a ha
      _ = H.card := by simp
      _ = 3 := hhigh
  have hb2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpoint : ∀ y ∈ G.neighborFinset x, k y = if y ∈ B 1 then 1 else 0 := by
    intro y hy
    by_cases hyH : y ∈ H
    · have hzero : k y = 0 := by
        unfold k squareOrderHighIncidenceCount
        rw [Finset.card_eq_zero]
        ext a
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
        intro hay haH
        have hay : G.Adj y a :=
          (G.mem_neighborFinset y a).mp hay
        exact hp.high_independent hyH haH hay
      have hynotB : y ∉ B 1 := by
        intro hyB
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyB).1).2 hyH
      simp [hzero, hynotB]
    · have hyLow : y ∈ Finset.univ \ H := Finset.mem_sdiff.mpr ⟨by simp, hyH⟩
      have hkle : k y ≤ 4 := by
        rcases hp.degree_dichotomy y with hlo | hhi
        · have := hp.low_incidence_bound hlo
          change 2 * k y ≤ 9 at this
          omega
        · exact (hyH (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
      have hyNot3 : k y ≠ 3 := by
        intro hky
        have hyB3 : y ∈ B 3 := Finset.mem_filter.mpr ⟨hyLow, hky⟩
        have hyx : y = x := Finset.card_le_one.mp (by omega) y hyB3 x hx
        subst y
        exact G.loopless.irrefl x ((G.mem_neighborFinset x x).mp hy)
      have hyNot2 : k y ≠ 2 := by
        intro hky
        have : y ∈ B 2 := Finset.mem_filter.mpr ⟨hyLow, hky⟩
        simpa [hb2] using this
      have hyNot4 : k y ≠ 4 := by
        intro hky
        have : y ∈ B 4 := Finset.mem_filter.mpr ⟨hyLow, hky⟩
        simpa [hb4] using this
      have hk01 : k y = 0 ∨ k y = 1 := by omega
      rcases hk01 with hk0 | hk1
      · have hynotB : y ∉ B 1 := by
          intro hyB
          have hky := (Finset.mem_filter.mp hyB).2
          change k y = 1 at hky
          omega
        simp [hk0, hynotB]
      · have hyB : y ∈ B 1 := Finset.mem_filter.mpr ⟨hyLow, hk1⟩
        simp [hk1, hyB]
  calc
    (G.neighborFinset x ∩ B 1).card =
        ∑ y ∈ G.neighborFinset x, if y ∈ B 1 then 1 else 0 := by
          simp
    _ = ∑ y ∈ G.neighborFinset x, k y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact (hpoint y hy).symm
    _ = 3 := hsum

/-- The full original-neighborhood census of the rare bin-three vertex in
the second three-high profile is `3H + 3B₁ + 3B₀`. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    (G.neighborFinset x ∩ H).card = 3 ∧
      (G.neighborFinset x ∩ B 1).card = 3 ∧
      (G.neighborFinset x ∩ B 0).card = 3 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hkx : k x = 3 := (Finset.mem_filter.mp hx).2
  have hxHigh : G.neighborFinset x ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · change H.card ≤ k x
      rw [hkx, hhigh]
  have hHighCard : (G.neighborFinset x ∩ H).card = 3 := by
    rw [hxHigh, hhigh]
  have hB1 :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hxdeg : G.degree x = 9 := by
    have hxLow := (Finset.mem_filter.mp hx).1
    have hxNotHigh := (Finset.mem_sdiff.mp hxLow).2
    rcases hp.degree_dichotomy x with hlo | hhi
    · exact hlo
    · exact (hxNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hb2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hlowPartition :
      G.neighborFinset x \ H =
        (G.neighborFinset x ∩ B 0) ∪ (G.neighborFinset x ∩ B 1) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨hy, hyNotHigh⟩
      have hyLow : y ∈ Finset.univ \ H :=
        Finset.mem_sdiff.mpr ⟨by simp, hyNotHigh⟩
      have hkle : k y ≤ 4 := by
        rcases hp.degree_dichotomy y with hlo | hhi
        · have := hp.low_incidence_bound hlo
          change 2 * k y ≤ 9 at this
          omega
        · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
      have hkNot2 : k y ≠ 2 := by
        intro hky
        have : y ∈ B 2 := Finset.mem_filter.mpr ⟨hyLow, hky⟩
        simpa [hb2] using this
      have hkNot3 : k y ≠ 3 := by
        intro hky
        have hyB3 : y ∈ B 3 := Finset.mem_filter.mpr ⟨hyLow, hky⟩
        have hyx : y = x := Finset.card_le_one.mp (by omega) y hyB3 x hx
        subst y
        exact G.loopless.irrefl x ((G.mem_neighborFinset x x).mp hy)
      have hkNot4 : k y ≠ 4 := by
        intro hky
        have : y ∈ B 4 := Finset.mem_filter.mpr ⟨hyLow, hky⟩
        simpa [hb4] using this
      have hk01 : k y = 0 ∨ k y = 1 := by omega
      rcases hk01 with hk0 | hk1
      · exact Or.inl ⟨hy, Finset.mem_filter.mpr ⟨hyLow, hk0⟩⟩
      · exact Or.inr ⟨hy, Finset.mem_filter.mpr ⟨hyLow, hk1⟩⟩
    · rintro (⟨hy, hyB⟩ | ⟨hy, hyB⟩)
      · exact ⟨hy, (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyB).1).2⟩
      · exact ⟨hy, (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyB).1).2⟩
  have hdisj : Disjoint (G.neighborFinset x ∩ B 0)
      (G.neighborFinset x ∩ B 1) := by
    rw [Finset.disjoint_left]
    intro y hy0 hy1
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy0).2).2
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy1).2).2
    omega
  have hlowCard : (G.neighborFinset x \ H).card = 6 := by
    rw [Finset.card_sdiff]
    rw [G.card_neighborFinset_eq_degree, hxdeg]
    have hinter : (H ∩ G.neighborFinset x).card = 3 := by
      simpa [Finset.inter_comm] using hHighCard
    omega
  have hB0 : (G.neighborFinset x ∩ B 0).card = 3 := by
    rw [hlowPartition, Finset.card_union_of_disjoint hdisj, hB1] at hlowCard
    omega
  exact ⟨hHighCard, hB1, hB0⟩

end

end Erdos85

#print axioms
  Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
#print axioms
  Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
