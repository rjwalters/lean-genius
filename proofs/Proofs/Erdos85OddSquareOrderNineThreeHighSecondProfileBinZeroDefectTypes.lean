import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileCore

/-! # Bin-zero defect types in the q = 9 three-high second profile

Node: B.3 / GAP B-CLASSIFY.  The 50 bin-zero vertices split into regular
type `(B₀,B₁,B₃)=(5,3,0)` and exceptional type `(7,0,1)`.  The five
exceptional vertices are precisely the bin-zero defect neighbors of the
unique bin-three vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every bin-zero vertex in the second three-high profile has defect type
`(5,3,0)` or `(7,0,1)` across bins zero, one, and three. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 3 ∧
        (D.neighborFinset x ∩ B 3).card = 0) ∨
      ((D.neighborFinset x ∩ B 0).card = 7 ∧
        (D.neighborFinset x ∩ B 1).card = 0 ∧
        (D.neighborFinset x ∩ B 3).card = 1) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
  norm_num at hpnt
  have hpart := squareOrderNine_defectNeighbor_bin_partition
    G hfree hmin hcard hp x
  dsimp only at hpart
  change
    (∑ j ∈ Finset.range 5, (D.neighborFinset x ∩ B j).card) = D.degree x ∧
      (∑ j ∈ Finset.range 5, j * (D.neighborFinset x ∩ B j).card) =
        ∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y at hpart
  rw [hpnt.1, hpnt.2] at hpart
  norm_num [Finset.sum_range_succ] at hpart
  rw [hB2, hB4] at hpart
  norm_num at hpart
  change
    ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 3 ∧
        (D.neighborFinset x ∩ B 3).card = 0) ∨
      ((D.neighborFinset x ∩ B 0).card = 7 ∧
        (D.neighborFinset x ∩ B 1).card = 0 ∧
        (D.neighborFinset x ∩ B 3).card = 1)
  by_cases hthree : (D.neighborFinset x ∩ B 3).card = 0
  · left
    exact ⟨by omega, by omega, hthree⟩
  · right
    exact ⟨by omega, by omega, by omega⟩

/-- Exactly five bin-zero vertices have a bin-three defect neighbor, hence
exactly five have exceptional type `(7,0,1)`. -/
theorem squareOrderNine_threeHigh_secondProfile_special_binZero_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((B 0).filter fun y => (D.neighborFinset y ∩ B 3).card = 1).card = 5 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 0).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 3).card = 1
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have he03 : squareOrderNineDefectBinEdgeCount G 0 3 = 5 := by
    rcases squareOrderNine_threeHigh_defectQuotient_census
        G hfree hmin hcover hcard hp hhigh with hfirst | hsecond
    · have he02zero : squareOrderNineDefectBinEdgeCount G 0 2 = 0 := by
        simp [squareOrderNineDefectBinEdgeCount, B, hB2]
      omega
    · exact hsecond.2.2.1
  have hpoint : ∀ y ∈ B 0,
      (D.neighborFinset y ∩ B 3).card = 0 ∨
        (D.neighborFinset y ∩ B 3).card = 1 := by
    intro y hy
    have ht :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hy
    dsimp only at ht
    rcases ht with hregular | hspecial
    · exact Or.inl hregular.2.2
    · exact Or.inr hspecial.2.2
  change E.card = 5
  calc
    E.card = ∑ y ∈ B 0, if y ∈ E then 1 else 0 := by
      rw [Finset.card_eq_sum_ones]
      simp [E]
      congr 1
      ext y
      simp
    _ = ∑ y ∈ B 0, (D.neighborFinset y ∩ B 3).card := by
      apply Finset.sum_congr rfl
      intro y hy
      rcases hpoint y hy with hzero | hone
      · have hzero' :
            ((secondOrderDefectGraph G).neighborFinset y ∩ B 3).card = 0 := by
          simpa [D] using hzero
        have hyNotE : y ∉ E := by simp [E, hzero']
        simp [hyNotE, hzero]
      · have hone' :
            ((secondOrderDefectGraph G).neighborFinset y ∩ B 3).card = 1 := by
          simpa [D] using hone
        have hyE : y ∈ E := by simp [E, hy, hone']
        simp [hyE, hone]
    _ = squareOrderNineDefectBinEdgeCount G 0 3 := by rfl
    _ = 5 := he03

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_binZero_card
