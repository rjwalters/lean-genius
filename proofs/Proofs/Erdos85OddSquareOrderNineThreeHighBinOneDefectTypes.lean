import Proofs.Erdos85OddSquareOrderNineThreeHighLocalMatching

/-! # Bin-one defect types in the q = 9 three-high profile

Node: B.3 / GAP B-CLASSIFY.  The pointwise defect ledger leaves exactly two
possible neighbor types for a bin-one vertex in the first three-high profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the `(54,24,3,0,0)` profile, every bin-one vertex has one of two
exact defect-neighborhood types: `(B₀,B₁,B₂)=(6,0,1)` or `(5,2,0)`. -/
theorem squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 1) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((D.neighborFinset x ∩ B 0).card = 6 ∧
        (D.neighborFinset x ∩ B 1).card = 0 ∧
        (D.neighborFinset x ∩ B 2).card = 1) ∨
      ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 2 ∧
        (D.neighborFinset x ∩ B 2).card = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hB3 : B 3 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
  change D.degree x = 8 - 1 ∧
    (∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y) =
      3 - 1 at hpnt
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
  rw [hB3, hB4] at hpart
  norm_num at hpart
  by_cases htwo : (D.neighborFinset x ∩ B 2).card = 0
  · right
    change (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 2 ∧
      (D.neighborFinset x ∩ B 2).card = 0
    omega
  · left
    change (D.neighborFinset x ∩ B 0).card = 6 ∧
      (D.neighborFinset x ∩ B 1).card = 0 ∧
      (D.neighborFinset x ∩ B 2).card = 1
    omega

/-- A bin-one vertex defect-adjacent to a bin-two witness is necessarily the
exceptional `(B₀,B₁,B₂)=(6,0,1)` type. -/
theorem squareOrderNine_threeHigh_firstProfile_defectMate_binOne_type
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hDxy : (secondOrderDefectGraph G).Adj x y) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (D.neighborFinset y ∩ B 0).card = 6 ∧
      (D.neighborFinset y ∩ B 1).card = 0 ∧
      (D.neighborFinset y ∩ B 2).card = 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have htypes :=
    squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hy
  dsimp only at htypes
  rcases htypes with hexceptional | hordinary
  · exact hexceptional
  · have hxMem : x ∈ D.neighborFinset y ∩ B 2 :=
      Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset y x).mpr hDxy.symm, hx⟩
    have hpos : 0 < (D.neighborFinset y ∩ B 2).card :=
      Finset.card_pos.mpr ⟨x, hxMem⟩
    rw [hordinary.2.2] at hpos
    omega

/-- Exactly three bin-one vertices have a bin-two defect neighbor in the
first three-high profile.  These are precisely the exceptional pointwise
type singled out above. -/
theorem squareOrderNine_threeHigh_firstProfile_exceptional_binOne_card
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 1).card = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1
  have hB3 : B 3 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
  have he12 : squareOrderNineDefectBinEdgeCount G 1 2 = 3 := by
    rcases squareOrderNine_threeHigh_defectQuotient_census
        G hfree hmin hcover hcard hp hhigh with hfirst | hsecond
    · exact hfirst.2.2.2.2.1
    · have he03zero : squareOrderNineDefectBinEdgeCount G 0 3 = 0 := by
        simp [squareOrderNineDefectBinEdgeCount, B, hB3]
      omega
  have hpoint : ∀ y ∈ B 1,
      ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0 ∨
        ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1 := by
    intro y hy
    have ht :=
      squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc3 hc4 hy
    dsimp only at ht
    rcases ht with he | ho
    · exact Or.inr he.2.2
    · exact Or.inl ho.2.2
  change E.card = 3
  calc
    E.card = ∑ y ∈ B 1, if y ∈ E then 1 else 0 := by
      rw [Finset.card_eq_sum_ones]
      simp [E]
      congr 1
      ext y
      simp
    _ = ∑ y ∈ B 1,
        ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card := by
      apply Finset.sum_congr rfl
      intro y hy
      rcases hpoint y hy with hzero | hone
      · have hyNotE : y ∉ E := by simp [E, hzero]
        simp [hyNotE, hzero]
      · have hyE : y ∈ E := by simp [E, hy, hone]
        simp [hyE, hone]
    _ = squareOrderNineDefectBinEdgeCount G 1 2 := by
      rfl
    _ = 3 := he12
end

end Erdos85

#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_defectMate_binOne_type
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_exceptional_binOne_card
