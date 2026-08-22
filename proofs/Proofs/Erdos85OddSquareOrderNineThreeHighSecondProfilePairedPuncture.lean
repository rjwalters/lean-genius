import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileRowCover

/-! # Paired punctures in the q = 9 second three-high profile

Node: B.3 / GAP B-CLASSIFY.  In the four-local-triangle branch, the two
special bin-zero endpoints form an original edge and already share the rare
bin-three root.  C4-freeness therefore makes their seven-point external
bin-zero supports disjoint.  This couples the two pointwise missing-row laws
to a fourteen-point piece of the full B0--B1 design.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The external seven-point supports of the two special endpoints are
disjoint.  Any common support point would be a second common neighbor of the
special edge, in addition to the bin-three root. -/
theorem squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x y z : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hloc : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let Fy := (G.neighborFinset y ∩ B 0) \ S
    let Fz := (G.neighborFinset z ∩ B 0) \ S
    Disjoint Fy Fz := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let Fy := (G.neighborFinset y ∩ B 0) \ S
  let Fz := (G.neighborFinset z ∩ B 0) \ S
  have hyzAdj :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  have hle := common_le_one_of_not_containsC4 hfree y z hyz
  rw [Finset.disjoint_left]
  intro w hwY hwZ
  have hwYParts := Finset.mem_sdiff.mp hwY
  have hwZParts := Finset.mem_sdiff.mp hwZ
  have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset z :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwYParts.1).1,
      (Finset.mem_inter.mp hwZParts.1).1⟩
  have hyParts := Finset.mem_sdiff.mp hy
  have hzParts := Finset.mem_sdiff.mp hz
  have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset y x).mpr ((G.adj_comm x y).mp
        ((G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyParts.1).1)),
      (G.mem_neighborFinset z x).mpr ((G.adj_comm x z).mp
        ((G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hzParts.1).1))⟩
  have hwx : w = x := Finset.card_le_one.mp hle w hwCommon x hxCommon
  have hkw : squareOrderHighIncidenceCount G 9 w = 0 :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hwYParts.1).2).2
  have hkx : squareOrderHighIncidenceCount G 9 x = 3 :=
    (Finset.mem_filter.mp hx).2
  rw [hwx] at hkw
  omega

/-- The paired special supports occupy exactly fourteen external bin-zero
points. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_support_card_fourteen
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x y z : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hloc : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let Fy := (G.neighborFinset y ∩ B 0) \ S
    let Fz := (G.neighborFinset z ∩ B 0) \ S
    (Fy ∪ Fz).card = 14 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let Fy := (G.neighborFinset y ∩ B 0) \ S
  let Fz := (G.neighborFinset z ∩ B 0) \ S
  have hdisj :=
    squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  dsimp only at hdisj
  have hFy :=
    squareOrderNine_threeHigh_secondProfile_nondefect_special_support_card_seven
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  have hFz :=
    squareOrderNine_threeHigh_secondProfile_nondefect_special_support_card_seven
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hz
  dsimp only at hFy hFz
  rw [Finset.card_union_of_disjoint hdisj, hFy, hFz]

/-- Full paired-puncture package.  The two seven-point supports form a
fourteen-point set, and the defect rows at each special endpoint are exactly
the unmarked rows missing its corresponding support. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_puncture_design
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x y z : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hloc : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let Fy := (G.neighborFinset y ∩ B 0) \ S
    let Fz := (G.neighborFinset z ∩ B 0) \ S
    let D := secondOrderDefectGraph G
    (Fy ∪ Fz).card = 14 ∧
      (D.neighborFinset y ∩ U1 =
        U1.filter fun b => (G.neighborFinset b ∩ Fy).card = 0) ∧
      (D.neighborFinset z ∩ U1 =
        U1.filter fun b => (G.neighborFinset b ∩ Fz).card = 0) := by
  classical
  dsimp only
  constructor
  · exact squareOrderNine_threeHigh_secondProfile_paired_support_card_fourteen
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  constructor
  · exact
      squareOrderNine_threeHigh_secondProfile_nondefect_special_defect_eq_missing_rows
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  · exact
      squareOrderNine_threeHigh_secondProfile_nondefect_special_defect_eq_missing_rows
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hz

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_support_card_fourteen
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_puncture_design
