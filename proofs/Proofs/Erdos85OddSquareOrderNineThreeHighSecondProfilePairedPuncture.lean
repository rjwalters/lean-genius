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

/-- Pointwise binary design equation on the paired puncture.  Every unmarked
bin-one row hits each seven-point support once, except that the hit is
replaced by the corresponding special defect. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_puncture_row_equation
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
    {x y z b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hloc : (G.induce (G.neighborSet x)).edgeFinset.card = 4)
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let Fy := (G.neighborFinset y ∩ B 0) \ S
    let Fz := (G.neighborFinset z ∩ B 0) \ S
    let D := secondOrderDefectGraph G
    (G.neighborFinset b ∩ (Fy ∪ Fz)).card +
        (if D.Adj y b then 1 else 0) +
        (if D.Adj z b then 1 else 0) = 2 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let Fy := (G.neighborFinset y ∩ B 0) \ S
  let Fz := (G.neighborFinset z ∩ B 0) \ S
  let D := secondOrderDefectGraph G
  have hdesign :=
    squareOrderNine_threeHigh_secondProfile_paired_puncture_design
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  dsimp only at hdesign
  have hbU : b ∈ U1 := hb
  have endpointHit (e : V) (heB0 : e ∈ B 0) (F : Finset V)
      (hFsub : F ⊆ G.neighborFinset e)
      (hmissing : D.neighborFinset e ∩ U1 =
        U1.filter fun c => (G.neighborFinset c ∩ F).card = 0) :
      (G.neighborFinset b ∩ F).card +
        (if D.Adj e b then 1 else 0) = 1 := by
    have hbe : b ≠ e := by
      intro h
      subst e
      have hkb : squareOrderHighIncidenceCount G 9 b = 1 :=
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
      have hke : squareOrderHighIncidenceCount G 9 b = 0 :=
        (Finset.mem_filter.mp heB0).2
      omega
    have hle : (G.neighborFinset b ∩ F).card ≤ 1 := by
      apply (Finset.card_le_card ?_).trans
        (common_le_one_of_not_containsC4 hfree b e hbe)
      intro w hw
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
        hFsub (Finset.mem_inter.mp hw).2⟩
    have hzero_iff : (G.neighborFinset b ∩ F).card = 0 ↔ D.Adj e b := by
      have hmem := Finset.ext_iff.mp hmissing b
      simp only [Finset.mem_inter, hbU, true_and, Finset.mem_filter] at hmem
      rw [D.mem_neighborFinset] at hmem
      simpa using hmem.symm
    by_cases hD : D.Adj e b
    · rw [if_pos hD, (hzero_iff.mpr hD)]
    · rw [if_neg hD]
      have hpos : 0 < (G.neighborFinset b ∩ F).card :=
        Nat.pos_of_ne_zero fun hzero => hD (hzero_iff.mp hzero)
      omega
  have hyB0 : y ∈ B 0 :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2
  have hzB0 : z ∈ B 0 :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hz).1).2
  have hFySub : Fy ⊆ G.neighborFinset y := fun _ hw =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1).1
  have hFzSub : Fz ⊆ G.neighborFinset z := fun _ hw =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1).1
  have hyHit := endpointHit y hyB0 Fy hFySub hdesign.2.1
  have hzHit := endpointHit z hzB0 Fz hFzSub hdesign.2.2
  have hdisj :=
    squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  dsimp only at hdisj
  have hhitDisj : Disjoint (G.neighborFinset b ∩ Fy)
      (G.neighborFinset b ∩ Fz) :=
    hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint hhitDisj]
  simp only [D] at hyHit hzHit ⊢
  omega

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_support_card_fourteen
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_puncture_design
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_puncture_row_equation
