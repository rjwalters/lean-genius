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

/-- Each special endpoint has exactly three defect rows in the unmarked
bin-one core.  Its full bin-one defect degree is three, while a marked row
would share the bin-three root as an original common neighbor. -/
theorem squareOrderNine_threeHigh_secondProfile_special_unmarked_defect_card_three
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    (D.neighborFinset y ∩ U1).card = 3 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have hregular :=
    squareOrderNine_threeHigh_secondProfile_nondefect_binZero_is_regular
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  dsimp only at hregular
  have hmarkedZero : D.neighborFinset y ∩ M = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    have hbParts := Finset.mem_inter.mp hb
    have hbM := Finset.mem_inter.mp hbParts.2
    have hyParts := Finset.mem_sdiff.mp hy
    have hyx : G.Adj y x := (G.adj_comm x y).mp
      ((G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyParts.1).1)
    have hbx : G.Adj b x := (G.adj_comm x b).mp
      ((G.mem_neighborFinset x b).mp hbM.1)
    have hyb : y ≠ b := by
      intro h
      subst b
      have hky := (Finset.mem_filter.mp (Finset.mem_inter.mp hyParts.1).2).2
      have hkb := (Finset.mem_filter.mp hbM.2).2
      omega
    exact (not_secondOrderDefect_adj_of_commonNeighbor
      G hfree hyb hyx hbx) ((D.mem_neighborFinset y b).mp hbParts.1)
  have hsplit : D.neighborFinset y ∩ B 1 =
      (D.neighborFinset y ∩ M) ∪ (D.neighborFinset y ∩ U1) := by
    ext b
    simp only [M, U1, Finset.mem_inter, Finset.mem_union,
      Finset.mem_sdiff]
    tauto
  rw [hmarkedZero, Finset.empty_union] at hsplit
  rw [← hsplit, hregular.2.1]

/-- Joint census of the two three-row defect punctures.  All four row
classes are determined by the overlap `I` of the two defect sets. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_defect_census
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
      (secondOrderDefectGraph G).neighborFinset x) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let Ey := D.neighborFinset y ∩ U1
    let Ez := D.neighborFinset z ∩ U1
    let I := Ey ∩ Ez
    Ey.card = 3 ∧ Ez.card = 3 ∧ I.card ≤ 3 ∧
      (Ey \ Ez).card = 3 - I.card ∧
      (Ez \ Ey).card = 3 - I.card ∧
      (U1 \ (Ey ∪ Ez)).card = 18 + I.card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let Ey := D.neighborFinset y ∩ U1
  let Ez := D.neighborFinset z ∩ U1
  let I := Ey ∩ Ez
  have hEy : Ey.card = 3 :=
    squareOrderNine_threeHigh_secondProfile_special_unmarked_defect_card_three
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  have hEz : Ez.card = 3 :=
    squareOrderNine_threeHigh_secondProfile_special_unmarked_defect_card_three
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hz
  have hIle : I.card ≤ 3 := by
    calc I.card ≤ Ey.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hEy
  have hEyDiff : (Ey \ Ez).card = 3 - I.card := by
    change (Ey \ Ez).card = 3 - (Ey ∩ Ez).card
    rw [Finset.card_sdiff, hEy]
    congr 2
    rw [Finset.inter_comm]
  have hEzDiff : (Ez \ Ey).card = 3 - I.card := by
    change (Ez \ Ey).card = 3 - (Ey ∩ Ez).card
    rw [Finset.card_sdiff, hEz]
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hmarked.2]
  have hEySub : Ey ⊆ U1 := Finset.inter_subset_right
  have hEzSub : Ez ⊆ U1 := Finset.inter_subset_right
  have hUnionSub : Ey ∪ Ez ⊆ U1 := Finset.union_subset hEySub hEzSub
  have hUnionCard : (Ey ∪ Ez).card = 6 - I.card := by
    change (Ey ∪ Ez).card = 6 - (Ey ∩ Ez).card
    rw [Finset.card_union, hEy, hEz]
  have hNeither : (U1 \ (Ey ∪ Ez)).card = 18 + I.card := by
    rw [Finset.card_sdiff_of_subset hUnionSub, hU1card, hUnionCard]
    omega
  exact ⟨hEy, hEz, hIle, hEyDiff, hEzDiff, hNeither⟩

/-- A special seven-point support resolves the 21 nondefect unmarked rows
into seven disjoint triples. -/
theorem squareOrderNine_threeHigh_secondProfile_special_puncture_resolution
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := (G.neighborFinset y ∩ B 0) \ S
    let E := (secondOrderDefectGraph G).neighborFinset y ∩ U1
    let block := fun w => G.neighborFinset w ∩ U1
    (∀ w ∈ F, (block w).card = 3) ∧
      (∀ w ∈ F, ∀ v ∈ F, w ≠ v → Disjoint (block w) (block v)) ∧
      F.biUnion block = U1 \ E := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let F := (G.neighborFinset y ∩ B 0) \ S
  let D := secondOrderDefectGraph G
  let E := D.neighborFinset y ∩ U1
  let block := fun w => G.neighborFinset w ∩ U1
  have hyParts := Finset.mem_sdiff.mp hy
  have hyS : y ∈ S := hyParts.1
  have hyB0 : y ∈ B 0 := (Finset.mem_inter.mp hyParts.1).2
  have hxB3 : squareOrderHighIncidenceCount G 9 x = 3 :=
    (Finset.mem_filter.mp hx).2
  have hFoff : F ⊆ T \ P := by
    intro w hwF
    have hwParts := Finset.mem_sdiff.mp hwF
    have hwB0 := (Finset.mem_inter.mp hwParts.1).2
    have hwT : w ∈ T := Finset.mem_sdiff.mpr ⟨hwB0, hwParts.2⟩
    refine Finset.mem_sdiff.mpr ⟨hwT, ?_⟩
    intro hwP
    simp only [P, Finset.mem_biUnion] at hwP
    obtain ⟨m, hmM, hwm⟩ := hwP
    have hmParts := Finset.mem_inter.mp hmM
    have hwmParts := Finset.mem_inter.mp hwm
    have hym : y ≠ m := by
      intro h
      subst m
      have hky := (Finset.mem_filter.mp hyB0).2
      have hkm := (Finset.mem_filter.mp hmParts.2).2
      omega
    have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset m :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y x).mpr ((G.adj_comm x y).mp
          ((G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyS).1)),
        (G.mem_neighborFinset m x).mpr ((G.adj_comm x m).mp
          ((G.mem_neighborFinset x m).mp hmParts.1))⟩
    have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset m :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwParts.1).1,
        hwmParts.1⟩
    have hwx : w ≠ x := by
      intro h
      subst w
      have hkw := (Finset.mem_filter.mp hwB0).2
      omega
    have hle := common_le_one_of_not_containsC4 hfree y m hym
    exact hwx (Finset.card_le_one.mp hle w hwCommon x hxCommon)
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hblocks : ∀ w ∈ F, (block w).card = 3 := by
    intro w hw
    exact hcensus.2.2.2.1 w (hFoff hw)
  have hyNotU1 : y ∉ U1 := by
    intro hyU
    have hky0 := (Finset.mem_filter.mp hyB0).2
    have hky1 := (Finset.mem_filter.mp
      (Finset.mem_sdiff.mp hyU).1).2
    omega
  have hgeneric := c4Free_neighbor_blocks_partition_common_targets
    G hfree y U1 hyNotU1
  dsimp only at hgeneric
  have hdisj : ∀ w ∈ F, ∀ v ∈ F, w ≠ v →
      Disjoint (block w) (block v) := by
    intro w hw v hv hwv
    apply hgeneric.1 w (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1).1
      v (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1 hwv
  have hcoverEq : F.biUnion block = U1 \ E := by
    ext b
    constructor
    · intro hb
      simp only [F, block, Finset.mem_biUnion] at hb
      obtain ⟨w, hwF, hbBlock⟩ := hb
      have hbParts := Finset.mem_inter.mp hbBlock
      refine Finset.mem_sdiff.mpr ⟨hbParts.2, ?_⟩
      intro hbE
      have hbD := (Finset.mem_inter.mp hbE).1
      have hyb : y ≠ b := by
        intro h
        subst b
        exact hyNotU1 hbParts.2
      have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hyb).mp ((D.mem_neighborFinset y b).mp hbD)
      have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset b :=
        Finset.mem_inter.mpr ⟨
          (Finset.mem_inter.mp (Finset.mem_sdiff.mp hwF).1).1,
          (G.mem_neighborFinset b w).mpr ((G.adj_comm w b).mp
            ((G.mem_neighborFinset w b).mp hbParts.1))⟩
      have hpos : 0 < (G.neighborFinset y ∩ G.neighborFinset b).card :=
        Finset.card_pos.mpr ⟨w, hwCommon⟩
      omega
    · intro hb
      have hbParts := Finset.mem_sdiff.mp hb
      have hyb : y ≠ b := by
        intro h
        subst b
        exact hyNotU1 hbParts.1
      have hnotD : b ∉ D.neighborFinset y := fun hbD =>
        hbParts.2 (Finset.mem_inter.mpr ⟨hbD, hbParts.1⟩)
      have hpos : 0 < (G.neighborFinset b ∩ F).card := by
        by_contra hnotPos
        have hzero : (G.neighborFinset b ∩ F).card = 0 := by omega
        have hmissing :=
          squareOrderNine_threeHigh_secondProfile_nondefect_special_defect_eq_missing_rows
            G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
        dsimp only at hmissing
        have hmem := Finset.ext_iff.mp hmissing b
        exact hnotD (Finset.mem_inter.mp (hmem.mpr
          (Finset.mem_filter.mpr ⟨hbParts.1, hzero⟩))).1
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have hwParts := Finset.mem_inter.mp hw
      simp only [F, block, Finset.mem_biUnion]
      exact ⟨w, hwParts.2, Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w b).mpr ((G.adj_comm b w).mp
          ((G.mem_neighborFinset b w).mp hwParts.1)), hbParts.1⟩⟩
  exact ⟨hblocks, hdisj, hcoverEq⟩

/-- The two special resolutions are cross-orthogonal: one triple from each
resolution meets in at most one unmarked row. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_resolutions_cross_le_one
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
    let block := fun w => G.neighborFinset w ∩ U1
    ∀ wy ∈ Fy, ∀ wz ∈ Fz, ((block wy) ∩ (block wz)).card ≤ 1 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let Fy := (G.neighborFinset y ∩ B 0) \ S
  let Fz := (G.neighborFinset z ∩ B 0) \ S
  let block := fun w => G.neighborFinset w ∩ U1
  have hdisj :=
    squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  dsimp only at hdisj
  intro wy hwy wz hwz
  have hwyz : wy ≠ wz := by
    intro h
    subst wz
    exact (Finset.disjoint_left.mp hdisj) hwy hwz
  apply (Finset.card_le_card ?_).trans
    (common_le_one_of_not_containsC4 hfree wy wz hwyz)
  intro b hb
  have hbParts := Finset.mem_inter.mp hb
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbParts.1).1,
    (Finset.mem_inter.mp hbParts.2).1⟩

/-- The two external seven-point supports are anticomplete in the original
graph.  A cross edge would close a four-cycle through the special edge. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_supports_anticomplete
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
    ∀ wy ∈ Fy, ∀ wz ∈ Fz, ¬ G.Adj wy wz := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let Fy := (G.neighborFinset y ∩ B 0) \ S
  let Fz := (G.neighborFinset z ∩ B 0) \ S
  have hyzAdj :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  have hyS : y ∈ S := (Finset.mem_sdiff.mp hy).1
  have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
  intro wy hwy wz hwz hcross
  have hwyParts := Finset.mem_sdiff.mp hwy
  have hwzParts := Finset.mem_sdiff.mp hwz
  have hywz : y ≠ wz := fun h =>
    hwzParts.2 (h ▸ hyS)
  have hwyz : wy ≠ z := fun h =>
    hwyParts.2 (h ▸ hzS)
  have hwyCommon : wy ∈ G.neighborFinset y ∩ G.neighborFinset wz :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwyParts.1).1,
      (G.mem_neighborFinset wz wy).mpr ((G.adj_comm wy wz).mp hcross)⟩
  have hzCommon : z ∈ G.neighborFinset y ∩ G.neighborFinset wz :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y z).mpr hyzAdj,
      (G.mem_neighborFinset wz z).mpr ((G.adj_comm z wz).mp
        ((G.mem_neighborFinset z wz).mp
          (Finset.mem_inter.mp hwzParts.1).1))⟩
  have hle := common_le_one_of_not_containsC4 hfree y wz hywz
  exact hwyz (Finset.card_le_one.mp hle wy hwyCommon z hzCommon)

/-- Every triple in a special puncture resolution is rainbow: it contains
exactly one unmarked bin-one row from each high-root fiber. -/
theorem squareOrderNine_threeHigh_secondProfile_special_puncture_blocks_rainbow
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := (G.neighborFinset y ∩ B 0) \ S
    let block := fun w => G.neighborFinset w ∩ U1
    let color := fun a => G.neighborFinset a ∩ U1
    ∀ w ∈ F, ∀ a ∈ H, ((block w) ∩ (color a)).card = 1 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  let block := fun w => G.neighborFinset w ∩ U1
  let color := fun a => G.neighborFinset a ∩ U1
  have hresolution :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_resolution
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  dsimp only at hresolution
  have hcolors :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcolors
  intro w hwF a ha
  have hwLow : w ∉ H := by
    intro hwH
    have hwB0 := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hwF).1).2
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwB0).1).2 hwH
  have hle : ∀ r ∈ H, ((block w) ∩ (color r)).card ≤ 1 := by
    intro r hr
    rw [Finset.card_le_one]
    intro u hu v hv
    have huParts := Finset.mem_inter.mp hu
    have hvParts := Finset.mem_inter.mp hv
    have huBlock := Finset.mem_inter.mp huParts.1
    have hvBlock := Finset.mem_inter.mp hvParts.1
    have huColor := Finset.mem_inter.mp huParts.2
    have hvColor := Finset.mem_inter.mp hvParts.2
    by_contra huv
    exact (squareOrderNine_threeHigh_secondProfile_same_high_fiber_separation
      G hfree huv hr
        ((G.mem_neighborFinset r u).mp huColor.1)
        ((G.mem_neighborFinset r v).mp hvColor.1)
        hwLow).1 ⟨
          (G.mem_neighborFinset w u).mp huBlock.1,
          (G.mem_neighborFinset w v).mp hvBlock.1⟩
  have hpair : ∀ r ∈ H, ∀ s ∈ H, r ≠ s →
      Disjoint ((block w) ∩ (color r)) ((block w) ∩ (color s)) := by
    intro r hr s hs hrs
    exact (hcolors.2.2.1 r hr s hs hrs).mono
      (fun _ h => (Finset.mem_inter.mp h).2)
      (fun _ h => (Finset.mem_inter.mp h).2)
  have hunion : H.biUnion (fun r => (block w) ∩ (color r)) = block w := by
    ext u
    constructor
    · intro hu
      simp only [Finset.mem_biUnion] at hu
      obtain ⟨r, _hr, huParts⟩ := hu
      exact (Finset.mem_inter.mp huParts).1
    · intro hu
      have huU := (Finset.mem_inter.mp hu).2
      have huColors : u ∈ H.biUnion color := by
        rw [hcolors.2.2.2]
        exact huU
      simp only [Finset.mem_biUnion] at huColors ⊢
      obtain ⟨r, hr, huColor⟩ := huColors
      exact ⟨r, hr, Finset.mem_inter.mpr ⟨hu, huColor⟩⟩
  have hsum : (∑ r ∈ H, ((block w) ∩ (color r)).card) = 3 := by
    rw [← Finset.card_biUnion hpair, hunion,
      hresolution.1 w hwF]
  have hrest : (∑ r ∈ H.erase a,
      ((block w) ∩ (color r)).card) ≤ 2 := by
    have hbound := Finset.sum_le_card_nsmul (H.erase a)
      (fun r => ((block w) ∩ (color r)).card) 1 (by
        intro r hr
        exact hle r (Finset.mem_of_mem_erase hr))
    rw [Finset.card_erase_of_mem ha, hcolors.1] at hbound
    norm_num at hbound
    exact hbound
  have hdecomp := Finset.sum_erase_add H
    (fun r => ((block w) ∩ (color r)).card) ha
  change (∑ r ∈ H.erase a, ((block w) ∩ (color r)).card) +
      ((block w) ∩ (color a)).card =
        ∑ r ∈ H, ((block w) ∩ (color r)).card at hdecomp
  rw [hsum] at hdecomp
  have haLe := hle a ha
  change ((block w) ∩ (color a)).card = 1
  omega

/-- The three-row hole of a special puncture is also rainbow: exactly one
missing row lies in each high-root fiber. -/
theorem squareOrderNine_threeHigh_secondProfile_special_puncture_hole_rainbow
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let E := (secondOrderDefectGraph G).neighborFinset y ∩ U1
    let color := fun a => G.neighborFinset a ∩ U1
    ∀ a ∈ H, (E ∩ color a).card = 1 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  let E := (secondOrderDefectGraph G).neighborFinset y ∩ U1
  let block := fun w => G.neighborFinset w ∩ U1
  let color := fun a => G.neighborFinset a ∩ U1
  have hresolution :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_resolution
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  dsimp only at hresolution
  have hrainbow :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_blocks_rainbow
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  dsimp only at hrainbow
  have hcolors :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcolors
  have hFcard :=
    squareOrderNine_threeHigh_secondProfile_nondefect_special_support_card_seven
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  change F.card = 7 at hFcard
  intro a ha
  let covered := (U1 \ E) ∩ color a
  have hcoveredEq : covered =
      F.biUnion fun w => (block w) ∩ color a := by
    ext b
    constructor
    · intro hb
      have hbParts := Finset.mem_inter.mp hb
      have hbUnion : b ∈ F.biUnion block := by
        rw [hresolution.2.2]
        exact hbParts.1
      simp only [Finset.mem_biUnion] at hbUnion ⊢
      obtain ⟨w, hwF, hbBlock⟩ := hbUnion
      exact ⟨w, hwF, Finset.mem_inter.mpr ⟨hbBlock, hbParts.2⟩⟩
    · intro hb
      simp only [Finset.mem_biUnion] at hb
      obtain ⟨w, hwF, hbParts⟩ := hb
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hbParts).2⟩
      rw [← hresolution.2.2]
      simp only [Finset.mem_biUnion]
      exact ⟨w, hwF, (Finset.mem_inter.mp hbParts).1⟩
  have hcoveredPair : ∀ w ∈ F, ∀ v ∈ F, w ≠ v →
      Disjoint ((block w) ∩ color a) ((block v) ∩ color a) := by
    intro w hw v hv hwv
    exact (hresolution.2.1 w hw v hv hwv).mono
      (fun _ h => (Finset.mem_inter.mp h).1)
      (fun _ h => (Finset.mem_inter.mp h).1)
  have hcoveredCard : covered.card = 7 := by
    rw [hcoveredEq, Finset.card_biUnion hcoveredPair]
    calc
      (∑ w ∈ F, ((block w) ∩ color a).card) = ∑ _w ∈ F, 1 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hrainbow w hw a ha
      _ = 7 := by simp [hFcard]
  have hcolorCard : (color a).card = 8 := hcolors.2.1 a ha
  have hcolorSplit : color a = covered ∪ (E ∩ color a) := by
    ext b
    simp only [covered, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    constructor
    · intro hbColor
      by_cases hbE : b ∈ E
      · exact Or.inr ⟨hbE, hbColor⟩
      · exact Or.inl ⟨⟨(Finset.mem_inter.mp hbColor).2, hbE⟩, hbColor⟩
    · rintro (hb | hb) <;> exact hb.2
  have hsplitDisj : Disjoint covered (E ∩ color a) := by
    rw [Finset.disjoint_left]
    intro b hbCovered hbE
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hbCovered).1).2
      (Finset.mem_inter.mp hbE).1
  have hcards := congrArg Finset.card hcolorSplit
  rw [Finset.card_union_of_disjoint hsplitDisj,
    hcolorCard, hcoveredCard] at hcards
  change 8 = 7 + (E ∩ color a).card at hcards
  change (E ∩ color a).card = 1
  omega

/-- The overlap of the two special holes is exactly their three-color
agreement count.  In each color the overlap contributes either zero or one. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_hole_color_agreement
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
      (secondOrderDefectGraph G).neighborFinset x) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let Ey := D.neighborFinset y ∩ U1
    let Ez := D.neighborFinset z ∩ U1
    let I := Ey ∩ Ez
    let color := fun a => G.neighborFinset a ∩ U1
    (∀ a ∈ H,
      (Ey ∩ color a).card = 1 ∧
      (Ez ∩ color a).card = 1 ∧
      (I ∩ color a).card ≤ 1) ∧
      (∑ a ∈ H, (I ∩ color a).card) = I.card := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let Ey := D.neighborFinset y ∩ U1
  let Ez := D.neighborFinset z ∩ U1
  let I := Ey ∩ Ez
  let color := fun a => G.neighborFinset a ∩ U1
  have hyRainbow :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_hole_rainbow
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  have hzRainbow :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_hole_rainbow
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hz
  dsimp only at hyRainbow hzRainbow
  have hcolors :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcolors
  have hpoint : ∀ a ∈ H,
      (Ey ∩ color a).card = 1 ∧
      (Ez ∩ color a).card = 1 ∧
      (I ∩ color a).card ≤ 1 := by
    intro a ha
    refine ⟨hyRainbow a ha, hzRainbow a ha, ?_⟩
    calc
      (I ∩ color a).card ≤ (Ey ∩ color a).card := by
        apply Finset.card_le_card
        intro b hb
        have hbParts := Finset.mem_inter.mp hb
        exact Finset.mem_inter.mpr ⟨
          (Finset.mem_inter.mp hbParts.1).1, hbParts.2⟩
      _ = 1 := hyRainbow a ha
  have hpair : ∀ a ∈ H, ∀ b ∈ H, a ≠ b →
      Disjoint (I ∩ color a) (I ∩ color b) := by
    intro a ha b hb hab
    exact (hcolors.2.2.1 a ha b hb hab).mono
      (fun _ h => (Finset.mem_inter.mp h).2)
      (fun _ h => (Finset.mem_inter.mp h).2)
  have hISub : I ⊆ U1 := fun _ hb =>
    (Finset.mem_inter.mp (Finset.mem_inter.mp hb).1).2
  have hunion : H.biUnion (fun a => I ∩ color a) = I := by
    ext v
    constructor
    · intro hv
      simp only [Finset.mem_biUnion] at hv
      obtain ⟨a, _ha, hvParts⟩ := hv
      exact (Finset.mem_inter.mp hvParts).1
    · intro hvI
      have hvU : v ∈ U1 := hISub hvI
      have hvColors : v ∈ H.biUnion color := by
        rw [hcolors.2.2.2]
        exact hvU
      simp only [Finset.mem_biUnion] at hvColors ⊢
      obtain ⟨a, ha, hvColor⟩ := hvColors
      exact ⟨a, ha, Finset.mem_inter.mpr ⟨hvI, hvColor⟩⟩
  refine ⟨hpoint, ?_⟩
  rw [← Finset.card_biUnion hpair, hunion]

/-- In each high color, the two resolutions share six rows, plus one exactly
when their missing-row selectors agree in that color. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_color_shared_rows
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
      (secondOrderDefectGraph G).neighborFinset x) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let Ey := D.neighborFinset y ∩ U1
    let Ez := D.neighborFinset z ∩ U1
    let I := Ey ∩ Ez
    let color := fun a => G.neighborFinset a ∩ U1
    ∀ a ∈ H,
      ((color a) \ (Ey ∪ Ez)).card = 6 + (I ∩ color a).card := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let Ey := D.neighborFinset y ∩ U1
  let Ez := D.neighborFinset z ∩ U1
  let I := Ey ∩ Ez
  let color := fun a => G.neighborFinset a ∩ U1
  have hagree :=
    squareOrderNine_threeHigh_secondProfile_paired_hole_color_agreement
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz
  dsimp only at hagree
  have hcolors :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcolors
  intro a ha
  let C := color a
  let A := Ey ∩ C
  let Z := Ez ∩ C
  let J := I ∩ C
  have hpoint := hagree.1 a ha
  have hA : A.card = 1 := hpoint.1
  have hZ : Z.card = 1 := hpoint.2.1
  have hC : C.card = 8 := hcolors.2.1 a ha
  have hAZinter : A ∩ Z = J := by
    ext b
    simp only [A, Z, J, I, Finset.mem_inter]
    tauto
  have hCU : C ∩ (Ey ∪ Ez) = A ∪ Z := by
    ext b
    simp only [A, Z, Finset.mem_inter, Finset.mem_union]
    tauto
  have hUnionCard : (A ∪ Z).card = 2 - J.card := by
    rw [Finset.card_union, hA, hZ, hAZinter]
  have hRemoved : ((Ey ∪ Ez) ∩ C).card = 2 - J.card := by
    rw [Finset.inter_comm, hCU, hUnionCard]
  change (C \ (Ey ∪ Ez)).card = 6 + J.card
  rw [Finset.card_sdiff, hC, hRemoved]
  have hJle : J.card ≤ 1 := hpoint.2.2
  omega

/-- Formal partial-matching interface between the two resolutions.  Every
row resolved on both sides has a unique serving block pair, and each block
pair serves at most one row. -/
theorem squareOrderNine_threeHigh_secondProfile_paired_resolution_matching
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
    let D := secondOrderDefectGraph G
    let Fy := (G.neighborFinset y ∩ B 0) \ S
    let Fz := (G.neighborFinset z ∩ B 0) \ S
    let Ey := D.neighborFinset y ∩ U1
    let Ez := D.neighborFinset z ∩ U1
    let block := fun w => G.neighborFinset w ∩ U1
    (∀ b ∈ U1 \ (Ey ∪ Ez), ∃! p : V × V,
      p.1 ∈ Fy ∧ p.2 ∈ Fz ∧ b ∈ block p.1 ∧ b ∈ block p.2) ∧
      (∀ wy ∈ Fy, ∀ wz ∈ Fz, ∀ b ∈ block wy ∩ block wz,
        ∀ c ∈ block wy ∩ block wz, b = c) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let Fy := (G.neighborFinset y ∩ B 0) \ S
  let Fz := (G.neighborFinset z ∩ B 0) \ S
  let Ey := D.neighborFinset y ∩ U1
  let Ez := D.neighborFinset z ∩ U1
  let block := fun w => G.neighborFinset w ∩ U1
  have hyRes :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_resolution
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  have hzRes :=
    squareOrderNine_threeHigh_secondProfile_special_puncture_resolution
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hz
  dsimp only at hyRes hzRes
  have hcross :=
    squareOrderNine_threeHigh_secondProfile_paired_resolutions_cross_le_one
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hloc
  dsimp only at hcross
  constructor
  · intro b hb
    have hbParts := Finset.mem_sdiff.mp hb
    have hbY : b ∈ U1 \ Ey := Finset.mem_sdiff.mpr ⟨hbParts.1, fun h =>
      hbParts.2 (Finset.mem_union_left _ h)⟩
    have hbZ : b ∈ U1 \ Ez := Finset.mem_sdiff.mpr ⟨hbParts.1, fun h =>
      hbParts.2 (Finset.mem_union_right _ h)⟩
    have hbYUnion : b ∈ Fy.biUnion block := by
      rw [hyRes.2.2]
      exact hbY
    have hbZUnion : b ∈ Fz.biUnion block := by
      rw [hzRes.2.2]
      exact hbZ
    simp only [Finset.mem_biUnion] at hbYUnion hbZUnion
    obtain ⟨wy, hwy, hbwy⟩ := hbYUnion
    obtain ⟨wz, hwz, hbwz⟩ := hbZUnion
    refine ⟨(wy, wz), ⟨hwy, hwz, hbwy, hbwz⟩, ?_⟩
    intro p hp'
    have hpParts := hp'
    have hfirst : p.1 = wy := by
      by_contra hne
      have hdisj := hyRes.2.1 p.1 hpParts.1 wy hwy hne
      exact (Finset.disjoint_left.mp hdisj) hpParts.2.2.1 hbwy
    have hsecond : p.2 = wz := by
      by_contra hne
      have hdisj := hzRes.2.1 p.2 hpParts.2.1 wz hwz hne
      exact (Finset.disjoint_left.mp hdisj) hpParts.2.2.2 hbwz
    exact Prod.ext hfirst hsecond
  · intro wy hwy wz hwz b hb c hc
    exact Finset.card_le_one.mp (hcross wy hwy wz hwz)
      b hb c hc

/-- A common missing row has a five-point B0 support simultaneously
disjoint from both eight-point special rows. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_union
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
    {x y z b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let Ry := G.neighborFinset y ∩ B 0
    let Rz := G.neighborFinset z ∩ B 0
    let Q := G.neighborFinset b ∩ B 0
    Ry.card = 8 ∧ Rz.card = 8 ∧ Q.card = 5 ∧
      Disjoint Ry Rz ∧ Disjoint Ry Q ∧ Disjoint Rz Q ∧
      ((Ry ∪ Rz) ∪ Q).card = 21 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let Ry := G.neighborFinset y ∩ B 0
  let Rz := G.neighborFinset z ∩ B 0
  let Q := G.neighborFinset b ∩ B 0
  let D := secondOrderDefectGraph G
  have hyBase := (Finset.mem_sdiff.mp hy).1
  have hzBase := (Finset.mem_sdiff.mp hz).1
  have hbParts := Finset.mem_inter.mp hb
  have hbY := Finset.mem_inter.mp hbParts.1
  have hbZ := Finset.mem_inter.mp hbParts.2
  have hbB1 : b ∈ B 1 := (Finset.mem_sdiff.mp hbY.2).1
  have hyB0 : y ∈ B 0 := (Finset.mem_inter.mp hyBase).2
  have hzB0 : z ∈ B 0 := (Finset.mem_inter.mp hzBase).2
  have hxy : G.Adj x y :=
    (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyBase).1
  have hxz : G.Adj x z :=
    (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hzBase).1
  have hyAnti : b ∈ antipodalNeighbors G y ∩ B 1 := by
    have hanti :=
      squareOrderNine_threeHigh_binThree_binZero_neighbor_binOne_defect_antipodal
        G hfree hhigh hx hyB0 hbB1 hxy
          ((D.mem_neighborFinset y b).mp hbY.1)
    exact Finset.mem_inter.mpr ⟨
      (antipodalGraph_adj G y b).mp hanti, hbB1⟩
  have hzAnti : b ∈ antipodalNeighbors G z ∩ B 1 := by
    have hanti :=
      squareOrderNine_threeHigh_binThree_binZero_neighbor_binOne_defect_antipodal
        G hfree hhigh hx hzB0 hbB1 hxz
          ((D.mem_neighborFinset z b).mp hbZ.1)
    exact Finset.mem_inter.mpr ⟨
      (antipodalGraph_adj G z b).mp hanti, hbB1⟩
  have hyFiber :=
    squareOrderNine_threeHigh_secondProfile_special_antipodal_binOne_fiber
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyBase hyAnti
  have hzFiber :=
    squareOrderNine_threeHigh_secondProfile_special_antipodal_binOne_fiber
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hzBase hzAnti
  dsimp only at hyFiber hzFiber
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpack
  have hRy : Ry.card = 8 := hpack.1 y hyBase
  have hRz : Rz.card = 8 := hpack.1 z hzBase
  have hQ : Q.card = 5 := hyFiber.2.1
  have hYZ : Disjoint Ry Rz := hpack.2.1 y hyBase z hzBase hyz
  have hYQ : Disjoint Ry Q := hyFiber.2.2.2
  have hZQ : Disjoint Rz Q := hzFiber.2.2.2
  have hUnionQ : Disjoint (Ry ∪ Rz) Q := by
    rw [Finset.disjoint_left]
    intro v hvUnion hvQ
    rcases Finset.mem_union.mp hvUnion with hvY | hvZ
    · exact (Finset.disjoint_left.mp hYQ) hvY hvQ
    · exact (Finset.disjoint_left.mp hZQ) hvZ hvQ
  have hUnionCard : ((Ry ∪ Rz) ∪ Q).card = 21 := by
    rw [Finset.card_union_of_disjoint hUnionQ,
      Finset.card_union_of_disjoint hYZ, hRy, hRz, hQ]
  exact ⟨hRy, hRz, hQ, hYZ, hYQ, hZQ, hUnionCard⟩

/-- A row missing from both special punctures has two or three special
defects.  Consequently its mixed column has one of two exact profiles:
three or two ordinary defect rows, fifteen core rows, and respectively
twenty-nine or thirty residual rows. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_mixed_column_dichotomy
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
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let A := fun t => (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
    let C := fun t => (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
    let defectRows := T.filter fun t => D.Adj t b
    let residualRows := T.filter fun t => (A t).Nonempty
    let coreRows := T.filter fun t => (C t).Nonempty
    let specialDefects := (D.neighborFinset b ∩ S).card
    coreRows.card = 15 ∧
      ((specialDefects = 2 ∧ defectRows.card = 3 ∧ residualRows.card = 29) ∨
       (specialDefects = 3 ∧ defectRows.card = 2 ∧ residualRows.card = 30)) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let A := fun t => (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let C := fun t => (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
  let defectRows := T.filter fun t => D.Adj t b
  let residualRows := T.filter fun t => (A t).Nonempty
  let coreRows := T.filter fun t => (C t).Nonempty
  let specialDefects := (D.neighborFinset b ∩ S).card
  have hbParts := Finset.mem_inter.mp hb
  have hbY := Finset.mem_inter.mp hbParts.1
  have hbZ := Finset.mem_inter.mp hbParts.2
  have hbU1 : b ∈ B 1 \ (G.neighborFinset x ∩ B 1) := hbY.2
  have hyS : y ∈ S := (Finset.mem_sdiff.mp hy).1
  have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
  have hyDb : y ∈ D.neighborFinset b := by
    apply (D.mem_neighborFinset b y).mpr
    exact ((D.mem_neighborFinset y b).mp hbY.1).symm
  have hzDb : z ∈ D.neighborFinset b := by
    apply (D.mem_neighborFinset b z).mpr
    exact ((D.mem_neighborFinset z b).mp hbZ.1).symm
  have hySpecial : y ∈ D.neighborFinset b ∩ S :=
    Finset.mem_inter.mpr ⟨hyDb, hyS⟩
  have hzSpecial : z ∈ D.neighborFinset b ∩ S :=
    Finset.mem_inter.mpr ⟨hzDb, hzS⟩
  have htwo : 2 ≤ specialDefects := by
    have hsub : ({y, z} : Finset V) ⊆ D.neighborFinset b ∩ S := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hySpecial
      · exact hzSpecial
    have hcardSub := Finset.card_le_card hsub
    rw [Finset.card_pair hyz] at hcardSub
    exact hcardSub
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hScard : S.card = 3 := by
    simpa [S, B] using hcensus.2.2
  have hthree : specialDefects ≤ 3 := by
    have hsub : D.neighborFinset b ∩ S ⊆ S := Finset.inter_subset_right
    have := Finset.card_le_card hsub
    omega
  have hmixed :=
    squareOrderNine_threeHigh_secondProfile_unmarked_mixed_column_counts
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hbU1
  dsimp only at hmixed
  rcases hmixed with ⟨hdefect, hcore, hresidual⟩
  change defectRows.card + specialDefects = 5 at hdefect
  change coreRows.card = 15 at hcore
  change residualRows.card = 27 + specialDefects at hresidual
  refine ⟨hcore, ?_⟩
  have hs : specialDefects = 2 ∨ specialDefects = 3 := by omega
  rcases hs with hs | hs
  · have hs' : (D.neighborFinset b ∩ S).card = 2 := by
      simpa [specialDefects] using hs
    have hd : defectRows.card = 3 := by omega
    have hr : residualRows.card = 29 := by omega
    exact Or.inl ⟨hs, hd, hr⟩
  · have hs' : (D.neighborFinset b ∩ S).card = 3 := by
      simpa [specialDefects] using hs
    have hd : defectRows.card = 2 := by omega
    have hr : residualRows.card = 30 := by omega
    exact Or.inr ⟨hs, hd, hr⟩

/-- A common missing row is defect-adjacent to exactly the two nondefect
special endpoints.  The third special row lies in the defect fiber of the
bin-three root and its forced exceptional profile has no bin-one defect
neighbors. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_specialDefects_eq_two
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
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let D := secondOrderDefectGraph G
    (D.neighborFinset b ∩ S).card = 2 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let D := secondOrderDefectGraph G
  let R := S \ D.neighborFinset x
  let H := D.neighborFinset b ∩ S
  have hbParts := Finset.mem_inter.mp hb
  have hbY := Finset.mem_inter.mp hbParts.1
  have hbZ := Finset.mem_inter.mp hbParts.2
  have hbB1 : b ∈ B 1 := (Finset.mem_sdiff.mp hbY.2).1
  have hyR : y ∈ R := hy
  have hzR : z ∈ R := hz
  have hbranch :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  change ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ R.card = 0) ∨
    ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ R.card = 2) at hbranch
  have hRcard : R.card = 2 := by
    rcases hbranch with h3 | h4
    · have : 0 < R.card := Finset.card_pos.mpr ⟨y, hyR⟩
      omega
    · exact h4.2
  have hHsubR : H ⊆ R := by
    intro w hwH
    have hwParts := Finset.mem_inter.mp hwH
    have hwS := hwParts.2
    apply Finset.mem_sdiff.mpr
    refine ⟨hwS, ?_⟩
    intro hwDx
    have hwSParts := Finset.mem_inter.mp hwS
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hwSParts.2
    dsimp only at htype
    have hDwx : D.Adj w x := ((D.mem_neighborFinset x w).mp hwDx).symm
    rcases htype with hreg | hexc
    · have hxInter : x ∈ D.neighborFinset w ∩ B 3 :=
        Finset.mem_inter.mpr ⟨(D.mem_neighborFinset w x).mpr hDwx, hx⟩
      have hpos : 0 < (D.neighborFinset w ∩ B 3).card :=
        Finset.card_pos.mpr ⟨x, hxInter⟩
      rw [hreg.2.2] at hpos
      omega
    · have hwb : D.Adj w b := by
        exact (D.adj_comm b w).mp ((D.mem_neighborFinset b w).mp hwParts.1)
      have hbInter : b ∈ D.neighborFinset w ∩ B 1 :=
        Finset.mem_inter.mpr ⟨(D.mem_neighborFinset w b).mpr hwb, hbB1⟩
      have hpos : 0 < (D.neighborFinset w ∩ B 1).card :=
        Finset.card_pos.mpr ⟨b, hbInter⟩
      rw [hexc.2.1] at hpos
      omega
  have hHle : H.card ≤ 2 := by
    calc H.card ≤ R.card := Finset.card_le_card hHsubR
      _ = 2 := hRcard
  have hyH : y ∈ H := by
    refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_sdiff.mp hy).1⟩
    exact (D.mem_neighborFinset b y).mpr
      (((D.mem_neighborFinset y b).mp hbY.1).symm)
  have hzH : z ∈ H := by
    refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_sdiff.mp hz).1⟩
    exact (D.mem_neighborFinset b z).mpr
      (((D.mem_neighborFinset z b).mp hbZ.1).symm)
  have htwo : 2 ≤ H.card := by
    have hsub : ({y, z} : Finset V) ⊆ H := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hyH
      · exact hzH
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hyz] at this
    exact this
  change H.card = 2
  omega

/-- The mixed column of a common missing row has the unique profile
`(special defects, ordinary defects, core, residual) = (2, 3, 15, 29)`.
The nominal three-special-defect alternative cannot occur. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_mixed_column_exact
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
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let A := fun t => (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
    let C := fun t => (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
    let defectRows := T.filter fun t => D.Adj t b
    let residualRows := T.filter fun t => (A t).Nonempty
    let coreRows := T.filter fun t => (C t).Nonempty
    let specialDefects := (D.neighborFinset b ∩ S).card
    specialDefects = 2 ∧ defectRows.card = 3 ∧
      coreRows.card = 15 ∧ residualRows.card = 29 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let A := fun t => (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let C := fun t => (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
  let defectRows := T.filter fun t => D.Adj t b
  let residualRows := T.filter fun t => (A t).Nonempty
  let coreRows := T.filter fun t => (C t).Nonempty
  let specialDefects := (D.neighborFinset b ∩ S).card
  have hs :=
    squareOrderNine_threeHigh_secondProfile_common_hole_specialDefects_eq_two
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  change specialDefects = 2 at hs
  have hbU1 : b ∈ B 1 \ (G.neighborFinset x ∩ B 1) :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp hb).1).2
  have hmixed :=
    squareOrderNine_threeHigh_secondProfile_unmarked_mixed_column_counts
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hbU1
  dsimp only at hmixed
  rcases hmixed with ⟨hdefect, hcore, hresidual⟩
  change defectRows.card + specialDefects = 5 at hdefect
  change coreRows.card = 15 at hcore
  change residualRows.card = 27 + specialDefects at hresidual
  have hd : defectRows.card = 3 := by omega
  have hr : residualRows.card = 29 := by omega
  exact ⟨hs, hd, hcore, hr⟩

/-- The five B0 neighbors of a common missing row all lie in the ordinary
47-row block.  Their induced ordinary-row degrees have the forced multiset
`{5,6,6,6,6}`: one support point has degree five and four have degree six.
Their disjoint neighbor blocks partition the 29 residual rows. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_degree_profile
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
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let Q0 := G.neighborFinset b ∩ B 0
    let Q := G.neighborFinset b ∩ T
    let F := fun q => G.neighborFinset q ∩ T
    let U := (S.biUnion fun s => G.neighborFinset s ∩ B 0) \ S
    Q0 = Q ∧ Q.card = 5 ∧ (∑ q ∈ Q, (F q).card) = 29 ∧
      (Q.filter fun q => (F q).card = 5).card = 1 ∧
      (Q.filter fun q => (F q).card = 6).card = 4 ∧
      (Q ∩ U).card = 1 ∧ (Q \ U).card = 4 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let Q0 := G.neighborFinset b ∩ B 0
  let Q := G.neighborFinset b ∩ T
  let F := fun q => G.neighborFinset q ∩ T
  let A := fun t => (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let residualRows := T.filter fun t => (A t).Nonempty
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_union
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  dsimp only at hpack
  have hQ0card : Q0.card = 5 := hpack.2.2.1
  have hQsubQ0 : Q ⊆ Q0 := by
    intro q hq
    have hqParts := Finset.mem_inter.mp hq
    exact Finset.mem_inter.mpr ⟨hqParts.1, (Finset.mem_sdiff.mp hqParts.2).1⟩
  have hQle : Q.card ≤ 5 := by
    calc Q.card ≤ Q0.card := Finset.card_le_card hQsubQ0
      _ = 5 := hQ0card
  have hexact :=
    squareOrderNine_threeHigh_secondProfile_common_hole_mixed_column_exact
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  dsimp only at hexact
  have hresidual : residualRows.card = 29 := hexact.2.2.2
  have hbNotT : b ∉ T := by
    intro hbT
    have hbB0 := (Finset.mem_sdiff.mp hbT).1
    have hbB1 := (Finset.mem_sdiff.mp
      (Finset.mem_inter.mp (Finset.mem_inter.mp hb).1).2).1
    have hk0 := (Finset.mem_filter.mp hbB0).2
    have hk1 := (Finset.mem_filter.mp hbB1).2
    omega
  have hgeneric :=
    c4Free_neighbor_blocks_partition_common_targets G hfree b T hbNotT
  dsimp only at hgeneric
  have hdisj : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → Disjoint (F q) (F r) := by
    intro q hq r hr hqr
    exact hgeneric.1 q (Finset.mem_inter.mp hq).1
      r (Finset.mem_inter.mp hr).1 hqr
  have hunion : Q.biUnion F = residualRows := by
    ext t
    constructor
    · intro htUnion
      simp only [Finset.mem_biUnion] at htUnion
      obtain ⟨q, hqQ, htF⟩ := htUnion
      have hqParts := Finset.mem_inter.mp hqQ
      have htParts := Finset.mem_inter.mp htF
      refine Finset.mem_filter.mpr ⟨htParts.2, ⟨q, ?_⟩⟩
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset t q).mpr
          ((G.adj_comm q t).mp ((G.mem_neighborFinset q t).mp htParts.1)),
        hqParts.2⟩, hqParts.1⟩
    · intro htFilter
      have htParts := Finset.mem_filter.mp htFilter
      obtain ⟨q, hqA⟩ := htParts.2
      have hqAParts := Finset.mem_inter.mp hqA
      have htq := Finset.mem_inter.mp hqAParts.1
      simp only [Finset.mem_biUnion]
      exact ⟨q, Finset.mem_inter.mpr ⟨hqAParts.2, htq.2⟩,
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset q t).mpr
            ((G.adj_comm t q).mp ((G.mem_neighborFinset t q).mp htq.1)),
          htParts.1⟩⟩
  have hsum : (∑ q ∈ Q, (F q).card) = 29 := by
    rw [← Finset.card_biUnion hdisj, hunion, hresidual]
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_ordinary_binZero_residual_census
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  let U := (S.biUnion fun s => G.neighborFinset s ∩ B 0) \ S
  have hdegree : ∀ q ∈ Q, (F q).card = if q ∈ U then 5 else 6 := by
    intro q hq
    have hqT := (Finset.mem_inter.mp hq).2
    have hqDeg := hcensus.2.2.1 ⟨q, hqT⟩
    rw [degree_induce_finset_eq_card_inter] at hqDeg
    exact hqDeg
  have hQge : 5 ≤ Q.card := by
    have hbound : (∑ q ∈ Q, (F q).card) ≤ ∑ _q ∈ Q, 6 := by
      apply Finset.sum_le_sum
      intro q hq
      rw [hdegree q hq]
      split <;> omega
    have hprod : 29 ≤ Q.card * 6 := by
      calc
        29 = ∑ q ∈ Q, (F q).card := hsum.symm
        _ ≤ ∑ _q ∈ Q, 6 := hbound
        _ = Q.card * 6 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
    omega
  have hQcard : Q.card = 5 := by omega
  have hQQ0 : Q = Q0 :=
    Finset.eq_of_subset_of_card_le hQsubQ0 (by omega)
  let Q5 := Q.filter fun q => (F q).card = 5
  let Q6 := Q.filter fun q => (F q).card = 6
  have hsplit : Q = Q5 ∪ Q6 := by
    ext q
    simp only [Q5, Q6, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      rw [hdegree q hq]
      split <;> simp_all
    · tauto
  have h56 : Disjoint Q5 Q6 := by
    rw [Finset.disjoint_left]
    intro q hq5 hq6
    have h5 := (Finset.mem_filter.mp hq5).2
    have h6 := (Finset.mem_filter.mp hq6).2
    omega
  have hcards : Q5.card + Q6.card = 5 := by
    have := congrArg Finset.card hsplit
    rw [Finset.card_union_of_disjoint h56, hQcard] at this
    omega
  have hsum56 : 5 * Q5.card + 6 * Q6.card = 29 := by
    calc
      5 * Q5.card + 6 * Q6.card =
          (∑ q ∈ Q5, (F q).card) + ∑ q ∈ Q6, (F q).card := by
        congr 1
        · calc
            5 * Q5.card = ∑ _q ∈ Q5, 5 := by simp [Nat.mul_comm]
            _ = ∑ q ∈ Q5, (F q).card := by
              apply Finset.sum_congr rfl
              intro q hq
              exact ((Finset.mem_filter.mp hq).2).symm
        · calc
            6 * Q6.card = ∑ _q ∈ Q6, 6 := by simp [Nat.mul_comm]
            _ = ∑ q ∈ Q6, (F q).card := by
              apply Finset.sum_congr rfl
              intro q hq
              exact ((Finset.mem_filter.mp hq).2).symm
      _ = ∑ q ∈ Q, (F q).card := by
        rw [hsplit, Finset.sum_union h56]
      _ = 29 := hsum
  have hQ5 : Q5.card = 1 := by omega
  have hQ6 : Q6.card = 4 := by omega
  have hQ5U : Q5 = Q ∩ U := by
    ext q
    simp only [Q5, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hq, hq5⟩
      refine ⟨hq, ?_⟩
      rw [hdegree q hq] at hq5
      by_contra hqU
      simp [hqU] at hq5
    · rintro ⟨hq, hqU⟩
      refine ⟨hq, ?_⟩
      rw [hdegree q hq]
      simp [hqU]
  have hQ6U : Q6 = Q \ U := by
    ext q
    simp only [Q6, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hq, hq6⟩
      refine ⟨hq, ?_⟩
      intro hqU
      rw [hdegree q hq] at hq6
      simp [hqU] at hq6
    · rintro ⟨hq, hqU⟩
      refine ⟨hq, ?_⟩
      rw [hdegree q hq]
      simp [hqU]
  exact ⟨hQQ0.symm, hQcard, hsum, hQ5, hQ6,
    hQ5U ▸ hQ5, hQ6U ▸ hQ6⟩

/-- Let `w` be the third special B0 row, distinct from the two puncture
endpoints.  A common missing row has exactly one B0 neighbor on `w`'s row
and four B0 neighbors off it.  The unique neighbor on `w`'s row is exactly
the degree-five point in its five-support profile. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_third_row_owner
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
    {x y z w b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hw : w ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let Q := G.neighborFinset b ∩ T
    let Rw := G.neighborFinset w ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    (Q ∩ Rw).card = 1 ∧ (Q \ Rw).card = 4 ∧
      (∀ q ∈ Q ∩ Rw, q ∉ P ∧
        (G.neighborFinset q ∩ U1).card = 3) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let Q0 := G.neighborFinset b ∩ B 0
  let Q := G.neighborFinset b ∩ T
  let Ry := G.neighborFinset y ∩ B 0
  let Rz := G.neighborFinset z ∩ B 0
  let Rw := G.neighborFinset w ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let U := (S.biUnion fun s => G.neighborFinset s ∩ B 0) \ S
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_degree_profile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  dsimp only at hprofile
  have hQ0eq : Q0 = Q := hprofile.1
  have hQcard : Q.card = 5 := hprofile.2.1
  have hQUcard : (Q ∩ U).card = 1 := hprofile.2.2.2.2.2.1
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_union
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  dsimp only at hpack
  have hYQ0 : Disjoint Ry Q0 := hpack.2.2.2.2.1
  have hZQ0 : Disjoint Rz Q0 := hpack.2.2.2.2.2.1
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hScard : S.card = 3 := hcensus.2.2
  have hyS : y ∈ S := (Finset.mem_sdiff.mp hy).1
  have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
  have hwS : w ∈ S := hw
  let P3 : Finset V := {y, z, w}
  have hPsub : P3 ⊆ S := by
    intro v hv
    simp only [P3, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hyS
    · exact hzS
    · exact hwS
  have hPcard : P3.card = 3 := by
    have hyNot : y ∉ ({z, w} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hyz, fun h => hwy h.symm⟩
    have hzNot : z ∉ ({w} : Finset V) := by
      simp only [Finset.mem_singleton]
      exact fun h => hwz h.symm
    change ({y, z, w} : Finset V).card = 3
    rw [Finset.card_insert_of_notMem hyNot,
      Finset.card_insert_of_notMem hzNot]
    simp
  have hPS : P3 = S :=
    Finset.eq_of_subset_of_card_le hPsub (by rw [hPcard, hScard])
  have hQUeq : Q ∩ U = Q ∩ Rw := by
    ext q
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hqQ, hqU⟩
      refine ⟨hqQ, ?_⟩
      have hqUParts := Finset.mem_sdiff.mp hqU
      simp only [Finset.mem_biUnion] at hqUParts
      obtain ⟨s, hsS, hqs⟩ := hqUParts.1
      have hsP : s ∈ P3 := by rw [hPS]; exact hsS
      simp only [P3, Finset.mem_insert, Finset.mem_singleton] at hsP
      rcases hsP with rfl | rfl | rfl
      · have hqQ0 : q ∈ Q0 := hQ0eq.symm ▸ hqQ
        exact ((Finset.disjoint_left.mp hYQ0) hqs hqQ0).elim
      · have hqQ0 : q ∈ Q0 := hQ0eq.symm ▸ hqQ
        exact ((Finset.disjoint_left.mp hZQ0) hqs hqQ0).elim
      · exact hqs
    · rintro ⟨hqQ, hqRw⟩
      refine ⟨hqQ, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · simp only [Finset.mem_biUnion]
        exact ⟨w, hwS, hqRw⟩
      · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hqQ).2).2
  have hQRw : (Q ∩ Rw).card = 1 := by
    rw [← hQUeq]
    exact hQUcard
  have hQdiff : (Q \ Rw).card = 4 := by
    rw [Finset.card_sdiff, hQcard, Finset.inter_comm Rw Q, hQRw]
  have hpairCensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpairCensus
  have howner : ∀ q ∈ Q ∩ Rw, q ∉ P ∧
      (G.neighborFinset q ∩ U1).card = 3 := by
    intro q hqOwner
    have hqParts := Finset.mem_inter.mp hqOwner
    have hqQParts := Finset.mem_inter.mp hqParts.1
    have hqT := hqQParts.2
    have hqRw := Finset.mem_inter.mp hqParts.2
    have hqNotP : q ∉ P := by
      intro hqP
      simp only [P, Finset.mem_biUnion] at hqP
      obtain ⟨m, hmM, hmq⟩ := hqP
      have hmParts := Finset.mem_inter.mp hmM
      have hmqParts := Finset.mem_inter.mp hmq
      have hwParts := Finset.mem_inter.mp hw
      have hxq : x ≠ q := by
        intro hxq
        subst q
        have hk3 := (Finset.mem_filter.mp hx).2
        have hk0 := (Finset.mem_filter.mp
          (Finset.mem_sdiff.mp hqT).1).2
        omega
      have hwm : w ≠ m := by
        intro hwm
        subst m
        have hk0 := (Finset.mem_filter.mp hwParts.2).2
        have hk1 := (Finset.mem_filter.mp hmParts.2).2
        omega
      have hwCommon : w ∈ G.neighborFinset x ∩ G.neighborFinset q := by
        refine Finset.mem_inter.mpr ⟨hwParts.1, ?_⟩
        exact (G.mem_neighborFinset q w).mpr
          ((G.adj_comm w q).mp ((G.mem_neighborFinset w q).mp hqRw.1))
      have hmCommon : m ∈ G.neighborFinset x ∩ G.neighborFinset q := by
        refine Finset.mem_inter.mpr ⟨hmParts.1, ?_⟩
        exact (G.mem_neighborFinset q m).mpr
          ((G.adj_comm m q).mp ((G.mem_neighborFinset m q).mp hmqParts.1))
      have hle := (not_containsC4_iff_forall_common_le_one G).mp
        hfree x q hxq
      exact hwm (Finset.card_le_one.mp hle w hwCommon m hmCommon)
    refine ⟨hqNotP, ?_⟩
    exact hpairCensus.2.2.2.1 q
      (Finset.mem_sdiff.mpr ⟨hqT, hqNotP⟩)
  exact ⟨hQRw, hQdiff, howner⟩

/-- Pointwise U1 pair budget for a common missing row.  Its B0 common-center
blocks, together with its defect neighbors inside U1, have total size ten;
the remaining thirteen partners are covered by its three U1 centers (six)
and its unique high center (seven). -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_B0_defect_partner_budget
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
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let Q := G.neighborFinset b ∩ B 0
    let D1 := (secondOrderDefectGraph G).neighborFinset b ∩ U1
    (∑ q ∈ Q, (G.neighborFinset q ∩ U1.erase b).card) + D1.card = 10 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let H := squareOrderHighVertices G 9
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let U := U1.erase b
  let D := secondOrderDefectGraph G
  let Q := G.neighborFinset b ∩ B 0
  let C1 := G.neighborFinset b ∩ B 1
  let C1u := G.neighborFinset b ∩ U1
  let CH := G.neighborFinset b ∩ H
  let F := fun c => G.neighborFinset c ∩ U
  let D1 := D.neighborFinset b ∩ U1
  have hbParts := Finset.mem_inter.mp (Finset.mem_inter.mp hb).1
  have hbU1 : b ∈ U1 := hbParts.2
  have hbB1 : b ∈ B 1 := (Finset.mem_sdiff.mp hbU1).1
  have hbNotX : ¬ G.Adj b x := by
    intro hbx
    exact (Finset.mem_sdiff.mp hbU1).2 (Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x b).mpr hbx.symm, hbB1⟩)
  have hU1card : U1.card = 24 := by
    have hmarked :=
      squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
    dsimp only at hmarked
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_right,
      hmarked.1, hmarked.2]
  have hUcard : U.card = 23 := by
    change (U1.erase b).card = 23
    rw [Finset.card_erase_of_mem hbU1, hU1card]
  have hbNotU : b ∉ U := Finset.notMem_erase b U1
  have htotal :=
    c4Free_sum_neighbor_block_cards_eq_defect_complement
      G hfree b U hbNotU
  dsimp only at htotal
  change (∑ c ∈ G.neighborFinset b, (F c).card) =
    (U \ D.neighborFinset b).card at htotal
  have hDU : D.neighborFinset b ∩ U = D1 := by
    ext v
    simp only [U, D1, Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨hvD, _hvb, hvU1⟩
      exact ⟨hvD, hvU1⟩
    · rintro ⟨hvD, hvU1⟩
      exact ⟨hvD, D.ne_of_adj ((D.mem_neighborFinset b v).mp hvD) |>.symm,
        hvU1⟩
  have hright : (U \ D.neighborFinset b).card = 23 - D1.card := by
    rw [Finset.card_sdiff, hDU, hUcard]
  have hC1card : C1.card = 3 := by
    have hdeg :=
      squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hbB1
    dsimp only at hdeg
    simpa [hbNotX] using hdeg.1
  have hcubic :=
    squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcubic
  have hC1ucard : C1u.card = 3 := by
    have hdeg := hcubic.2.1 (⟨b, hbU1⟩ : ↥(↑U1 : Set V))
    rw [degree_induce_finset_eq_card_inter] at hdeg
    exact hdeg
  have hC1ueq : C1 = C1u := by
    have hsub : C1u ⊆ C1 := by
      intro c hc
      have hcParts := Finset.mem_inter.mp hc
      exact Finset.mem_inter.mpr ⟨hcParts.1,
        (Finset.mem_sdiff.mp hcParts.2).1⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hC1card, hC1ucard]) |>.symm
  have hCHcard : CH.card = 1 := (Finset.mem_filter.mp hbB1).2
  have hQcard : Q.card = 5 := by
    have hprofile :=
      squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_degree_profile
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
    dsimp only at hprofile
    change (G.neighborFinset b ∩ B 0).card = 5
    exact hprofile.1 ▸ hprofile.2.1
  have hQsub : Q ⊆ G.neighborFinset b := Finset.inter_subset_left
  have hC1sub : C1 ⊆ G.neighborFinset b := Finset.inter_subset_left
  have hCHsub : CH ⊆ G.neighborFinset b := Finset.inter_subset_left
  have hQ_C1 : Disjoint Q C1 := by
    rw [Finset.disjoint_left]
    intro v hvQ hvC
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hvQ).2).2
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hvC).2).2
    omega
  have hQ_CH : Disjoint Q CH := by
    rw [Finset.disjoint_left]
    intro v hvQ hvH
    have hvLow := (Finset.mem_filter.mp (Finset.mem_inter.mp hvQ).2).1
    exact (Finset.mem_sdiff.mp hvLow).2 (Finset.mem_inter.mp hvH).2
  have hC1_CH : Disjoint C1 CH := by
    rw [Finset.disjoint_left]
    intro v hvC hvH
    have hvLow := (Finset.mem_filter.mp (Finset.mem_inter.mp hvC).2).1
    exact (Finset.mem_sdiff.mp hvLow).2 (Finset.mem_inter.mp hvH).2
  have hcentersSub : (Q ∪ C1) ∪ CH ⊆ G.neighborFinset b :=
    Finset.union_subset (Finset.union_subset hQsub hC1sub) hCHsub
  have hbDegree : G.degree b = 9 := by
    rcases hp.degree_dichotomy b with hlo | hhi
    · exact hlo
    · have hbLow := (Finset.mem_filter.mp hbB1).1
      exact ((Finset.mem_sdiff.mp hbLow).2
        (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hcentersCard : ((Q ∪ C1) ∪ CH).card = 9 := by
    have hQC_CH : Disjoint (Q ∪ C1) CH := by
      rw [Finset.disjoint_left]
      intro v hv hvH
      rcases Finset.mem_union.mp hv with hvQ | hvC
      · exact (Finset.disjoint_left.mp hQ_CH) hvQ hvH
      · exact (Finset.disjoint_left.mp hC1_CH) hvC hvH
    rw [Finset.card_union_of_disjoint hQC_CH,
      Finset.card_union_of_disjoint hQ_C1, hQcard, hC1card, hCHcard]
  have hcenters : (Q ∪ C1) ∪ CH = G.neighborFinset b := by
    apply Finset.eq_of_subset_of_card_le hcentersSub
    rw [hcentersCard, G.card_neighborFinset_eq_degree, hbDegree]
  have hC1sum : (∑ c ∈ C1, (F c).card) = 6 := by
    calc
      _ = ∑ _c ∈ C1, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcU1 : c ∈ U1 := by
          rw [hC1ueq] at hc
          exact (Finset.mem_inter.mp hc).2
        have hdeg := hcubic.2.1 (⟨c, hcU1⟩ : ↥(↑U1 : Set V))
        rw [degree_induce_finset_eq_card_inter] at hdeg
        have hbc : b ∈ G.neighborFinset c ∩ U1 :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset c b).mpr
            (((G.mem_neighborFinset b c).mp (Finset.mem_inter.mp hc).1).symm), hbU1⟩
        change (G.neighborFinset c ∩ U1.erase b).card = 2
        rw [Finset.inter_erase, Finset.card_erase_of_mem hbc, hdeg]
      _ = 6 := by simp [hC1card]
  have hfibers :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hfibers
  have hCHsum : (∑ a ∈ CH, (F a).card) = 7 := by
    calc
      _ = ∑ _a ∈ CH, 7 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haParts := Finset.mem_inter.mp ha
        have hfiber := hfibers.2.1 a haParts.2
        have hba : b ∈ G.neighborFinset a ∩ U1 :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr
            (((G.mem_neighborFinset b a).mp haParts.1).symm), hbU1⟩
        change (G.neighborFinset a ∩ U1.erase b).card = 7
        rw [Finset.inter_erase, Finset.card_erase_of_mem hba, hfiber]
      _ = 7 := by simp [hCHcard]
  have hleft : (∑ c ∈ G.neighborFinset b, (F c).card) =
      (∑ q ∈ Q, (F q).card) + 13 := by
    rw [← hcenters, Finset.sum_union]
    · rw [Finset.sum_union hQ_C1, hC1sum, hCHsum]
    · rw [Finset.disjoint_left]
      intro v hv hvH
      rcases Finset.mem_union.mp hv with hvQ | hvC
      · exact (Finset.disjoint_left.mp hQ_CH) hvQ hvH
      · exact (Finset.disjoint_left.mp hC1_CH) hvC hvH
  change (∑ q ∈ Q, (F q).card) + D1.card = 10
  rw [hleft, hright] at htotal
  omega

/-- Among the four degree-six B0 support points off the third special row,
the number outside the marked-support target plus the common row's U1
defect degree is exactly four.  In particular at least two of the four are
outside the marked-support target. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_degreeSix_marked_census
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
    {x y z w b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hw : w ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let Q := G.neighborFinset b ∩ T
    let Rw := G.neighborFinset w ∩ B 0
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let O := (Q \ Rw) \ P
    let D1 := (secondOrderDefectGraph G).neighborFinset b ∩ U1
    O.card + D1.card = 4 ∧ 2 ≤ O.card ∧ D1.card ≤ 2 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let Q0 := G.neighborFinset b ∩ B 0
  let Q := G.neighborFinset b ∩ T
  let Rw := G.neighborFinset w ∩ B 0
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let A := Q ∩ Rw
  let R := Q \ Rw
  let RP := R ∩ P
  let O := R \ P
  let D := secondOrderDefectGraph G
  let D1 := D.neighborFinset b ∩ U1
  let K := fun q => G.neighborFinset q ∩ U1.erase b
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_degree_profile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  dsimp only at hprofile
  have hQ0eq : Q0 = Q := hprofile.1
  have howner :=
    squareOrderNine_threeHigh_secondProfile_common_hole_third_row_owner
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz
        hw hwy hwz hb
  dsimp only at howner
  have hAcard : A.card = 1 := howner.1
  have hRcard : R.card = 4 := howner.2.1
  have hAoff : ∀ q ∈ A, q ∉ P ∧
      (G.neighborFinset q ∩ U1).card = 3 := howner.2.2
  have hbudget :=
    squareOrderNine_threeHigh_secondProfile_common_hole_B0_defect_partner_budget
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz hb
  dsimp only at hbudget
  change (∑ q ∈ Q0, (K q).card) + D1.card = 10 at hbudget
  rw [hQ0eq] at hbudget
  have hpairCensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpairCensus
  have hbU1 : b ∈ U1 :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp hb).1).2
  have hQsplit : Q = A ∪ R := by
    ext q
    simp only [A, R, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hAR : Disjoint A R := by
    rw [Finset.disjoint_left]
    intro q hqA hqR
    exact (Finset.mem_sdiff.mp hqR).2 (Finset.mem_inter.mp hqA).2
  have hRsplit : R = RP ∪ O := by
    ext q
    simp only [RP, O, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hRPO : Disjoint RP O := by
    rw [Finset.disjoint_left]
    intro q hqP hqO
    exact (Finset.mem_sdiff.mp hqO).2 (Finset.mem_inter.mp hqP).2
  have hcards : RP.card + O.card = 4 := by
    have := congrArg Finset.card hRsplit
    rw [Finset.card_union_of_disjoint hRPO, hRcard] at this
    omega
  have hKcard (q : V) (hqQ : q ∈ Q) :
      (K q).card = if q ∈ P then 1 else 2 := by
    have hqT := (Finset.mem_inter.mp hqQ).2
    have hbq : b ∈ G.neighborFinset q ∩ U1 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset q b).mpr
        (((G.mem_neighborFinset b q).mp (Finset.mem_inter.mp hqQ).1).symm), hbU1⟩
    by_cases hqP : q ∈ P
    · have hdeg := hpairCensus.2.2.1 q hqP
      simp only [hqP, if_true]
      change (G.neighborFinset q ∩ U1.erase b).card = 1
      rw [Finset.inter_erase, Finset.card_erase_of_mem hbq, hdeg]
    · have hdeg := hpairCensus.2.2.2.1 q
        (Finset.mem_sdiff.mpr ⟨hqT, hqP⟩)
      simp only [hqP, if_false]
      change (G.neighborFinset q ∩ U1.erase b).card = 2
      rw [Finset.inter_erase, Finset.card_erase_of_mem hbq, hdeg]
  have hAsum : (∑ q ∈ A, (K q).card) = 2 := by
    calc
      _ = ∑ _q ∈ A, 2 := by
        apply Finset.sum_congr rfl
        intro q hqA
        have hqQ := (Finset.mem_inter.mp hqA).1
        rw [hKcard q hqQ]
        simp [hAoff q hqA |>.1]
      _ = 2 := by simp [hAcard]
  have hRPsum : (∑ q ∈ RP, (K q).card) = RP.card := by
    calc
      _ = ∑ _q ∈ RP, 1 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqParts := Finset.mem_inter.mp hq
        have hqQ := (Finset.mem_sdiff.mp hqParts.1).1
        rw [hKcard q hqQ]
        simp [hqParts.2]
      _ = RP.card := by simp
  have hOsum : (∑ q ∈ O, (K q).card) = 2 * O.card := by
    calc
      _ = ∑ _q ∈ O, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqParts := Finset.mem_sdiff.mp hq
        have hqQ := (Finset.mem_sdiff.mp hqParts.1).1
        rw [hKcard q hqQ]
        simp [hqParts.2]
      _ = 2 * O.card := by simp [Nat.mul_comm]
  have hsum : (∑ q ∈ Q, (K q).card) = 6 + O.card := by
    rw [hQsplit, Finset.sum_union hAR, hAsum,
      hRsplit, Finset.sum_union hRPO, hRPsum, hOsum]
    omega
  have hDtotal :=
    squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4
        ((Finset.mem_sdiff.mp hbU1).1)
  dsimp only at hDtotal
  have hD1sub : D1 ⊆ D.neighborFinset b ∩ B 1 := by
    intro v hv
    have hvParts := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨hvParts.1,
      (Finset.mem_sdiff.mp hvParts.2).1⟩
  have hDle : D1.card ≤ 2 := by
    calc D1.card ≤ (D.neighborFinset b ∩ B 1).card :=
        Finset.card_le_card hD1sub
      _ = 2 := hDtotal.2.1
  rw [hsum] at hbudget
  change (6 + O.card) + D1.card = 10 at hbudget
  have heq : O.card + D1.card = 4 := by omega
  have hOge : 2 ≤ O.card := by omega
  exact ⟨heq, hOge, hDle⟩

/-- The common-hole degree-six census can be expressed entirely in terms of
marked defect incidence: the number of degree-six support points outside the
marked-support target is two plus the number of marked defect neighbors of
the common row. -/
theorem squareOrderNine_threeHigh_secondProfile_common_hole_degreeSix_marked_exact
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
    {x y z w b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hw : w ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)
    (hwy : w ≠ y) (hwz : w ≠ z)
    (hb : b ∈
      ((secondOrderDefectGraph G).neighborFinset y ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) ∩
      ((secondOrderDefectGraph G).neighborFinset z ∩
        (squareOrderNineLowIncidenceBin G 1 \
          (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let Q := G.neighborFinset b ∩ T
    let Rw := G.neighborFinset w ∩ B 0
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let O := (Q \ Rw) \ P
    let DM := (secondOrderDefectGraph G).neighborFinset b ∩ M
    O.card = 2 + DM.card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let Q := G.neighborFinset b ∩ T
  let Rw := G.neighborFinset w ∩ B 0
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let O := (Q \ Rw) \ P
  let D := secondOrderDefectGraph G
  let DM := D.neighborFinset b ∩ M
  let D1 := D.neighborFinset b ∩ U1
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_common_hole_degreeSix_marked_census
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hz hyz
        hw hwy hwz hb
  dsimp only at hcensus
  have hOD1 : O.card + D1.card = 4 := by
    simpa [O, D1, Q, Rw, P, T, S, U1, M, B, D] using hcensus.1
  have hbU1 : b ∈ U1 :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp hb).1).2
  have hBsplit : B 1 = M ∪ U1 := by
    ext v
    simp only [M, U1, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hMUdisj : Disjoint M U1 := by
    rw [Finset.disjoint_left]
    intro v hvM hvU
    exact (Finset.mem_sdiff.mp hvU).2 hvM
  have hsplit : DM.card + D1.card =
      (D.neighborFinset b ∩ B 1).card := by
    rw [hBsplit, Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint
        (hMUdisj.mono Finset.inter_subset_right Finset.inter_subset_right)]
  have hDtotal :=
    squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4
        ((Finset.mem_sdiff.mp hbU1).1)
  dsimp only at hDtotal
  have hMD1 : DM.card + D1.card = 2 := by
    calc
      DM.card + D1.card = (D.neighborFinset b ∩ B 1).card := hsplit
      _ = 2 := hDtotal.2.1
  dsimp [O, DM, D1, Q, Rw, P, T, S, U1, M, B, D] at hOD1 hMD1 ⊢
  omega

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_supports_disjoint
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_support_card_fourteen
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_puncture_design
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_puncture_row_equation
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_unmarked_defect_card_three
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_defect_census
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_puncture_resolution
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_resolutions_cross_le_one
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_supports_anticomplete
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_puncture_blocks_rainbow
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_puncture_hole_rainbow
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_hole_color_agreement
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_color_shared_rows
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_paired_resolution_matching
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_union
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_mixed_column_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_specialDefects_eq_two
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_mixed_column_exact
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_B0_support_degree_profile
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_third_row_owner
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_B0_defect_partner_budget
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_degreeSix_marked_census
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_common_hole_degreeSix_marked_exact
