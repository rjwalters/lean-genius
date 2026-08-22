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
