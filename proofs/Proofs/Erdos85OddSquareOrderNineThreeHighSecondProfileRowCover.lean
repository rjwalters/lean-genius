import Proofs.Erdos85C4FreeNeighborBlockPartition
import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes

/-! # Row covers for the q=9 three-high second profile

This module applies the generic C4-free neighbor-block partition without
adding further material to the large bin-zero classification module.  Every
ordinary bin-zero row partitions the unmarked 24-point bin-one core outside
its defect neighborhood.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For every bin-zero vertex, its neighbor rows cover the unmarked bin-one
core with no overlap.  Numerically, the total row mass is `24` minus its
number of unmarked bin-one defect neighbors. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    (∑ w ∈ G.neighborFinset t,
      (G.neighborFinset w ∩ U1).card) =
        24 - (D.neighborFinset t ∩ U1).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMcard :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hMcard]
  have htNotU1 : t ∉ U1 := by
    intro htU1
    have htB1 := (Finset.mem_sdiff.mp htU1).1
    have hkt0 := (Finset.mem_filter.mp ht).2
    have hkt1 := (Finset.mem_filter.mp htB1).2
    omega
  have hcover := c4Free_sum_neighbor_block_cards_eq_defect_complement
    G hfree t U1 htNotU1
  dsimp only at hcover
  rw [hcover, Finset.card_sdiff, hU1card]

/-- Weighted defect-type form of the row cover.  A regular bin-zero row has
unmarked row mass `21` plus its number of defect edges to the three marked
bin-one points; an exceptional row has full mass `24`. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_row_mass_dichotomy
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let mass := ∑ w ∈ G.neighborFinset t,
      (G.neighborFinset w ∩ U1).card
    mass = 21 + (D.neighborFinset t ∩ M).card ∨ mass = 24 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let mass := ∑ w ∈ G.neighborFinset t,
    (G.neighborFinset w ∩ U1).card
  have hrow :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hrow
  change mass = 24 - (D.neighborFinset t ∩ U1).card at hrow
  have htype :=
    squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc4 ht
  dsimp only at htype
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hpartition : D.neighborFinset t ∩ B 1 =
      (D.neighborFinset t ∩ U1) ∪ (D.neighborFinset t ∩ M) := by
    ext y
    constructor
    · intro hy
      have hyParts := Finset.mem_inter.mp hy
      by_cases hyM : y ∈ M
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hyParts.1, hyM⟩)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hyParts.1,
          Finset.mem_sdiff.mpr ⟨hyParts.2, hyM⟩⟩)
    · intro hy
      rcases Finset.mem_union.mp hy with hyU | hyM
      · have hyParts := Finset.mem_inter.mp hyU
        exact Finset.mem_inter.mpr ⟨hyParts.1,
          (Finset.mem_sdiff.mp hyParts.2).1⟩
      · have hyParts := Finset.mem_inter.mp hyM
        exact Finset.mem_inter.mpr ⟨hyParts.1, hMsub hyParts.2⟩
  have hdisj : Disjoint (D.neighborFinset t ∩ U1)
      (D.neighborFinset t ∩ M) := by
    rw [Finset.disjoint_left]
    intro y hyU hyM
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hyU).2).2
      (Finset.mem_inter.mp hyM).2
  have hcards := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdisj] at hcards
  rcases htype with hregular | hexceptional
  · left
    rw [hregular.2.1] at hcards
    change mass = 21 + (D.neighborFinset t ∩ M).card
    rw [hrow]
    omega
  · right
    rw [hexceptional.2.1] at hcards
    change mass = 24
    rw [hrow]
    omega

/-- Exact center weights on the two nonzero parts of a row cover.  Residual
bin-zero centers in the marked support union contribute two unmarked points,
the other residual bin-zero centers contribute three, and every unmarked
bin-one center contributes three by cubicity. -/
theorem squareOrderNine_threeHigh_secondProfile_row_center_weight_sums
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    (∑ w ∈ R, (G.neighborFinset w ∩ U1).card) =
        2 * (R.filter fun w => w ∈ P).card +
          3 * (R.filter fun w => w ∉ P).card ∧
      (∑ w ∈ G.neighborFinset t ∩ U1,
        (G.neighborFinset w ∩ U1).card) =
          3 * (G.neighborFinset t ∩ U1).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let R := G.neighborFinset t ∩ T
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hcore :=
    squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcore
  constructor
  · calc
      (∑ w ∈ R, (G.neighborFinset w ∩ U1).card) =
          ∑ w ∈ R, if w ∈ P then 2 else 3 := by
        apply Finset.sum_congr rfl
        intro w hwR
        have hwT := (Finset.mem_inter.mp hwR).2
        by_cases hwP : w ∈ P
        · rw [if_pos hwP]
          exact hcensus.2.2.1 w hwP
        · rw [if_neg hwP]
          exact hcensus.2.2.2.1 w
            (Finset.mem_sdiff.mpr ⟨hwT, hwP⟩)
      _ = 2 * (R.filter fun w => w ∈ P).card +
          3 * (R.filter fun w => w ∉ P).card := by
        rw [Finset.sum_ite]
        simp [Nat.mul_comm]
  · calc
      (∑ w ∈ G.neighborFinset t ∩ U1,
          (G.neighborFinset w ∩ U1).card) =
          ∑ _w ∈ G.neighborFinset t ∩ U1, 3 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwU := (Finset.mem_inter.mp hw).2
        have hdeg := hcore.2.1 ⟨w, hwU⟩
        rw [degree_induce_finset_eq_card_inter] at hdeg
        exact hdeg
      _ = 3 * (G.neighborFinset t ∩ U1).card := by
        simp [Nat.mul_comm]

/-- The remaining named center classes have zero weight in an ordinary B0
row cover.  Special B0 and marked B1 centers have no unmarked B1 neighbors;
an ordinary B0 row has neither high nor B3 centers. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_row_zero_centers
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    (∀ s ∈ S, (G.neighborFinset s ∩ U1).card = 0) ∧
      (∀ m ∈ M, (G.neighborFinset m ∩ U1).card = 0) ∧
      G.neighborFinset t ∩ H = ∅ ∧
      G.neighborFinset t ∩ B 3 = ∅ := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  have htParts := Finset.mem_sdiff.mp ht
  have hspecial : ∀ s ∈ S, (G.neighborFinset s ∩ U1).card = 0 := by
    intro s hs
    rw [Finset.card_eq_zero]
    ext b
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hsb hbU
    have hsParts := Finset.mem_inter.mp hs
    have hbB1 := (Finset.mem_sdiff.mp hbU).1
    have hxs : G.Adj x s := (G.mem_neighborFinset x s).mp hsParts.1
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hsParts.2 hbB1 hxs)
      ((G.mem_neighborFinset s b).mp hsb)
  have hmarked : ∀ m ∈ M, (G.neighborFinset m ∩ U1).card = 0 := by
    intro m hm
    have hmParts := Finset.mem_inter.mp hm
    have hmx : G.Adj m x := (G.adj_comm x m).mp
      ((G.mem_neighborFinset x m).mp hmParts.1)
    have hdeg := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hmParts.2
    dsimp only at hdeg
    have hzero : (G.neighborFinset m ∩ B 1).card = 0 := by
      simpa [hmx] using hdeg.1
    apply Nat.eq_zero_of_le_zero
    calc
      (G.neighborFinset m ∩ U1).card ≤
          (G.neighborFinset m ∩ B 1).card := by
        apply Finset.card_le_card
        intro b hb
        have hbParts := Finset.mem_inter.mp hb
        exact Finset.mem_inter.mpr ⟨hbParts.1,
          (Finset.mem_sdiff.mp hbParts.2).1⟩
      _ = 0 := hzero
  have hnoHigh : G.neighborFinset t ∩ H = ∅ := by
    rw [← Finset.card_eq_zero]
    change squareOrderHighIncidenceCount G 9 t = 0
    exact (Finset.mem_filter.mp htParts.1).2
  have hB3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hB3singleton : B 3 = {x} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun y hy => Finset.card_le_one.mp (by omega) y hy x hx⟩
  have hnoB3 : G.neighborFinset t ∩ B 3 = ∅ := by
    rw [hB3singleton]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyParts := Finset.mem_inter.mp hy
    have hyx : y = x := Finset.mem_singleton.mp hyParts.2
    subst y
    exact htParts.2 (Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x t).mpr
        ((G.adj_comm t x).mp ((G.mem_neighborFinset t x).mp hyParts.1)),
      htParts.1⟩)
  exact ⟨hspecial, hmarked, hnoHigh, hnoB3⟩

/-- The neighbors of an ordinary B0 vertex are exhausted by the four center
classes `S`, `T`, `M`, and `U1`. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    G.neighborFinset t =
      ((G.neighborFinset t ∩ S) ∪ (G.neighborFinset t ∩ T)) ∪
        ((G.neighborFinset t ∩ M) ∪ (G.neighborFinset t ∩ U1)) := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let N := G.neighborFinset t
  have htParts := Finset.mem_sdiff.mp ht
  have htLow := (Finset.mem_filter.mp htParts.1).1
  have htNotHigh : t ∉ H := (Finset.mem_sdiff.mp htLow).2
  have hzero := squareOrderNine_threeHigh_secondProfile_ordinary_row_zero_centers
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hzero
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpnt := squareOrderNine_originalNeighbor_lowBin_partition G hp htNotHigh
  change (∑ j ∈ Finset.range 5, (N ∩ B j).card) +
      squareOrderHighIncidenceCount G 9 t = G.degree t at hpnt
  have hkt : squareOrderHighIncidenceCount G 9 t = 0 :=
    (Finset.mem_filter.mp htParts.1).2
  rw [hkt] at hpnt
  norm_num [Finset.sum_range_succ] at hpnt
  rw [hB2, hB4, hzero.2.2.2] at hpnt
  simp only [Finset.inter_empty, Finset.card_empty, add_zero] at hpnt
  have hbinDisj : Disjoint (N ∩ B 0) (N ∩ B 1) := by
    rw [Finset.disjoint_left]
    intro y hy0 hy1
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy0).2).2
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy1).2).2
    omega
  let W := (N ∩ B 0) ∪ (N ∩ B 1)
  have hWsub : W ⊆ N := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy0 | hy1
    · exact (Finset.mem_inter.mp hy0).1
    · exact (Finset.mem_inter.mp hy1).1
  have hWcard : W.card = N.card := by
    rw [Finset.card_union_of_disjoint hbinDisj,
      G.card_neighborFinset_eq_degree]
    omega
  have hNW : N = W := by
    symm
    exact Finset.eq_of_subset_of_card_le hWsub (by omega)
  have hB0split : B 0 = S ∪ T := by
    ext y
    simp only [S, T, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro hy
      by_cases hyS : y ∈ G.neighborFinset x ∩ B 0
      · exact Or.inl (Finset.mem_inter.mp hyS)
      · exact Or.inr ⟨hy, fun hpair => hyS (Finset.mem_inter.mpr hpair)⟩
    · rintro (⟨_hyN, hyB⟩ | ⟨hyB, _hyNotS⟩)
      · exact hyB
      · exact hyB
  have hB1split : B 1 = M ∪ U1 := by
    ext y
    simp only [M, U1, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro hy
      by_cases hyM : y ∈ G.neighborFinset x ∩ B 1
      · exact Or.inl (Finset.mem_inter.mp hyM)
      · exact Or.inr ⟨hy, fun hpair => hyM (Finset.mem_inter.mpr hpair)⟩
    · rintro (⟨_hyN, hyB⟩ | ⟨hyB, _hyNotM⟩)
      · exact hyB
      · exact hyB
  change N = ((N ∩ S) ∪ (N ∩ T)) ∪ ((N ∩ M) ∪ (N ∩ U1))
  ext y
  constructor
  · intro hyN
    have hyW : y ∈ W := by rw [← hNW]; exact hyN
    rcases Finset.mem_union.mp hyW with hy0 | hy1
    · have hy0Parts := Finset.mem_inter.mp hy0
      have hySplit : y ∈ S ∪ T := by rw [← hB0split]; exact hy0Parts.2
      rcases Finset.mem_union.mp hySplit with hyS | hyT
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hy0Parts.1, hyS⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hy0Parts.1, hyT⟩))
    · have hy1Parts := Finset.mem_inter.mp hy1
      have hySplit : y ∈ M ∪ U1 := by rw [← hB1split]; exact hy1Parts.2
      rcases Finset.mem_union.mp hySplit with hyM | hyU
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hy1Parts.1, hyM⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hy1Parts.1, hyU⟩))
  · intro hy
    rcases Finset.mem_union.mp hy with hy0 | hy1
    · rcases Finset.mem_union.mp hy0 with hyS | hyT
      · exact (Finset.mem_inter.mp hyS).1
      · exact (Finset.mem_inter.mp hyT).1
    · rcases Finset.mem_union.mp hy1 with hyM | hyU
      · exact (Finset.mem_inter.mp hyM).1
      · exact (Finset.mem_inter.mp hyU).1

/-- Complete weighted expansion of an ordinary B0 row.  This is the exact
left-hand equation used by the residual finite-design model. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_equation
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    let mass := ∑ w ∈ G.neighborFinset t,
      (G.neighborFinset w ∩ U1).card
    mass = 2 * (R.filter fun w => w ∈ P).card +
      3 * (R.filter fun w => w ∉ P).card +
      3 * (G.neighborFinset t ∩ U1).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let N := G.neighborFinset t
  let NS := N ∩ S
  let R := N ∩ T
  let NM := N ∩ M
  let NU := N ∩ U1
  let f := fun w => (G.neighborFinset w ∩ U1).card
  let mass := ∑ w ∈ N, f w
  have hpart :=
    squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpart
  change N = (NS ∪ R) ∪ (NM ∪ NU) at hpart
  have hzero := squareOrderNine_threeHigh_secondProfile_ordinary_row_zero_centers
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hzero
  have hweights := squareOrderNine_threeHigh_secondProfile_row_center_weight_sums
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 (t := t) hx
  dsimp only at hweights
  change (∑ w ∈ R, f w) =
      2 * (R.filter fun w => w ∈ P).card +
        3 * (R.filter fun w => w ∉ P).card ∧
    (∑ w ∈ NU, f w) = 3 * NU.card at hweights
  have hST : Disjoint NS R := by
    rw [Finset.disjoint_left]
    intro w hwS hwT
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwT).2).2
      (Finset.mem_inter.mp hwS).2
  have hMU : Disjoint NM NU := by
    rw [Finset.disjoint_left]
    intro w hwM hwU
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwU).2).2
      (Finset.mem_inter.mp hwM).2
  have hcross : Disjoint (NS ∪ R) (NM ∪ NU) := by
    rw [Finset.disjoint_left]
    intro w hw0 hw1
    have hwB0 : w ∈ B 0 := by
      rcases Finset.mem_union.mp hw0 with hwS | hwT
      · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hwS).2).2
      · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwT).2).1
    have hwB1 : w ∈ B 1 := by
      rcases Finset.mem_union.mp hw1 with hwM | hwU
      · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hwM).2).2
      · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwU).2).1
    have hk0 := (Finset.mem_filter.mp hwB0).2
    have hk1 := (Finset.mem_filter.mp hwB1).2
    omega
  have hsumS : (∑ w ∈ NS, f w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    exact hzero.1 w (Finset.mem_inter.mp hw).2
  have hsumM : (∑ w ∈ NM, f w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    exact hzero.2.1 w (Finset.mem_inter.mp hw).2
  change (∑ w ∈ N, f w) = 2 * (R.filter fun w => w ∈ P).card +
    3 * (R.filter fun w => w ∉ P).card + 3 * NU.card
  rw [hpart, Finset.sum_union hcross, Finset.sum_union hST,
    Finset.sum_union hMU, hsumS, hsumM, hweights.1, hweights.2]
  omega

/-- Graph-facing weighted-row capstone.  The explicit `2/3/3` center count
equals the regular target `21 + |D(t) ∩ M|` or the exceptional target `24`. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_dichotomy
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
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    let D := secondOrderDefectGraph G
    let weight := 2 * (R.filter fun w => w ∈ P).card +
      3 * (R.filter fun w => w ∉ P).card +
      3 * (G.neighborFinset t ∩ U1).card
    weight = 21 + (D.neighborFinset t ∩ M).card ∨ weight = 24 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let R := G.neighborFinset t ∩ T
  let D := secondOrderDefectGraph G
  let mass := ∑ w ∈ G.neighborFinset t,
    (G.neighborFinset w ∩ U1).card
  let weight := 2 * (R.filter fun w => w ∈ P).card +
    3 * (R.filter fun w => w ∉ P).card +
    3 * (G.neighborFinset t ∩ U1).card
  have hweight :=
    squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_equation
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hweight
  change mass = weight at hweight
  have hmass :=
    squareOrderNine_threeHigh_secondProfile_binZero_row_mass_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
        (Finset.mem_sdiff.mp ht).1
  dsimp only at hmass
  change mass = 21 + (D.neighborFinset t ∩ M).card ∨ mass = 24 at hmass
  rcases hmass with hregular | hexceptional
  · exact Or.inl (hweight.symm.trans hregular)
  · exact Or.inr (hweight.symm.trans hexceptional)
end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_row_mass_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_row_center_weight_sums
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_row_zero_centers
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_equation
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_dichotomy
