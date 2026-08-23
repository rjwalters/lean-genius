import Proofs.Erdos85C4FreeCrossBlockOrthogonality
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

/-- Arithmetic terminal behind the ordinary weighted-row equation.  If the
two residual center counts partition a residual degree `r`, then the regular
combined-degree-eight target and exceptional combined-degree-nine target both
force `a + d = 3`. -/
theorem weighted_row_arithmetic_forces_pair_defect_three
    (a b c d r : ℕ)
    (hab : a + b = r)
    (hbranch :
      (r + c = 8 ∧ 2 * a + 3 * b + 3 * c = 21 + d) ∨
      (r + c = 9 ∧ 2 * a + 3 * b + 3 * c = 24 ∧ d = 0)) :
    a + d = 3 := by
  omega

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

/-- An ordinary B0 row has no special/marked center exactly on the exceptional
defect fiber of `x`; every other row has exactly one such center. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_special_marked_center_dichotomy
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
    let D := secondOrderDefectGraph G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    ((D.Adj x t ∧ (G.neighborFinset t ∩ S).card = 0 ∧
        (G.neighborFinset t ∩ M).card = 0) ∨
      (¬ D.Adj x t ∧ (G.neighborFinset t ∩ S).card +
        (G.neighborFinset t ∩ M).card = 1)) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let D := secondOrderDefectGraph G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let FS : V → Finset V := fun y => G.neighborFinset y ∩ B 0
  let W := (S.biUnion FS) ∪ (M.biUnion FS)
  let T := B 0 \ S
  let O := W \ S
  let C := (G.neighborFinset t ∩ S) ∪ (G.neighborFinset t ∩ M)
  have htParts := Finset.mem_sdiff.mp ht
  have htT : t ∈ T := Finset.mem_sdiff.mpr htParts
  have hholes :=
    squareOrderNine_threeHigh_secondProfile_support_holes_eq_defect_fiber
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hholes
  change T \ O = (D.neighborFinset x ∩ B 0) \ S at hholes
  have hOiff : t ∈ O ↔ C.Nonempty := by
    constructor
    · intro htO
      have htW := (Finset.mem_sdiff.mp htO).1
      rcases Finset.mem_union.mp htW with htWS | htWM
      · simp only [Finset.mem_biUnion] at htWS
        obtain ⟨s, hsS, hts⟩ := htWS
        refine ⟨s, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨?_, hsS⟩)⟩
        exact (G.mem_neighborFinset t s).mpr
          ((G.adj_comm s t).mp ((G.mem_neighborFinset s t).mp
            (Finset.mem_inter.mp hts).1))
      · simp only [Finset.mem_biUnion] at htWM
        obtain ⟨m, hmM, htm⟩ := htWM
        refine ⟨m, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨?_, hmM⟩)⟩
        exact (G.mem_neighborFinset t m).mpr
          ((G.adj_comm m t).mp ((G.mem_neighborFinset m t).mp
            (Finset.mem_inter.mp htm).1))
    · rintro ⟨y, hyC⟩
      refine Finset.mem_sdiff.mpr ⟨?_, htParts.2⟩
      rcases Finset.mem_union.mp hyC with hyS | hyM
      · have hyParts := Finset.mem_inter.mp hyS
        apply Finset.mem_union_left
        simp only [Finset.mem_biUnion]
        exact ⟨y, hyParts.2, Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset y t).mpr
            ((G.adj_comm t y).mp ((G.mem_neighborFinset t y).mp hyParts.1)),
          htParts.1⟩⟩
      · have hyParts := Finset.mem_inter.mp hyM
        apply Finset.mem_union_right
        simp only [Finset.mem_biUnion]
        exact ⟨y, hyParts.2, Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset y t).mpr
            ((G.adj_comm t y).mp ((G.mem_neighborFinset t y).mp hyParts.1)),
          htParts.1⟩⟩
  have hxt : x ≠ t := by
    intro h
    subst t
    have hk3 := (Finset.mem_filter.mp hx).2
    have hk0 := (Finset.mem_filter.mp htParts.1).2
    omega
  have hCsub : C ⊆ G.neighborFinset x ∩ G.neighborFinset t := by
    intro y hyC
    rcases Finset.mem_union.mp hyC with hyS | hyM
    · have hyParts := Finset.mem_inter.mp hyS
      have hySParts := Finset.mem_inter.mp hyParts.2
      exact Finset.mem_inter.mpr ⟨hySParts.1, hyParts.1⟩
    · have hyParts := Finset.mem_inter.mp hyM
      have hyMParts := Finset.mem_inter.mp hyParts.2
      exact Finset.mem_inter.mpr ⟨hyMParts.1, hyParts.1⟩
  have hCle : C.card ≤ 1 := by
    exact (Finset.card_le_card hCsub).trans
      ((not_containsC4_iff_forall_common_le_one G).mp hfree x t hxt)
  have hSMdisj : Disjoint (G.neighborFinset t ∩ S)
      (G.neighborFinset t ∩ M) := by
    rw [Finset.disjoint_left]
    intro y hyS hyM
    have hyB0 := (Finset.mem_inter.mp (Finset.mem_inter.mp hyS).2).2
    have hyB1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hyM).2).2
    have hk0 := (Finset.mem_filter.mp hyB0).2
    have hk1 := (Finset.mem_filter.mp hyB1).2
    omega
  by_cases hDxt : D.Adj x t
  · left
    have htQ : t ∈ (D.neighborFinset x ∩ B 0) \ S :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset x t).mpr hDxt, htParts.1⟩, htParts.2⟩
    have htHole : t ∈ T \ O := by rw [hholes]; exact htQ
    have htNotO := (Finset.mem_sdiff.mp htHole).2
    have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hC => htNotO (hOiff.mpr hC))
    have hcards := congrArg Finset.card hCempty
    rw [Finset.card_union_of_disjoint hSMdisj, Finset.card_empty] at hcards
    have hcards' : (G.neighborFinset t ∩ S).card +
        (G.neighborFinset t ∩ M).card = 0 := by
      simpa [C] using hcards
    have hz := Nat.add_eq_zero_iff.mp hcards'
    exact ⟨hDxt, by simpa [S] using hz.1, by simpa [M] using hz.2⟩
  · right
    have htO : t ∈ O := by
      by_contra htNotO
      have htHole : t ∈ T \ O := Finset.mem_sdiff.mpr ⟨htT, htNotO⟩
      have htQ : t ∈ (D.neighborFinset x ∩ B 0) \ S := by
        rw [← hholes]
        exact htHole
      exact hDxt ((D.mem_neighborFinset x t).mp
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp htQ).1).1)
    have hCpos : 0 < C.card := Finset.card_pos.mpr (hOiff.mp htO)
    have hCcard : C.card = 1 := by omega
    rw [Finset.card_union_of_disjoint hSMdisj] at hCcard
    exact ⟨hDxt, hCcard⟩

/-- Arithmetic-ready graph alignment for an ordinary row.  The regular
defect type has one special/marked center and hence residual/core degree
eight; the exceptional type has none and hence residual/core degree nine.
The weighted target is aligned with the same branch. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_aligned_weighted_row_branches
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
    (R.card + (G.neighborFinset t ∩ U1).card = 8 ∧
        weight = 21 + (D.neighborFinset t ∩ M).card) ∨
      (R.card + (G.neighborFinset t ∩ U1).card = 9 ∧
        weight = 24 ∧ (D.neighborFinset t ∩ M).card = 0) := by
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
  let D := secondOrderDefectGraph G
  let mass := ∑ w ∈ N, (G.neighborFinset w ∩ U1).card
  let weight := 2 * (R.filter fun w => w ∈ P).card +
    3 * (R.filter fun w => w ∉ P).card + 3 * NU.card
  have htB0 : t ∈ B 0 := (Finset.mem_sdiff.mp ht).1
  have hcent :=
    squareOrderNine_threeHigh_secondProfile_ordinary_special_marked_center_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hcent
  change (D.Adj x t ∧ NS.card = 0 ∧ NM.card = 0) ∨
    (¬ D.Adj x t ∧ NS.card + NM.card = 1) at hcent
  have htype :=
    squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc4 htB0
  dsimp only at htype
  have hB3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hregular_iff :
      ((D.neighborFinset t ∩ B 0).card = 5 ∧
        (D.neighborFinset t ∩ B 1).card = 3 ∧
        (D.neighborFinset t ∩ B 3).card = 0) ↔ ¬ D.Adj x t := by
    constructor
    · intro hreg hxt
      have hxInter : x ∈ D.neighborFinset t ∩ B 3 :=
        Finset.mem_inter.mpr ⟨(D.mem_neighborFinset t x).mpr
          ((D.adj_comm x t).mp hxt), hx⟩
      have : (D.neighborFinset t ∩ B 3).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨x, hxInter⟩
      exact this hreg.2.2
    · intro hnxt
      rcases htype with hreg | hexc
      · exact hreg
      · exfalso
        have hinter : D.neighborFinset t ∩ B 3 = B 3 := by
          apply Finset.eq_of_subset_of_card_le
          · exact Finset.inter_subset_right
          · rw [hexc.2.2, hB3card]
        have hxDt : x ∈ D.neighborFinset t := by
          have : x ∈ D.neighborFinset t ∩ B 3 := by rw [hinter]; exact hx
          exact (Finset.mem_inter.mp this).1
        exact hnxt ((D.adj_comm t x).mp ((D.mem_neighborFinset t x).mp hxDt))
  have hpart :=
    squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpart
  change N = (NS ∪ R) ∪ (NM ∪ NU) at hpart
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
  have hNcards := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hcross,
    Finset.card_union_of_disjoint hST,
    Finset.card_union_of_disjoint hMU] at hNcards
  have htdeg : G.degree t = 9 := by
    have htL := (Finset.mem_filter.mp htB0).1
    have htNotHigh : t ∉ squareOrderHighVertices G 9 :=
      (Finset.mem_sdiff.mp htL).2
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard t with hlo | hhi
    · exact hlo
    · exact (htNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  rw [G.card_neighborFinset_eq_degree, htdeg] at hNcards
  have hweight :=
    squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_equation
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hweight
  change mass = weight at hweight
  have hrow :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx htB0
  dsimp only at hrow
  change mass = 24 - (D.neighborFinset t ∩ U1).card at hrow
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hDpartition : D.neighborFinset t ∩ B 1 =
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
  have hDdisj : Disjoint (D.neighborFinset t ∩ U1)
      (D.neighborFinset t ∩ M) := by
    rw [Finset.disjoint_left]
    intro y hyU hyM
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hyU).2).2
      (Finset.mem_inter.mp hyM).2
  have hDcards := congrArg Finset.card hDpartition
  rw [Finset.card_union_of_disjoint hDdisj] at hDcards
  rcases hcent with hzero | hone
  · right
    have hexc : (D.neighborFinset t ∩ B 0).card = 7 ∧
        (D.neighborFinset t ∩ B 1).card = 0 ∧
        (D.neighborFinset t ∩ B 3).card = 1 := by
      rcases htype with hreg | hexc
      · exact (hregular_iff.mp hreg hzero.1).elim
      · exact hexc
    rw [hexc.2.1] at hDcards
    change R.card + NU.card = 9 ∧ weight = 24 ∧
      (D.neighborFinset t ∩ M).card = 0
    constructor
    · omega
    constructor
    · rw [← hweight, hrow]
      omega
    · omega
  · left
    have hreg := hregular_iff.mpr hone.1
    rw [hreg.2.1] at hDcards
    change R.card + NU.card = 8 ∧
      weight = 21 + (D.neighborFinset t ∩ M).card
    constructor
    · omega
    · rw [← hweight, hrow]
      omega

/-- Every ordinary B0 row either meets or is defect-adjacent to exactly three
of the marked support groups, counted at the aggregate level. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_pair_defect_three
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
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    let D := secondOrderDefectGraph G
    (R.filter fun w => w ∈ P).card +
      (D.neighborFinset t ∩ M).card = 3 := by
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
  let a := (R.filter fun w => w ∈ P).card
  let b := (R.filter fun w => w ∉ P).card
  let c := (G.neighborFinset t ∩ U1).card
  let d := (D.neighborFinset t ∩ M).card
  let r := R.card
  have hab : a + b = r := by
    exact Finset.card_filter_add_card_filter_not
      (s := R) (fun w => w ∈ P)
  have halign :=
    squareOrderNine_threeHigh_secondProfile_ordinary_aligned_weighted_row_branches
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at halign
  change (r + c = 8 ∧ 2 * a + 3 * b + 3 * c = 21 + d) ∨
    (r + c = 9 ∧ 2 * a + 3 * b + 3 * c = 24 ∧ d = 0) at halign
  exact weighted_row_arithmetic_forces_pair_defect_three a b c d r hab halign

/-- Graph-to-pattern bridge for reciprocity pruning.  The marked-support
neighbor pattern of every ordinary row is loopless, has size complementary
to its marked defect degree, and uses at most one point from each marked
seven-point support. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_pair_pattern
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
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let C := (G.neighborFinset t ∩ T).filter fun w => w ∈ P
    let D := secondOrderDefectGraph G
    C.card + (D.neighborFinset t ∩ M).card = 3 ∧
      t ∉ C ∧
      ∀ m ∈ M,
        (C.filter fun w => w ∈ G.neighborFinset m ∩ B 0).card ≤ 1 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let C := (G.neighborFinset t ∩ T).filter fun w => w ∈ P
  let D := secondOrderDefectGraph G
  have hsize :=
    squareOrderNine_threeHigh_secondProfile_ordinary_pair_defect_three
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hsize
  change C.card + (D.neighborFinset t ∩ M).card = 3 at hsize
  refine ⟨hsize, ?_, ?_⟩
  · intro htt
    have htN := (Finset.mem_inter.mp (Finset.mem_filter.mp htt).1).1
    exact G.loopless.irrefl t ((G.mem_neighborFinset t t).mp htN)
  · intro m hm
    have htm : t ≠ m := by
      intro h
      subst m
      have htB0 := (Finset.mem_sdiff.mp ht).1
      have hmB1 := (Finset.mem_inter.mp hm).2
      have hk0 := (Finset.mem_filter.mp htB0).2
      have hk1 := (Finset.mem_filter.mp hmB1).2
      omega
    apply (Finset.card_le_card ?_).trans
      ((not_containsC4_iff_forall_common_le_one G).mp hfree t m htm)
    intro w hw
    have hwParts := Finset.mem_filter.mp hw
    have hwC := Finset.mem_filter.mp hwParts.1
    have hwF := Finset.mem_inter.mp hwParts.2
    exact Finset.mem_inter.mpr ⟨
      (Finset.mem_inter.mp hwC.1).1,
      hwF.1⟩

/-- A pair-center row is necessarily in the regular row-cover branch.  It has
six residual neighbors, split into `3 - d` pair centers and `3 + d` triple
centers, where `d` is its marked defect degree.  The second equality is the
missing cardinality component of the graph-to-allowed-family bridge. -/
theorem squareOrderNine_threeHigh_secondProfile_pair_row_triple_completion_count
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
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (htP : t ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1).biUnion
      fun m => G.neighborFinset m ∩ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    let Q := R.filter fun w => w ∉ P
    let D := secondOrderDefectGraph G
    R.card = 6 ∧ Q.card = 3 + (D.neighborFinset t ∩ M).card := by
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
  let C := R.filter fun w => w ∈ P
  let Q := R.filter fun w => w ∉ P
  let D := secondOrderDefectGraph G
  have htB0 : t ∈ B 0 := (Finset.mem_sdiff.mp ht).1
  have hNMnonempty : NM.Nonempty := by
    simp only [Finset.mem_biUnion] at htP
    obtain ⟨m, hmM, htm⟩ := htP
    refine ⟨m, Finset.mem_inter.mpr ⟨?_, hmM⟩⟩
    exact (G.mem_neighborFinset t m).mpr
      ((G.adj_comm m t).mp ((G.mem_neighborFinset m t).mp
        (Finset.mem_inter.mp htm).1))
  have hcent :=
    squareOrderNine_threeHigh_secondProfile_ordinary_special_marked_center_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hcent
  change (D.Adj x t ∧ NS.card = 0 ∧ NM.card = 0) ∨
    (¬ D.Adj x t ∧ NS.card + NM.card = 1) at hcent
  have hspecial : NS.card + NM.card = 1 := by
    rcases hcent with hzero | hone
    · exact (Finset.card_ne_zero.mpr hNMnonempty hzero.2.2).elim
    · exact hone.2
  have hpart :=
    squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpart
  change N = (NS ∪ R) ∪ (NM ∪ NU) at hpart
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
  have hNcards := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hcross,
    Finset.card_union_of_disjoint hST,
    Finset.card_union_of_disjoint hMU] at hNcards
  have htdeg : G.degree t = 9 := by
    have htL := (Finset.mem_filter.mp htB0).1
    have htNotHigh : t ∉ squareOrderHighVertices G 9 :=
      (Finset.mem_sdiff.mp htL).2
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard t with hlo | hhi
    · exact hlo
    · exact (htNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  rw [G.card_neighborFinset_eq_degree, htdeg] at hNcards
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hNU : NU.card = 2 := hcensus.2.2.1 t htP
  have hR : R.card = 6 := by omega
  have hpair :=
    squareOrderNine_threeHigh_secondProfile_ordinary_pair_defect_three
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpair
  change C.card + (D.neighborFinset t ∩ M).card = 3 at hpair
  have hCQ : C.card + Q.card = R.card := by
    exact Finset.card_filter_add_card_filter_not
      (s := R) (fun w => w ∈ P)
  refine ⟨hR, ?_⟩
  apply Nat.add_left_cancel (n := C.card)
  calc
    C.card + Q.card = R.card := hCQ
    _ = 6 := hR
    _ = 3 + 3 := by norm_num
    _ = 3 + (C.card + (D.neighborFinset t ∩ M).card) := by rw [hpair]
    _ = C.card + (3 + (D.neighborFinset t ∩ M).card) := by omega

/-- The exact local admissibility predicate used by the reduced q=9
reciprocity model.  A proposed pair-center pattern `C` must admit the required
number of triple-center completion rows; all six completed residual blocks
are pairwise disjoint and avoid the original core block of the row. -/
def squareOrderNinePairRowAdmissible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (x t : V) (C : Finset V) : Prop :=
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let D := secondOrderDefectGraph G
  C ⊆ P ∧ t ∉ C ∧
    C.card + (D.neighborFinset t ∩ M).card = 3 ∧
    (∀ m ∈ M,
      (C.filter fun w => w ∈ G.neighborFinset m ∩ B 0).card ≤ 1) ∧
    ∃ Q : Finset V,
      Q ⊆ T \ P ∧
      Q.card = 3 + (D.neighborFinset t ∩ M).card ∧
      (∀ u ∈ C ∪ Q, ∀ v ∈ C ∪ Q, u ≠ v →
        Disjoint (G.neighborFinset u ∩ U1) (G.neighborFinset v ∩ U1)) ∧
      (∀ u ∈ C ∪ Q, ∀ c ∈ G.neighborFinset t ∩ U1,
        ∀ b ∈ G.neighborFinset u ∩ U1, ¬ G.Adj c b)

/-- The finite family of locally admissible pair-center patterns at a row. -/
def squareOrderNinePairRowAllowedPatterns
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (x t : V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun C => squareOrderNinePairRowAdmissible G x t C

/-- The actual marked-support neighbor patterns are reciprocal on the
21-point pair-center set, because they are restrictions of an undirected
residual adjacency relation. -/
theorem squareOrderNine_pair_pattern_mem_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x t u : V}
    (ht : t ∈ squareOrderNineLowIncidenceBin G 0 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hu : u ∈ squareOrderNineLowIncidenceBin G 0 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (htP : t ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1).biUnion
      fun m => G.neighborFinset m ∩ squareOrderNineLowIncidenceBin G 0)
    (huP : u ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1).biUnion
      fun m => G.neighborFinset m ∩ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let C := fun v => (G.neighborFinset v ∩ T).filter fun w => w ∈ P
    u ∈ C t ↔ t ∈ C u := by
  classical
  dsimp only
  constructor
  · intro hut
    have huAdj := (G.mem_neighborFinset t u).mp
      (Finset.mem_inter.mp (Finset.mem_filter.mp hut).1).1
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u t).mpr
        ((G.adj_comm t u).mp huAdj), ht⟩, htP⟩
  · intro htu
    have htAdj := (G.mem_neighborFinset u t).mp
      (Finset.mem_inter.mp (Finset.mem_filter.mp htu).1).1
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset t u).mpr
        ((G.adj_comm u t).mp htAdj), hu⟩, huP⟩

/-- Pointwise B0 Gram law.  Distinct residual neighbors of one ordinary row
have disjoint incidence blocks in the unmarked B1 core. -/
theorem squareOrderNine_threeHigh_secondProfile_residual_neighbor_blocks_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x t u v : V}
    (ht : t ∈ squareOrderNineLowIncidenceBin G 0 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hu : u ∈ G.neighborFinset t ∩
      (squareOrderNineLowIncidenceBin G 0 \
        (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)))
    (hv : v ∈ G.neighborFinset t ∩
      (squareOrderNineLowIncidenceBin G 0 \
        (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)))
    (huv : u ≠ v) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    Disjoint (G.neighborFinset u ∩ U1) (G.neighborFinset v ∩ U1) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  rw [Finset.disjoint_left]
  intro b hbu hbv
  have hbU := (Finset.mem_inter.mp hbu).2
  have htB0 := (Finset.mem_sdiff.mp ht).1
  have hbB1 := (Finset.mem_sdiff.mp hbU).1
  have htb : t ≠ b := by
    intro h
    subst b
    have hk0 := (Finset.mem_filter.mp htB0).2
    have hk1 := (Finset.mem_filter.mp hbB1).2
    omega
  have htCommon : t ∈ G.neighborFinset u ∩ G.neighborFinset v := by
    have htu := (G.mem_neighborFinset t u).mp (Finset.mem_inter.mp hu).1
    have htv := (G.mem_neighborFinset t v).mp (Finset.mem_inter.mp hv).1
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset u t).mpr ((G.adj_comm t u).mp htu),
      (G.mem_neighborFinset v t).mpr ((G.adj_comm t v).mp htv)⟩
  have hbCommon : b ∈ G.neighborFinset u ∩ G.neighborFinset v :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbu).1,
      (Finset.mem_inter.mp hbv).1⟩
  have hpairSub : ({t, b} : Finset V) ⊆
      G.neighborFinset u ∩ G.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact htCommon
    · exact hbCommon
  have hpairCard : ({t, b} : Finset V).card = 2 := by simp [htb]
  have hcommonLe :=
    (not_containsC4_iff_forall_common_le_one G).mp hfree u v huv
  have := Finset.card_le_card hpairSub
  omega

/-- Pointwise mixed Gram law.  If `u` is a residual neighbor of `t`, no
original U1-core edge can join an incidence point of `t` to an incidence
point of `u`. -/
theorem squareOrderNine_threeHigh_secondProfile_residual_block_avoids_core
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x t u c b : V}
    (ht : t ∈ squareOrderNineLowIncidenceBin G 0 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hu : u ∈ G.neighborFinset t ∩
      (squareOrderNineLowIncidenceBin G 0 \
        (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)))
    (hc : c ∈ G.neighborFinset t ∩
      (squareOrderNineLowIncidenceBin G 1 \
        (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)))
    (hb : b ∈ G.neighborFinset u ∩
      (squareOrderNineLowIncidenceBin G 1 \
        (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1))) :
    ¬ G.Adj c b := by
  intro hcb
  have htB0 := (Finset.mem_sdiff.mp ht).1
  have hbB1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).2).1
  have htb : t ≠ b := by
    intro h
    subst b
    have hk0 := (Finset.mem_filter.mp htB0).2
    have hk1 := (Finset.mem_filter.mp hbB1).2
    omega
  have huB0 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).1
  have hcB1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).2).1
  have huc : u ≠ c := by
    intro h
    subst c
    have hk0 := (Finset.mem_filter.mp huB0).2
    have hk1 := (Finset.mem_filter.mp hcB1).2
    omega
  have huCommon : u ∈ G.neighborFinset t ∩ G.neighborFinset b := by
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hu).1,
      (G.mem_neighborFinset b u).mpr ((G.adj_comm u b).mp
        ((G.mem_neighborFinset u b).mp (Finset.mem_inter.mp hb).1))⟩
  have hcCommon : c ∈ G.neighborFinset t ∩ G.neighborFinset b := by
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hc).1,
      (G.mem_neighborFinset b c).mpr ((G.adj_comm c b).mp hcb)⟩
  have hpairSub : ({u, c} : Finset V) ⊆
      G.neighborFinset t ∩ G.neighborFinset b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact huCommon
    · exact hcCommon
  have hpairCard : ({u, c} : Finset V).card = 2 := by simp [huc]
  have hcommonLe :=
    (not_containsC4_iff_forall_common_le_one G).mp hfree t b htb
  have := Finset.card_le_card hpairSub
  omega

/-- Every actual pair-row neighbor pattern belongs to the finite admissible
family.  This packages all graph-side hypotheses needed by the reduced
reciprocity-pruning obstruction into one membership statement. -/
theorem squareOrderNine_threeHigh_secondProfile_actual_pair_pattern_mem_allowed
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
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (htP : t ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1).biUnion
      fun m => G.neighborFinset m ∩ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let C := (G.neighborFinset t ∩ T).filter fun w => w ∈ P
    C ∈ squareOrderNinePairRowAllowedPatterns G x t := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let R := G.neighborFinset t ∩ T
  let C := R.filter fun w => w ∈ P
  let Q := R.filter fun w => w ∉ P
  let D := secondOrderDefectGraph G
  rw [squareOrderNinePairRowAllowedPatterns, Finset.mem_filter]
  refine ⟨Finset.mem_univ C, ?_⟩
  dsimp only [squareOrderNinePairRowAdmissible]
  have hpattern :=
    squareOrderNine_threeHigh_secondProfile_ordinary_pair_pattern
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpattern
  change C.card + (D.neighborFinset t ∩ M).card = 3 ∧ t ∉ C ∧
    ∀ m ∈ M,
      (C.filter fun w => w ∈ G.neighborFinset m ∩ B 0).card ≤ 1 at hpattern
  have hcompletion :=
    squareOrderNine_threeHigh_secondProfile_pair_row_triple_completion_count
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht htP
  dsimp only at hcompletion
  change R.card = 6 ∧ Q.card = 3 + (D.neighborFinset t ∩ M).card at hcompletion
  have hCsub : C ⊆ P := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  have hQsub : Q ⊆ T \ P := by
    intro u hu
    have huParts := Finset.mem_filter.mp hu
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp huParts.1).2, huParts.2⟩
  refine ⟨hCsub, hpattern.2.1, hpattern.1, hpattern.2.2,
    Q, hQsub, hcompletion.2, ?_, ?_⟩
  · intro u hu v hv huv
    have huR : u ∈ R := by
      rcases Finset.mem_union.mp hu with huC | huQ
      · exact (Finset.mem_filter.mp huC).1
      · exact (Finset.mem_filter.mp huQ).1
    have hvR : v ∈ R := by
      rcases Finset.mem_union.mp hv with hvC | hvQ
      · exact (Finset.mem_filter.mp hvC).1
      · exact (Finset.mem_filter.mp hvQ).1
    exact squareOrderNine_threeHigh_secondProfile_residual_neighbor_blocks_disjoint
      G hfree ht huR hvR huv
  · intro u hu c hc b hb
    have huR : u ∈ R := by
      rcases Finset.mem_union.mp hu with huC | huQ
      · exact (Finset.mem_filter.mp huC).1
      · exact (Finset.mem_filter.mp huQ).1
    exact squareOrderNine_threeHigh_secondProfile_residual_block_avoids_core
      G hfree ht huR hc hb

/-- Reciprocity has an immediate global parity consequence: the total marked
defect degree on the 21 pair-center rows is odd.  Indeed their pair-center
degrees are `3 - d`, and the induced pair graph has even degree sum. -/
theorem squareOrderNine_threeHigh_secondProfile_pair_marked_defect_sum_odd
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let D := secondOrderDefectGraph G
    Odd (∑ t ∈ P, (D.neighborFinset t ∩ M).card) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let D := secondOrderDefectGraph G
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hPcard : P.card = 21 := hcensus.1
  have hPsub : P ⊆ T := by
    intro y hyP
    simp only [P, Finset.mem_biUnion] at hyP
    obtain ⟨m, hmM, hym⟩ := hyP
    have hmParts := Finset.mem_inter.mp hmM
    have hymParts := Finset.mem_inter.mp hym
    refine Finset.mem_sdiff.mpr ⟨hymParts.2, ?_⟩
    intro hyS
    have hySParts := Finset.mem_inter.mp hyS
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hySParts.1
    have hymAdj : G.Adj y m := (G.adj_comm m y).mp
      ((G.mem_neighborFinset m y).mp hymParts.1)
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hySParts.2 hmParts.2 hxy) hymAdj
  let H := G.induce (↑P : Set V)
  have hdegree (t : ↑(↑P : Set V)) :
      H.degree t = (G.neighborFinset t.1 ∩ P).card := by
    exact degree_induce_finset_eq_card_inter G P t
  have hevenSubtype : Even (∑ t : ↑(↑P : Set V),
      (G.neighborFinset t.1 ∩ P).card) := by
    refine ⟨H.edgeFinset.card, ?_⟩
    calc
      (∑ t : ↑(↑P : Set V), (G.neighborFinset t.1 ∩ P).card) =
          ∑ t : ↑(↑P : Set V), H.degree t := by
            apply Finset.sum_congr rfl
            intro t _ht
            exact (hdegree t).symm
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
      _ = H.edgeFinset.card + H.edgeFinset.card := by omega
  have hevenPairDegree : Even
      (∑ t ∈ P, (G.neighborFinset t ∩ P).card) := by
    have hatt := Finset.sum_attach P
      (fun t => (G.neighborFinset t ∩ P).card)
    rw [← hatt]
    simpa using hevenSubtype
  have hpoint : ∀ t ∈ P,
      (G.neighborFinset t ∩ P).card +
        (D.neighborFinset t ∩ M).card = 3 := by
    intro t htP
    have htT := hPsub htP
    have hpair :=
      squareOrderNine_threeHigh_secondProfile_ordinary_pair_defect_three
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx htT
    dsimp only at hpair
    have hfilter :
        (G.neighborFinset t ∩ P) =
          (G.neighborFinset t ∩ T).filter fun w => w ∈ P := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · intro hw
        exact ⟨⟨hw.1, hPsub hw.2⟩, hw.2⟩
      · intro hw
        exact ⟨hw.1.1, hw.2⟩
    rw [hfilter]
    exact hpair
  have htotal :
      (∑ t ∈ P, (G.neighborFinset t ∩ P).card) +
        (∑ t ∈ P, (D.neighborFinset t ∩ M).card) = 63 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ t ∈ P, ((G.neighborFinset t ∩ P).card +
          (D.neighborFinset t ∩ M).card)) = ∑ _t ∈ P, 3 := by
            apply Finset.sum_congr rfl
            intro t htP
            exact hpoint t htP
      _ = 63 := by simp [hPcard]
  rw [← Nat.not_even_iff_odd]
  intro hevenDefect
  obtain ⟨a, ha⟩ := hevenPairDegree
  obtain ⟨b, hb⟩ := hevenDefect
  rw [ha, hb] at htotal
  omega

/-- Since the three marked supports have five holes each, the total marked
defect mass on all 47 ordinary rows is 15.  The odd pair-row contribution
therefore leaves an even contribution on the 26 triple-center rows. -/
theorem squareOrderNine_threeHigh_secondProfile_triple_marked_defect_sum_even
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let D := secondOrderDefectGraph G
    Even (∑ t ∈ T \ P, (D.neighborFinset t ∩ M).card) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let D := secondOrderDefectGraph G
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have hPsub : P ⊆ T := by
    intro y hyP
    simp only [P, Finset.mem_biUnion] at hyP
    obtain ⟨m, hmM, hym⟩ := hyP
    have hmParts := Finset.mem_inter.mp hmM
    have hymParts := Finset.mem_inter.mp hym
    refine Finset.mem_sdiff.mpr ⟨hymParts.2, ?_⟩
    intro hyS
    have hySParts := Finset.mem_inter.mp hyS
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hySParts.1
    have hymAdj : G.Adj y m := (G.adj_comm m y).mp
      ((G.mem_neighborFinset m y).mp hymParts.1)
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hySParts.2 hmParts.2 hxy) hymAdj
  have hMcard : M.card = 3 :=
    (squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx).2
  have htotal :
      (∑ t ∈ T, (D.neighborFinset t ∩ M).card) = 15 := by
    rw [sum_card_neighborFinset_inter_comm D T M]
    calc
      (∑ m ∈ M, (D.neighborFinset m ∩ T).card) = ∑ _m ∈ M, 5 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmParts := Finset.mem_inter.mp hm
        have hmtype :=
          squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
            G hfree hmin hcover hcard hp hhigh hc2 hc4 hmParts.2
        dsimp only at hmtype
        have heq : D.neighborFinset m ∩ T = D.neighborFinset m ∩ B 0 := by
          ext t
          simp only [Finset.mem_inter]
          constructor
          · intro ht
            exact ⟨ht.1, (Finset.mem_sdiff.mp ht.2).1⟩
          · intro ht
            refine ⟨ht.1, Finset.mem_sdiff.mpr ⟨ht.2, ?_⟩⟩
            intro htS
            have htSParts := Finset.mem_inter.mp htS
            have hmt : m ≠ t := by
              intro h
              subst t
              have hk1 := (Finset.mem_filter.mp hmParts.2).2
              have hk0 := (Finset.mem_filter.mp ht.2).2
              omega
            exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hmt
              ((G.adj_comm x m).mp ((G.mem_neighborFinset x m).mp hmParts.1))
              ((G.adj_comm x t).mp ((G.mem_neighborFinset x t).mp htSParts.1)))
                ((D.mem_neighborFinset m t).mp ht.1)
        rw [heq]
        exact hmtype.1
      _ = 15 := by simp [hMcard]
  have hsplit :
      (∑ t ∈ P, (D.neighborFinset t ∩ M).card) +
        (∑ t ∈ T \ P, (D.neighborFinset t ∩ M).card) = 15 := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hPsub]
    exact htotal
  have hpairOdd :=
    squareOrderNine_threeHigh_secondProfile_pair_marked_defect_sum_odd
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpairOdd
  rcases Nat.even_or_odd
      (∑ t ∈ T \ P, (D.neighborFinset t ∩ M).card) with heven | hodd
  · exact heven
  · obtain ⟨a, ha⟩ := hpairOdd
    obtain ⟨b, hb⟩ := hodd
    rw [ha, hb] at hsplit
    omega

/-- For an ordinary row and a marked root, all common neighbors lie in that
root's seven-point B0 support, and necessarily in the residual set `T`. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_marked_common_eq_support_hit
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
    {x t m : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hm : m ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let F := G.neighborFinset m ∩ B 0
    G.neighborFinset t ∩ G.neighborFinset m =
      (G.neighborFinset t ∩ T).filter fun w => w ∈ F := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := G.neighborFinset m ∩ B 0
  have hmParts := Finset.mem_inter.mp hm
  have hmx : G.Adj m x := (G.adj_comm x m).mp
    ((G.mem_neighborFinset x m).mp hmParts.1)
  have hmdeg :=
    squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hmParts.2
  dsimp only at hmdeg
  have hmB1zero : G.neighborFinset m ∩ B 1 = ∅ := by
    rw [← Finset.card_eq_zero]
    simpa [hmx] using hmdeg.1
  have hpart :=
    squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpart
  change G.neighborFinset t =
    ((G.neighborFinset t ∩ S) ∪ (G.neighborFinset t ∩ T)) ∪
      ((G.neighborFinset t ∩ M) ∪ (G.neighborFinset t ∩ U1)) at hpart
  ext w
  constructor
  · intro hw
    have hwParts := Finset.mem_inter.mp hw
    have hwtParts : w ∈
        ((G.neighborFinset t ∩ S) ∪ (G.neighborFinset t ∩ T)) ∪
          ((G.neighborFinset t ∩ M) ∪ (G.neighborFinset t ∩ U1)) := by
      rw [← hpart]
      exact hwParts.1
    rcases Finset.mem_union.mp hwtParts with hw0 | hw1
    · rcases Finset.mem_union.mp hw0 with hwS | hwT
      · have hwSParts := Finset.mem_inter.mp hwS
        have hsParts := Finset.mem_inter.mp hwSParts.2
        have hxm : G.Adj x m := (G.mem_neighborFinset x m).mp hmParts.1
        have hforbid :=
          squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
            G hfree hhigh hx hsParts.2 hmParts.2
              ((G.mem_neighborFinset x w).mp hsParts.1)
        exact (hforbid ((G.adj_comm m w).mp
          ((G.mem_neighborFinset m w).mp hwParts.2))).elim
      · have hwTParts := Finset.mem_inter.mp hwT
        exact Finset.mem_filter.mpr ⟨hwT,
          Finset.mem_inter.mpr ⟨hwParts.2,
            (Finset.mem_sdiff.mp hwTParts.2).1⟩⟩
    · rcases Finset.mem_union.mp hw1 with hwM | hwU
      · have hwB1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hwM).2).2
        have : w ∈ G.neighborFinset m ∩ B 1 :=
          Finset.mem_inter.mpr ⟨hwParts.2, hwB1⟩
        simpa [hmB1zero] using this
      · have hwB1 := (Finset.mem_sdiff.mp
          (Finset.mem_inter.mp hwU).2).1
        have : w ∈ G.neighborFinset m ∩ B 1 :=
          Finset.mem_inter.mpr ⟨hwParts.2, hwB1⟩
        simpa [hmB1zero] using this
  · intro hw
    have hwFilter := Finset.mem_filter.mp hw
    have hwR := Finset.mem_inter.mp hwFilter.1
    have hwF := Finset.mem_inter.mp hwFilter.2
    exact Finset.mem_inter.mpr ⟨hwR.1, hwF.1⟩

/-- Each of the three marked supports is a partial transversal of the
ordinary rows: a row hits the support exactly once, or misses it and is
defect-adjacent to its marked root. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_marked_support_hit_or_defect
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
    {x t m : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hm : m ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let F := G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    let D := secondOrderDefectGraph G
    ((R.filter fun w => w ∈ F).card = 1 ∧ ¬ D.Adj t m) ∨
      ((R.filter fun w => w ∈ F).card = 0 ∧ D.Adj t m) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let F := G.neighborFinset m ∩ B 0
  let R := G.neighborFinset t ∩ T
  let D := secondOrderDefectGraph G
  have htm : t ≠ m := by
    intro h
    subst m
    have htB0 := (Finset.mem_sdiff.mp ht).1
    have hk0 := (Finset.mem_filter.mp htB0).2
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hm).2).2
    omega
  have hcommon :=
    squareOrderNine_threeHigh_secondProfile_ordinary_marked_common_eq_support_hit
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht hm
  dsimp only at hcommon
  change G.neighborFinset t ∩ G.neighborFinset m = R.filter fun w => w ∈ F
    at hcommon
  have hle : (R.filter fun w => w ∈ F).card ≤ 1 := by
    rw [← hcommon]
    exact (not_containsC4_iff_forall_common_le_one G).mp hfree t m htm
  have hDzero : D.Adj t m ↔ (R.filter fun w => w ∈ F).card = 0 := by
    rw [← hcommon]
    exact secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree htm
  by_cases hD : D.Adj t m
  · right
    exact ⟨hDzero.mp hD, hD⟩
  · left
    have hne : (R.filter fun w => w ∈ F).card ≠ 0 := by
      intro hz
      exact hD (hDzero.mpr hz)
    have hone : (R.filter fun w => w ∈ F).card = 1 := by omega
    exact ⟨hone, hD⟩

/-- Inside each marked seven-point support, the defect holes have odd
cardinality.  The induced original graph is a matching on the nondefect
vertices: internal degree is one exactly off the defect fiber and zero on it.
-/
theorem squareOrderNine_threeHigh_secondProfile_marked_support_internal_defects_odd
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
    {x m : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hm : m ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let F := G.neighborFinset m ∩ B 0
    let D := secondOrderDefectGraph G
    Odd (F.filter fun t => D.Adj t m).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let F := G.neighborFinset m ∩ B 0
  let D := secondOrderDefectGraph G
  let Z := F.filter fun t => D.Adj t m
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_marked_binOne_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpack
  have hFcard : F.card = 7 := hpack.2.1 m hm
  have hFsub : F ⊆ T := by
    intro t htF
    have hmParts := Finset.mem_inter.mp hm
    have htParts := Finset.mem_inter.mp htF
    refine Finset.mem_sdiff.mpr ⟨htParts.2, ?_⟩
    intro htS
    have htSParts := Finset.mem_inter.mp htS
    have hxt : G.Adj x t := (G.mem_neighborFinset x t).mp htSParts.1
    have htm : G.Adj t m := (G.adj_comm m t).mp
      ((G.mem_neighborFinset m t).mp htParts.1)
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx htSParts.2 hmParts.2 hxt) htm
  let H := G.induce (↑F : Set V)
  have hdegree (t : ↑(↑F : Set V)) :
      H.degree t = (G.neighborFinset t.1 ∩ F).card := by
    exact degree_induce_finset_eq_card_inter G F t
  have hevenSubtype : Even (∑ t : ↑(↑F : Set V),
      (G.neighborFinset t.1 ∩ F).card) := by
    refine ⟨H.edgeFinset.card, ?_⟩
    calc
      (∑ t : ↑(↑F : Set V), (G.neighborFinset t.1 ∩ F).card) =
          ∑ t : ↑(↑F : Set V), H.degree t := by
            apply Finset.sum_congr rfl
            intro t _ht
            exact (hdegree t).symm
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
      _ = H.edgeFinset.card + H.edgeFinset.card := by omega
  have hevenDegree : Even
      (∑ t ∈ F, (G.neighborFinset t ∩ F).card) := by
    have hatt := Finset.sum_attach F
      (fun t => (G.neighborFinset t ∩ F).card)
    rw [← hatt]
    simpa using hevenSubtype
  have hlocal : ∀ t ∈ F,
      (G.neighborFinset t ∩ F).card = if D.Adj t m then 0 else 1 := by
    intro t htF
    have hhit :=
      squareOrderNine_threeHigh_secondProfile_ordinary_marked_support_hit_or_defect
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx (hFsub htF) hm
    dsimp only at hhit
    have heq : G.neighborFinset t ∩ F =
        (G.neighborFinset t ∩ T).filter fun w => w ∈ F := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · intro hw
        exact ⟨⟨hw.1, hFsub hw.2⟩, hw.2⟩
      · intro hw
        exact ⟨hw.1.1, hw.2⟩
    rw [heq]
    rcases hhit with hnondef | hdef
    · rw [if_neg hnondef.2]
      exact hnondef.1
    · rw [if_pos hdef.2]
      exact hdef.1
  have hdegSum :
      (∑ t ∈ F, (G.neighborFinset t ∩ F).card) = (F \ Z).card := by
    calc
      (∑ t ∈ F, (G.neighborFinset t ∩ F).card) =
          ∑ t ∈ F, if D.Adj t m then 0 else 1 := by
            apply Finset.sum_congr rfl
            intro t htF
            exact hlocal t htF
      _ = ∑ t ∈ F, if ¬ D.Adj t m then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro t _htF
            by_cases hD : D.Adj t m <;> simp [hD]
      _ = (F.filter fun t => ¬ D.Adj t m).card := by
            simpa using (Finset.sum_boole (R := ℕ)
              (fun t : V => ¬ D.Adj t m) F)
      _ = (F \ Z).card := by
            congr 1
            ext t
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · intro ht
              exact ⟨ht.1, fun htZ => ht.2 (Finset.mem_filter.mp htZ).2⟩
            · intro ht
              refine ⟨ht.1, ?_⟩
              intro hD
              exact ht.2 (Finset.mem_filter.mpr ⟨ht.1, hD⟩)
  rw [hdegSum] at hevenDegree
  have hZsub : Z ⊆ F := Finset.filter_subset _ _
  have hsplit : (F \ Z).card + Z.card = 7 := by
    have hZle : Z.card ≤ F.card := Finset.card_le_card hZsub
    rw [Finset.card_sdiff_of_subset hZsub, hFcard]
    omega
  rw [← Nat.not_even_iff_odd]
  intro hevenZ
  obtain ⟨a, ha⟩ := hevenDegree
  obtain ⟨b, hb⟩ := hevenZ
  rw [ha, hb] at hsplit
  omega

/-- A marked root has five ordinary B0 defects in total.  Since an odd number
lie in its own seven-point support, an even number lie outside that support. -/
theorem squareOrderNine_threeHigh_secondProfile_marked_support_external_defects_even
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
    {x m : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hm : m ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let F := G.neighborFinset m ∩ B 0
    let D := secondOrderDefectGraph G
    Even (D.neighborFinset m ∩ (T \ F)).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let F := G.neighborFinset m ∩ B 0
  let D := secondOrderDefectGraph G
  have hmParts := Finset.mem_inter.mp hm
  have hFsub : F ⊆ T := by
    intro t htF
    have htParts := Finset.mem_inter.mp htF
    refine Finset.mem_sdiff.mpr ⟨htParts.2, ?_⟩
    intro htS
    have htSParts := Finset.mem_inter.mp htS
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx htSParts.2 hmParts.2
        ((G.mem_neighborFinset x t).mp htSParts.1))
      ((G.adj_comm m t).mp ((G.mem_neighborFinset m t).mp htParts.1))
  have hmtype :=
    squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hmParts.2
  dsimp only at hmtype
  have htotal : (D.neighborFinset m ∩ T).card = 5 := by
    have heq : D.neighborFinset m ∩ T = D.neighborFinset m ∩ B 0 := by
      ext t
      simp only [Finset.mem_inter]
      constructor
      · intro ht
        exact ⟨ht.1, (Finset.mem_sdiff.mp ht.2).1⟩
      · intro ht
        refine ⟨ht.1, Finset.mem_sdiff.mpr ⟨ht.2, ?_⟩⟩
        intro htS
        have htSParts := Finset.mem_inter.mp htS
        have hmt : m ≠ t := by
          intro h
          subst t
          have hk1 := (Finset.mem_filter.mp hmParts.2).2
          have hk0 := (Finset.mem_filter.mp ht.2).2
          omega
        exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hmt
          ((G.adj_comm x m).mp ((G.mem_neighborFinset x m).mp hmParts.1))
          ((G.adj_comm x t).mp ((G.mem_neighborFinset x t).mp htSParts.1)))
            ((D.mem_neighborFinset m t).mp ht.1)
    rw [heq]
    exact hmtype.1
  have hinternalOdd : Odd (D.neighborFinset m ∩ F).card := by
    have hodd :=
      squareOrderNine_threeHigh_secondProfile_marked_support_internal_defects_odd
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hm
    dsimp only at hodd
    have heq : D.neighborFinset m ∩ F = F.filter fun t => D.Adj t m := by
      ext t
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · intro ht
        exact ⟨ht.2, (D.adj_comm m t).mp
          ((D.mem_neighborFinset m t).mp ht.1)⟩
      · intro ht
        exact ⟨(D.mem_neighborFinset m t).mpr
          ((D.adj_comm t m).mp ht.2), ht.1⟩
    rw [heq]
    exact hodd
  have hsplit :
      (D.neighborFinset m ∩ F).card +
        (D.neighborFinset m ∩ (T \ F)).card = 5 := by
    have hdisj : Disjoint (D.neighborFinset m ∩ F)
        (D.neighborFinset m ∩ (T \ F)) :=
      (Finset.disjoint_sdiff.mono Finset.inter_subset_right
        Finset.inter_subset_right)
    rw [← Finset.card_union_of_disjoint hdisj,
      ← Finset.inter_union_distrib_left,
      Finset.union_sdiff_of_subset hFsub]
    exact htotal
  rcases Nat.even_or_odd (D.neighborFinset m ∩ (T \ F)).card with heven | hodd
  · exact heven
  · obtain ⟨a, ha⟩ := hinternalOdd
    obtain ⟨b, hb⟩ := hodd
    rw [ha, hb] at hsplit
    omega

/-- Globally, each marked seven-point support is hit by exactly 42 of the 47
ordinary rows.  Its five missed rows are exactly the B0 defect neighbors of
the marked root. -/
theorem squareOrderNine_threeHigh_secondProfile_marked_support_fortyTwo_five_ledger
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
    {x m : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hm : m ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let F := G.neighborFinset m ∩ B 0
    let D := secondOrderDefectGraph G
    let misses := T.filter fun t => D.Adj t m
    let hits := T.filter fun t =>
      ((G.neighborFinset t ∩ T).filter fun w => w ∈ F).card = 1
    misses = D.neighborFinset m ∩ B 0 ∧ misses.card = 5 ∧ hits.card = 42 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let F := G.neighborFinset m ∩ B 0
  let D := secondOrderDefectGraph G
  let misses := T.filter fun t => D.Adj t m
  let hits := T.filter fun t =>
    ((G.neighborFinset t ∩ T).filter fun w => w ∈ F).card = 1
  have hmParts := Finset.mem_inter.mp hm
  have hmisses : misses = D.neighborFinset m ∩ B 0 := by
    ext t
    constructor
    · intro ht
      have htParts := Finset.mem_filter.mp ht
      have htT := Finset.mem_sdiff.mp htParts.1
      exact Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset m t).mpr ((D.adj_comm t m).mp htParts.2), htT.1⟩
    · intro ht
      have htParts := Finset.mem_inter.mp ht
      have hDmt := (D.mem_neighborFinset m t).mp htParts.1
      have htm : t ≠ m := (D.ne_of_adj hDmt).symm
      have htNotS : t ∉ S := by
        intro htS
        have htSParts := Finset.mem_inter.mp htS
        have htx : G.Adj t x := (G.adj_comm x t).mp
          ((G.mem_neighborFinset x t).mp htSParts.1)
        have hmx : G.Adj m x := (G.adj_comm x m).mp
          ((G.mem_neighborFinset x m).mp hmParts.1)
        exact (not_secondOrderDefect_adj_of_commonNeighbor
          G hfree htm htx hmx) ((D.adj_comm m t).mp hDmt)
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htParts.2, htNotS⟩,
        (D.adj_comm m t).mp hDmt⟩
  have hmtype :=
    squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hmParts.2
  dsimp only at hmtype
  have hmisscard : misses.card = 5 := by rw [hmisses, hmtype.1]
  have hTcard : T.card = 47 := by
    have hSsub : S ⊆ B 0 := Finset.inter_subset_right
    have hB0card : (B 0).card = 50 :=
      squareOrderNine_threeHigh_secondProfile_binZero_card
        G hcard hp hhigh hc3
    have hcensus :=
      squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
    dsimp only at hcensus
    have hScard : S.card = 3 := hcensus.2.2
    have hinter : S ∩ B 0 = S := Finset.inter_eq_left.mpr hSsub
    rw [Finset.card_sdiff, hinter, hB0card, hScard]
  have hhitIff : ∀ t ∈ T,
      (((G.neighborFinset t ∩ T).filter fun w => w ∈ F).card = 1 ↔
        ¬ D.Adj t m) := by
    intro t htT
    have ht : t ∈ B 0 \ S := htT
    have hlocal :=
      squareOrderNine_threeHigh_secondProfile_ordinary_marked_support_hit_or_defect
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht hm
    dsimp only at hlocal
    change ((((G.neighborFinset t ∩ T).filter fun w => w ∈ F).card = 1 ∧
      ¬ D.Adj t m) ∨
      (((G.neighborFinset t ∩ T).filter fun w => w ∈ F).card = 0 ∧
      D.Adj t m)) at hlocal
    constructor
    · intro hone
      rcases hlocal with hhit | hmiss
      · exact hhit.2
      · omega
    · intro hnotD
      rcases hlocal with hhit | hmiss
      · exact hhit.1
      · exact (hnotD hmiss.2).elim
  have hhitEq : hits = T.filter fun t => ¬ D.Adj t m := by
    ext t
    simp only [hits, Finset.mem_filter]
    constructor
    · rintro ⟨htT, hhit⟩
      exact ⟨htT, (hhitIff t htT).mp hhit⟩
    · rintro ⟨htT, hnotD⟩
      exact ⟨htT, (hhitIff t htT).mpr hnotD⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := T) (fun t => D.Adj t m)
  have hhitcard : hits.card = 42 := by
    rw [hhitEq]
    change misses.card + (T.filter fun t => ¬ D.Adj t m).card = T.card at hsplit
    omega
  exact ⟨hmisses, hmisscard, hhitcard⟩

/-- The mixed common-neighbor set of an ordinary B0 row and an unmarked B1
point splits exactly into residual-B0 centers and U1-core centers.  Special
B0 and marked-B1 centers contribute none. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_common_center_partition
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
    {x t b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    G.neighborFinset t ∩ G.neighborFinset b =
      ((G.neighborFinset t ∩ T) ∩ G.neighborFinset b) ∪
        ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  have hbU1 : b ∈ U1 := hb
  have hzero :=
    squareOrderNine_threeHigh_secondProfile_ordinary_row_zero_centers
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hzero
  have hpart :=
    squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpart
  change G.neighborFinset t =
    ((G.neighborFinset t ∩ S) ∪ (G.neighborFinset t ∩ T)) ∪
      ((G.neighborFinset t ∩ M) ∪ (G.neighborFinset t ∩ U1)) at hpart
  ext w
  constructor
  · intro hw
    have hwParts := Finset.mem_inter.mp hw
    have hwtParts : w ∈
        ((G.neighborFinset t ∩ S) ∪ (G.neighborFinset t ∩ T)) ∪
          ((G.neighborFinset t ∩ M) ∪ (G.neighborFinset t ∩ U1)) := by
      rw [← hpart]
      exact hwParts.1
    rcases Finset.mem_union.mp hwtParts with hw0 | hw1
    · rcases Finset.mem_union.mp hw0 with hwS | hwT
      · have hwSParts := Finset.mem_inter.mp hwS
        have hcardZero := hzero.1 w hwSParts.2
        have hmem : b ∈ G.neighborFinset w ∩ U1 :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset w b).mpr
              ((G.adj_comm b w).mp ((G.mem_neighborFinset b w).mp hwParts.2)),
            hbU1⟩
        have hempty := Finset.card_eq_zero.mp hcardZero
        have hmemEmpty : b ∈ (∅ : Finset V) := hempty ▸ hmem
        have : False := by simpa using hmemEmpty
        exact this.elim
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hwT, hwParts.2⟩)
    · rcases Finset.mem_union.mp hw1 with hwM | hwU
      · have hwMParts := Finset.mem_inter.mp hwM
        have hcardZero := hzero.2.1 w hwMParts.2
        have hmem : b ∈ G.neighborFinset w ∩ U1 :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset w b).mpr
              ((G.adj_comm b w).mp ((G.mem_neighborFinset b w).mp hwParts.2)),
            hbU1⟩
        have hempty := Finset.card_eq_zero.mp hcardZero
        have hmemEmpty : b ∈ (∅ : Finset V) := hempty ▸ hmem
        have : False := by simpa using hmemEmpty
        exact this.elim
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hwU, hwParts.2⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hwT | hwU
    · have hwParts := Finset.mem_inter.mp hwT
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwParts.1).1, hwParts.2⟩
    · have hwParts := Finset.mem_inter.mp hwU
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwParts.1).1, hwParts.2⟩

/-- Pointwise mixed defect coupling.  An ordinary B0 row is defect-adjacent
to an unmarked B1 point exactly when both possible common-center classes—the
residual B0 class and the U1 cubic-core class—are empty. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_defect_iff_no_centers
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
    {x t b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    D.Adj t b ↔
      ((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card = 0 ∧
        ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b).card = 0 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have htb : t ≠ b := by
    intro h
    subst b
    have htB0 := (Finset.mem_sdiff.mp ht).1
    have hbB1 := (Finset.mem_sdiff.mp hb).1
    have hk0 := (Finset.mem_filter.mp htB0).2
    have hk1 := (Finset.mem_filter.mp hbB1).2
    omega
  have hpartition :=
    squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_common_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht hb
  dsimp only at hpartition
  rw [secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree htb,
    hpartition]
  simp only [Finset.card_eq_zero, Finset.union_eq_empty]

/-- Zero-slack mixed resolution.  Every ordinary-B0/unmarked-B1 pair is
resolved in exactly one of three ways: a defect edge, one residual-B0 common
center, or one U1-core common center. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_three_way_resolution
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
    {x t b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
    let C := (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
    (D.Adj t b ∧ A.card = 0 ∧ C.card = 0) ∨
      (¬ D.Adj t b ∧ A.card = 1 ∧ C.card = 0) ∨
      (¬ D.Adj t b ∧ A.card = 0 ∧ C.card = 1) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let C := (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
  have htb : t ≠ b := by
    intro h
    subst b
    have htB0 := (Finset.mem_sdiff.mp ht).1
    have hbB1 := (Finset.mem_sdiff.mp hb).1
    have hk0 := (Finset.mem_filter.mp htB0).2
    have hk1 := (Finset.mem_filter.mp hbB1).2
    omega
  have hpartition :=
    squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_common_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht hb
  dsimp only at hpartition
  change G.neighborFinset t ∩ G.neighborFinset b = A ∪ C at hpartition
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro w hwA hwC
    have hwT := (Finset.mem_inter.mp (Finset.mem_inter.mp hwA).1).2
    have hwU := (Finset.mem_inter.mp (Finset.mem_inter.mp hwC).1).2
    have hwB0 := (Finset.mem_sdiff.mp hwT).1
    have hwB1 := (Finset.mem_sdiff.mp hwU).1
    have hk0 := (Finset.mem_filter.mp hwB0).2
    have hk1 := (Finset.mem_filter.mp hwB1).2
    omega
  have hcards := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdisj] at hcards
  have hle : A.card + C.card ≤ 1 := by
    rw [← hcards]
    exact (not_containsC4_iff_forall_common_le_one G).mp hfree t b htb
  have hzero :=
    squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_defect_iff_no_centers
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht hb
  dsimp only at hzero
  change D.Adj t b ↔ A.card = 0 ∧ C.card = 0 at hzero
  by_cases hD : D.Adj t b
  · left
    exact ⟨hD, (hzero.mp hD).1, (hzero.mp hD).2⟩
  · have hnotboth : ¬ (A.card = 0 ∧ C.card = 0) := by
      intro hz
      exact hD (hzero.mpr hz)
    by_cases hA : A.card = 0
    · right
      right
      have hC : C.card = 1 := by omega
      exact ⟨hD, hA, hC⟩
    · right
      left
      have hAone : A.card = 1 := by omega
      have hCzero : C.card = 0 := by omega
      exact ⟨hD, hAone, hCzero⟩

/-- Exact local cardinalities on an exceptional (hole) row.  It has three
unmarked core neighbors and six residual bin-zero neighbors, split evenly
between the marked-support pair centers and the complementary triple
centers. -/
theorem squareOrderNine_threeHigh_secondProfile_exceptional_row_exact_cardinalities
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
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hxt : (secondOrderDefectGraph G).Adj x t) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let R := G.neighborFinset t ∩ T
    (G.neighborFinset t ∩ U1).card = 3 ∧ R.card = 6 ∧
      (R.filter fun w => w ∈ P).card = 3 ∧
      (R.filter fun w => w ∉ P).card = 3 := by
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
  let C := R.filter fun w => w ∈ P
  let Q := R.filter fun w => w ∉ P
  let D := secondOrderDefectGraph G
  have hcent :=
    squareOrderNine_threeHigh_secondProfile_ordinary_special_marked_center_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hcent
  change (D.Adj x t ∧ NS.card = 0 ∧ NM.card = 0) ∨
    (¬ D.Adj x t ∧ NS.card + NM.card = 1) at hcent
  have hzero : NS.card = 0 ∧ NM.card = 0 := by
    rcases hcent with hzero | hone
    · exact hzero.2
    · exact (hone.1 hxt).elim
  have htNotP : t ∉ P := by
    intro htP
    simp only [P, Finset.mem_biUnion] at htP
    obtain ⟨m, hmM, htm⟩ := htP
    have hmNM : m ∈ NM := Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset t m).mpr
        ((G.adj_comm m t).mp ((G.mem_neighborFinset m t).mp
          (Finset.mem_inter.mp htm).1)), hmM⟩
    have hNMempty : NM = ∅ := Finset.card_eq_zero.mp hzero.2
    rw [hNMempty] at hmNM
    simpa using hmNM
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcensus
  have htOff : t ∈ T \ P := Finset.mem_sdiff.mpr ⟨ht, htNotP⟩
  have hNU : NU.card = 3 := hcensus.2.2.2.1 t htOff
  have hpart :=
    squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpart
  change N = (NS ∪ R) ∪ (NM ∪ NU) at hpart
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
  have hNcards := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hcross,
    Finset.card_union_of_disjoint hST,
    Finset.card_union_of_disjoint hMU] at hNcards
  have htB0 : t ∈ B 0 := (Finset.mem_sdiff.mp ht).1
  have htdeg : G.degree t = 9 := by
    have htL := (Finset.mem_filter.mp htB0).1
    have htNotHigh : t ∉ squareOrderHighVertices G 9 :=
      (Finset.mem_sdiff.mp htL).2
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard t with hlo | hhi
    · exact hlo
    · exact (htNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  rw [G.card_neighborFinset_eq_degree, htdeg] at hNcards
  have hR : R.card = 6 := by omega
  have hpair :=
    squareOrderNine_threeHigh_secondProfile_ordinary_pair_defect_three
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpair
  change C.card + (D.neighborFinset t ∩ M).card = 3 at hpair
  have hDmarkedZero : (D.neighborFinset t ∩ M).card = 0 := by
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 htB0
    dsimp only at htype
    rcases htype with hregular | hexceptional
    · have hxmem : x ∈ D.neighborFinset t ∩ B 3 :=
        Finset.mem_inter.mpr ⟨(D.mem_neighborFinset t x).mpr
          ((D.adj_comm x t).mp hxt), hx⟩
      have hempty : D.neighborFinset t ∩ B 3 = ∅ :=
        Finset.card_eq_zero.mp hregular.2.2
      rw [hempty] at hxmem
      simpa using hxmem
    · have hsub : D.neighborFinset t ∩ M ⊆ D.neighborFinset t ∩ B 1 := by
        intro m hm
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hm).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hm).2).2⟩
      apply Finset.card_eq_zero.mpr
      apply Finset.Subset.antisymm
      · intro m hm
        have hm' := hsub hm
        have hempty : D.neighborFinset t ∩ B 1 = ∅ :=
          Finset.card_eq_zero.mp hexceptional.2.1
        rw [hempty] at hm'
        simpa using hm'
      · exact Finset.empty_subset _
  have hC : C.card = 3 := by omega
  have hCQ : C.card + Q.card = R.card :=
    Finset.card_filter_add_card_filter_not (s := R) (fun w => w ∈ P)
  have hQ : Q.card = 3 := by omega
  exact ⟨hNU, hR, hC, hQ⟩

/-- Exceptional-to-pair reciprocity in the exact form used by the coupled
sixpack model.  The hole selects exactly three marked-support pair rows,
at most one from each marked support.  Equivalently, these are precisely
the pair rows whose complementary (triple-row) residual pattern contains
the hole. -/
theorem squareOrderNine_threeHigh_secondProfile_exceptional_pair_reciprocity
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
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hxt : (secondOrderDefectGraph G).Adj x t) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    let C := (G.neighborFinset t ∩ T).filter fun u => u ∈ P
    let Q := fun u => (G.neighborFinset u ∩ T).filter fun w => w ∉ P
    C.card = 3 ∧
      (∀ m ∈ M,
        (C.filter fun u => u ∈ G.neighborFinset m ∩ B 0).card = 1) ∧
      C = T.filter fun u => u ∈ P ∧ t ∈ Q u := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let C := (G.neighborFinset t ∩ T).filter fun u => u ∈ P
  let Q := fun u => (G.neighborFinset u ∩ T).filter fun w => w ∉ P
  let D := secondOrderDefectGraph G
  have hcards :=
    squareOrderNine_threeHigh_secondProfile_exceptional_row_exact_cardinalities
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht hxt
  dsimp only at hcards
  have hpattern :=
    squareOrderNine_threeHigh_secondProfile_ordinary_pair_pattern
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
  dsimp only at hpattern
  let F := fun m => G.neighborFinset m ∩ B 0
  let CF := fun m => C.filter fun u => u ∈ F m
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_marked_binOne_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpack
  have hCFdisj : ∀ m ∈ M, ∀ n ∈ M, m ≠ n → Disjoint (CF m) (CF n) := by
    intro m hm n hn hmn
    exact (hpack.2.2.1 m hm n hn hmn).mono
      (by intro u hu; exact (Finset.mem_filter.mp hu).2)
      (by intro u hu; exact (Finset.mem_filter.mp hu).2)
  have hCFunion : M.biUnion CF = C := by
    ext u
    constructor
    · intro hu
      simp only [Finset.mem_biUnion] at hu
      obtain ⟨m, _hm, huCF⟩ := hu
      exact (Finset.mem_filter.mp huCF).1
    · intro huC
      have huP := (Finset.mem_filter.mp huC).2
      simp only [P, Finset.mem_biUnion] at huP
      obtain ⟨m, hmM, hum⟩ := huP
      simp only [Finset.mem_biUnion]
      exact ⟨m, hmM, Finset.mem_filter.mpr ⟨huC, hum⟩⟩
  have hsum : (∑ m ∈ M, (CF m).card) = 3 := by
    rw [← Finset.card_biUnion hCFdisj, hCFunion, hcards.2.2.1]
  have hEach : ∀ m ∈ M, (CF m).card = 1 := by
    intro m hm
    have hMcard : M.card = 3 := hpack.1
    have hrest : (∑ n ∈ M.erase m, (CF n).card) ≤ 2 := by
      calc
        (∑ n ∈ M.erase m, (CF n).card) ≤ ∑ _n ∈ M.erase m, 1 := by
          apply Finset.sum_le_sum
          intro n hn
          exact hpattern.2.2 n (Finset.mem_of_mem_erase hn)
        _ = 2 := by simp [Finset.card_erase_of_mem hm, hMcard]
    have hsplit := Finset.sum_erase_add M (fun n => (CF n).card) hm
    have hsplit' : (∑ n ∈ M.erase m, (CF n).card) + (CF m).card = 3 :=
      hsplit.trans hsum
    have hmLe : (CF m).card ≤ 1 := hpattern.2.2 m hm
    omega
  have htNotP : t ∉ P := by
    have hcent :=
      squareOrderNine_threeHigh_secondProfile_ordinary_special_marked_center_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht
    dsimp only at hcent
    let NS := G.neighborFinset t ∩ S
    let NM := G.neighborFinset t ∩ M
    change (D.Adj x t ∧ NS.card = 0 ∧ NM.card = 0) ∨
      (¬ D.Adj x t ∧ NS.card + NM.card = 1) at hcent
    have hNMzero : NM.card = 0 := by
      rcases hcent with hzero | hone
      · exact hzero.2.2
      · exact (hone.1 hxt).elim
    intro htP
    simp only [P, Finset.mem_biUnion] at htP
    obtain ⟨m, hmM, htm⟩ := htP
    have hmNM : m ∈ NM := Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset t m).mpr
        ((G.adj_comm m t).mp ((G.mem_neighborFinset m t).mp
          (Finset.mem_inter.mp htm).1)), hmM⟩
    have hempty : NM = ∅ := Finset.card_eq_zero.mp hNMzero
    rw [hempty] at hmNM
    simpa using hmNM
  refine ⟨hcards.2.2.1, ?_, ?_⟩
  · intro m hm
    exact hEach m hm
  ext u
  simp only [C, Q, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨htu, huT⟩, huP⟩
    refine ⟨huT, huP, ?_⟩
    exact ⟨⟨(G.mem_neighborFinset u t).mpr
      ((G.adj_comm t u).mp ((G.mem_neighborFinset t u).mp htu)), ht⟩, htNotP⟩
  · rintro ⟨huT, huP, ⟨htu, _htT⟩, _htNotP⟩
    refine ⟨⟨?_, huT⟩, huP⟩
    exact (G.mem_neighborFinset t u).mpr
      ((G.adj_comm u t).mp ((G.mem_neighborFinset u t).mp htu))

/-- On an exceptional (hole) ordinary row, the defect alternative in the
mixed three-way resolution is impossible.  Hence every unmarked point is
resolved by exactly one residual-B0 center or exactly one U1-core center.
This is the graph-level form of the coupled DTB capacity/orthogonality row
used by the q=9 obstruction search. -/
theorem squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center
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
    {x t b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hxt : (secondOrderDefectGraph G).Adj x t)
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
    let C := (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
    (A.card = 1 ∧ C.card = 0) ∨ (A.card = 0 ∧ C.card = 1) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let D := secondOrderDefectGraph G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let C := (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
  have htB0 : t ∈ B 0 := (Finset.mem_sdiff.mp ht).1
  have htype :=
    squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc4 htB0
  dsimp only at htype
  have hB1zero : (D.neighborFinset t ∩ B 1).card = 0 := by
    rcases htype with hregular | hexceptional
    · have hxmem : x ∈ D.neighborFinset t ∩ B 3 := by
        refine Finset.mem_inter.mpr ⟨?_, hx⟩
        exact (D.mem_neighborFinset t x).mpr ((D.adj_comm x t).mp hxt)
      have hne : (D.neighborFinset t ∩ B 3).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨x, hxmem⟩
      exact (hne hregular.2.2).elim
    · exact hexceptional.2.1
  have hnotDtb : ¬ D.Adj t b := by
    intro htb
    have hbB1 : b ∈ B 1 := (Finset.mem_sdiff.mp hb).1
    have hbmem : b ∈ D.neighborFinset t ∩ B 1 :=
      Finset.mem_inter.mpr ⟨(D.mem_neighborFinset t b).mpr htb, hbB1⟩
    have hempty := Finset.card_eq_zero.mp hB1zero
    rw [hempty] at hbmem
    simpa using hbmem
  have hthree :=
    squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_three_way_resolution
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ht hb
  dsimp only at hthree
  change (D.Adj t b ∧ A.card = 0 ∧ C.card = 0) ∨
    (¬ D.Adj t b ∧ A.card = 1 ∧ C.card = 0) ∨
    (¬ D.Adj t b ∧ A.card = 0 ∧ C.card = 1) at hthree
  rcases hthree with hdefect | hresidual | hcore
  · exact (hnotDtb hdefect.1).elim
  · exact Or.inl hresidual.2
  · exact Or.inr hcore.2

/-- Complement-law packaging of
`squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center`.
For an exceptional row the residual-center and U1-core-center counts sum to
one, and either count is one exactly when the other is zero. -/
theorem squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_resolution
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
    {x t b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ (squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hxt : (secondOrderDefectGraph G).Adj x t)
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
    let C := (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
    A.card + C.card = 1 ∧
      (A.card = 1 ↔ C.card = 0) ∧ (C.card = 1 ↔ A.card = 0) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let A := (G.neighborFinset t ∩ T) ∩ G.neighborFinset b
  let C := (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
  have hcenter :=
    squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht hxt hb
  dsimp only at hcenter
  change (A.card = 1 ∧ C.card = 0) ∨
    (A.card = 0 ∧ C.card = 1) at hcenter
  change A.card + C.card = 1 ∧
    (A.card = 1 ↔ C.card = 0) ∧ (C.card = 1 ↔ A.card = 0)
  omega

/-- Set form of the exceptional-row DTB partition.  The U1 blocks carried by
residual neighbors of a hole row cover exactly the complement of the U1
blocks carried by its core neighbors.  The preceding pointwise theorem also
shows that the residual cover has multiplicity one. -/
theorem squareOrderNine_threeHigh_secondProfile_exceptional_residualBlocks_eq_coreComplement
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
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hxt : (secondOrderDefectGraph G).Adj x t) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let R := G.neighborFinset t ∩ T
    let C := G.neighborFinset t ∩ U1
    R.biUnion (fun w => G.neighborFinset w ∩ U1) =
      U1 \ C.biUnion (fun a => G.neighborFinset a ∩ U1) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let R := G.neighborFinset t ∩ T
  let C := G.neighborFinset t ∩ U1
  ext b
  constructor
  · intro hbResidual
    simp only [Finset.mem_biUnion] at hbResidual
    obtain ⟨w, hwR, hwb⟩ := hbResidual
    have hbU1 : b ∈ U1 := (Finset.mem_inter.mp hwb).2
    have hbInput : b ∈ B 1 \ (G.neighborFinset x ∩ B 1) := hbU1
    have hcell :=
      squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht hxt hbInput
    dsimp only at hcell
    change (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card = 1 ∧
      ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b).card = 0) ∨
      (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card = 0 ∧
      ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b).card = 1) at hcell
    have hwCommon : w ∈ (G.neighborFinset t ∩ T) ∩ G.neighborFinset b := by
      refine Finset.mem_inter.mpr ⟨hwR, ?_⟩
      exact (G.mem_neighborFinset b w).mpr
        ((G.adj_comm w b).mp ((G.mem_neighborFinset w b).mp
          (Finset.mem_inter.mp hwb).1))
    have hcoreZero : ((G.neighborFinset t ∩ U1) ∩
        G.neighborFinset b).card = 0 := by
      rcases hcell with hresidual | hcore
      · exact hresidual.2
      · have hempty := Finset.card_eq_zero.mp hcore.1
        rw [hempty] at hwCommon
        simpa using hwCommon
    refine Finset.mem_sdiff.mpr ⟨hbU1, ?_⟩
    intro hbCore
    simp only [Finset.mem_biUnion] at hbCore
    obtain ⟨a, haC, hab⟩ := hbCore
    have haCommon : a ∈ (G.neighborFinset t ∩ U1) ∩
        G.neighborFinset b := by
      refine Finset.mem_inter.mpr ⟨haC, ?_⟩
      exact (G.mem_neighborFinset b a).mpr
        ((G.adj_comm a b).mp ((G.mem_neighborFinset a b).mp
          (Finset.mem_inter.mp hab).1))
    have hempty := Finset.card_eq_zero.mp hcoreZero
    rw [hempty] at haCommon
    simpa using haCommon
  · intro hbComplement
    have hbParts := Finset.mem_sdiff.mp hbComplement
    have hbInput : b ∈ B 1 \ (G.neighborFinset x ∩ B 1) := hbParts.1
    have hcell :=
      squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht hxt hbInput
    dsimp only at hcell
    change (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card = 1 ∧
      ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b).card = 0) ∨
      (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card = 0 ∧
      ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b).card = 1) at hcell
    rcases hcell with hresidual | hcore
    · have hpos : 0 < ((G.neighborFinset t ∩ T) ∩
          G.neighborFinset b).card := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have hwParts := Finset.mem_inter.mp hw
      simp only [Finset.mem_biUnion]
      refine ⟨w, hwParts.1, Finset.mem_inter.mpr ⟨?_, hbParts.1⟩⟩
      exact (G.mem_neighborFinset w b).mpr
        ((G.adj_comm b w).mp ((G.mem_neighborFinset b w).mp hwParts.2))
    · have hpos : 0 < ((G.neighborFinset t ∩ U1) ∩
          G.neighborFinset b).card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have haParts := Finset.mem_inter.mp ha
      apply (hbParts.2 ?_).elim
      simp only [Finset.mem_biUnion]
      refine ⟨a, haParts.1, Finset.mem_inter.mpr ⟨?_, hbParts.1⟩⟩
      exact (G.mem_neighborFinset a b).mpr
        ((G.adj_comm b a).mp ((G.mem_neighborFinset b a).mp haParts.2))

/-- Cardinal form of the exceptional block complement.  The six disjoint
residual blocks cover fifteen unmarked points (three blocks of size two and
three of size three), while the three core-neighbor blocks cover the other
nine. -/
theorem squareOrderNine_threeHigh_secondProfile_exceptional_block_partition_cardinalities
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
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0))
    (hxt : (secondOrderDefectGraph G).Adj x t) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let R := G.neighborFinset t ∩ T
    let C := G.neighborFinset t ∩ U1
    (R.biUnion fun w => G.neighborFinset w ∩ U1).card = 15 ∧
      (C.biUnion fun a => G.neighborFinset a ∩ U1).card = 9 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  let R := G.neighborFinset t ∩ T
  let C := G.neighborFinset t ∩ U1
  have hdisj : ∀ u ∈ R, ∀ v ∈ R, u ≠ v →
      Disjoint (G.neighborFinset u ∩ U1) (G.neighborFinset v ∩ U1) := by
    intro u hu v hv huv
    exact squareOrderNine_threeHigh_secondProfile_residual_neighbor_blocks_disjoint
      G hfree ht hu hv huv
  have hweights :=
    squareOrderNine_threeHigh_secondProfile_row_center_weight_sums
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 (t := t) hx
  dsimp only at hweights
  have hcards :=
    squareOrderNine_threeHigh_secondProfile_exceptional_row_exact_cardinalities
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht hxt
  dsimp only at hcards
  have hresidual : (R.biUnion fun w => G.neighborFinset w ∩ U1).card = 15 := by
    rw [Finset.card_biUnion hdisj, hweights.1, hcards.2.2.1, hcards.2.2.2]
  have hcomplement :=
    squareOrderNine_threeHigh_secondProfile_exceptional_residualBlocks_eq_coreComplement
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx ht hxt
  dsimp only at hcomplement
  change (R.biUnion fun w => G.neighborFinset w ∩ U1) =
    U1 \ (C.biUnion fun a => G.neighborFinset a ∩ U1) at hcomplement
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
  have hcoreSub : (C.biUnion fun a => G.neighborFinset a ∩ U1) ⊆ U1 := by
    intro b hb
    simp only [Finset.mem_biUnion] at hb
    obtain ⟨a, _ha, hab⟩ := hb
    exact (Finset.mem_inter.mp hab).2
  have hsplit := Finset.card_sdiff_add_card_eq_card hcoreSub
  have hcomplementCard := congrArg Finset.card hcomplement
  have hsplit' : 15 + (C.biUnion fun a => G.neighborFinset a ∩ U1).card = 24 := by
    calc
      15 + (C.biUnion fun a => G.neighborFinset a ∩ U1).card =
          (R.biUnion fun w => G.neighborFinset w ∩ U1).card +
            (C.biUnion fun a => G.neighborFinset a ∩ U1).card := by rw [hresidual]
      _ = (U1 \ (C.biUnion fun a => G.neighborFinset a ∩ U1)).card +
            (C.biUnion fun a => G.neighborFinset a ∩ U1).card := by rw [hcomplementCard]
      _ = U1.card := hsplit
      _ = 24 := hU1card
  refine ⟨hresidual, ?_⟩
  apply Nat.add_left_cancel (n := 15)
  calc
    15 + (C.biUnion fun a => G.neighborFinset a ∩ U1).card = 24 := hsplit'
    _ = 15 + 9 := by norm_num

/-- Algebraic form of the decisive mixed-center compatibility constraint.
The residual-center matrix `A Q` and the cubic-core matrix `Q K` have
disjoint support, so their entrywise inner product (equivalently
`trace (Qᵀ A Q K)`) is zero.  This conclusion does not use defect row or
column degrees. -/
theorem squareOrderNine_threeHigh_secondProfile_residual_core_trace_zero
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
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    (∑ t ∈ T, ∑ b ∈ U1,
      (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).card *
        ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset b).card)) = 0 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  have hTU : Disjoint T U1 := by
    rw [Finset.disjoint_left]
    intro z hzT hzU
    have hzB0 := (Finset.mem_sdiff.mp hzT).1
    have hzB1 := (Finset.mem_sdiff.mp hzU).1
    have hk0 := (Finset.mem_filter.mp hzB0).2
    have hk1 := (Finset.mem_filter.mp hzB1).2
    omega
  exact c4Free_crossBlock_trace_zero G hfree T U1 hTU

/-- The companion Gram identity.  Off the diagonal, a pair of ordinary B0
rows cannot simultaneously share an unmarked-B1 incidence point and a
residual-B0 common center.  In matrix notation this is the vanishing of the
off-diagonal part of the entrywise product `(Q Qᵀ) * (A²)`. -/
theorem squareOrderNine_threeHigh_secondProfile_incidence_residual_gram_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x : V} :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    (∑ t ∈ T, ∑ u ∈ T.filter (fun u => u ≠ t),
      ((G.neighborFinset t ∩ U1) ∩ G.neighborFinset u).card *
        ((G.neighborFinset t ∩ T) ∩ G.neighborFinset u).card) = 0 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  have hTU : Disjoint T U1 := by
    rw [Finset.disjoint_left]
    intro z hzT hzU
    have hzB0 := (Finset.mem_sdiff.mp hzT).1
    have hzB1 := (Finset.mem_sdiff.mp hzU).1
    have hk0 := (Finset.mem_filter.mp hzB0).2
    have hk1 := (Finset.mem_filter.mp hzB1).2
    omega
  exact c4Free_sameBlock_offDiagonal_gram_zero G hfree T U1 hTU

/-- For each U1 point, exactly fifteen ordinary rows are resolved through a
U1-core common center: its three cubic neighbors have five ordinary B0
neighbors each, and these three service fibers are disjoint. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_core_resolved_rows_card
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
    {x b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let C := fun t => (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
    (T.filter fun t => (C t).Nonempty).card = 15 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let W := G.neighborFinset b ∩ U1
  let F := fun w => G.neighborFinset w ∩ T
  let C := fun t => (G.neighborFinset t ∩ U1) ∩ G.neighborFinset b
  have hbU1 : b ∈ U1 := hb
  have hcore :=
    squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcore
  have hWcard : W.card = 3 := by
    have hdeg := hcore.2.1 ⟨b, hbU1⟩
    rw [degree_induce_finset_eq_card_inter] at hdeg
    exact hdeg
  have hFcard : ∀ w ∈ W, (F w).card = 5 := by
    intro w hwW
    have hwParts := Finset.mem_inter.mp hwW
    have hwU := Finset.mem_sdiff.mp hwParts.2
    have hwNotX : ¬ G.Adj w x := by
      intro hwx
      exact hwU.2 (Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x w).mpr hwx.symm, hwU.1⟩)
    have hwdeg :=
      squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hwU.1
    dsimp only at hwdeg
    have hB0card : (G.neighborFinset w ∩ B 0).card = 5 := by
      simpa [hwNotX] using hwdeg.2
    have hFT : F w = G.neighborFinset w ∩ B 0 := by
      apply Finset.Subset.antisymm
      · intro t htF
        have htParts := Finset.mem_inter.mp htF
        exact Finset.mem_inter.mpr ⟨htParts.1,
          (Finset.mem_sdiff.mp htParts.2).1⟩
      · intro t htB0
        have htParts := Finset.mem_inter.mp htB0
        refine Finset.mem_inter.mpr ⟨htParts.1,
          Finset.mem_sdiff.mpr ⟨htParts.2, ?_⟩⟩
        intro htS
        have htSParts := Finset.mem_inter.mp htS
        have hforbid :=
          squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
            G hfree hhigh hx htSParts.2 hwU.1
              ((G.mem_neighborFinset x t).mp htSParts.1)
        exact hforbid ((G.adj_comm w t).mp
          ((G.mem_neighborFinset w t).mp htParts.1))
    rw [hFT, hB0card]
  have hbNotT : b ∉ T := by
    intro hbT
    have hbB0 := (Finset.mem_sdiff.mp hbT).1
    have hk0 := (Finset.mem_filter.mp hbB0).2
    have hk1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
    omega
  have hgeneric :=
    c4Free_neighbor_blocks_partition_common_targets G hfree b T hbNotT
  dsimp only at hgeneric
  have hdisj : ∀ w ∈ W, ∀ z ∈ W, w ≠ z → Disjoint (F w) (F z) := by
    intro w hwW z hzW hwz
    exact hgeneric.1 w (Finset.mem_inter.mp hwW).1
      z (Finset.mem_inter.mp hzW).1 hwz
  have hunion : W.biUnion F = T.filter fun t => (C t).Nonempty := by
    ext t
    constructor
    · intro htUnion
      simp only [Finset.mem_biUnion] at htUnion
      obtain ⟨w, hwW, htF⟩ := htUnion
      have hwParts := Finset.mem_inter.mp hwW
      have htParts := Finset.mem_inter.mp htF
      refine Finset.mem_filter.mpr ⟨htParts.2, ⟨w, ?_⟩⟩
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset t w).mpr
          ((G.adj_comm w t).mp ((G.mem_neighborFinset w t).mp htParts.1)),
        hwParts.2⟩, hwParts.1⟩
    · intro htFilter
      have htParts := Finset.mem_filter.mp htFilter
      obtain ⟨w, hwC⟩ := htParts.2
      have hwCParts := Finset.mem_inter.mp hwC
      have hwtU := Finset.mem_inter.mp hwCParts.1
      simp only [Finset.mem_biUnion]
      exact ⟨w, Finset.mem_inter.mpr ⟨hwCParts.2, hwtU.2⟩,
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset w t).mpr
            ((G.adj_comm t w).mp ((G.mem_neighborFinset t w).mp hwtU.1)),
          htParts.1⟩⟩
  rw [← hunion, Finset.card_biUnion hdisj]
  calc
    (∑ w ∈ W, (F w).card) = ∑ _w ∈ W, 5 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hFcard w hw
    _ = 15 := by simp [hWcard]

/-- Complete mixed column law.  For a fixed U1 point, the 47 ordinary rows
split into defect, residual-B0-resolved, and U1-core-resolved cells.  There
are always fifteen core-resolved cells; removing the five total B0 defects
shows that the residual count is `27` plus the number of special B0 defects. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_mixed_column_counts
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
    {x b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hb : b ∈ squareOrderNineLowIncidenceBin G 1 \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1)) :
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
    defectRows.card + specialDefects = 5 ∧ coreRows.card = 15 ∧
      residualRows.card = 27 + specialDefects := by
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
  have hbParts := Finset.mem_sdiff.mp hb
  have hTcard : T.card = 47 := by
    have hSsub : S ⊆ B 0 := Finset.inter_subset_right
    have hB0card : (B 0).card = 50 :=
      squareOrderNine_threeHigh_secondProfile_binZero_card
        G hcard hp hhigh hc3
    have hcensus :=
      squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
    dsimp only at hcensus
    have hScard : S.card = 3 := hcensus.2.2
    have hinter : S ∩ B 0 = S := Finset.inter_eq_left.mpr hSsub
    rw [Finset.card_sdiff, hinter, hB0card, hScard]
  have hdefectEq : defectRows = D.neighborFinset b ∩ T := by
    ext t
    constructor
    · intro ht
      have htParts := Finset.mem_filter.mp ht
      exact Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset b t).mpr ((D.adj_comm t b).mp htParts.2),
        htParts.1⟩
    · intro ht
      have htParts := Finset.mem_inter.mp ht
      exact Finset.mem_filter.mpr ⟨htParts.2,
        (D.adj_comm b t).mp ((D.mem_neighborFinset b t).mp htParts.1)⟩
  have hB0split : B 0 = S ∪ T := by
    ext t
    simp only [S, T, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro htB
      by_cases htS : t ∈ G.neighborFinset x ∩ B 0
      · exact Or.inl (Finset.mem_inter.mp htS)
      · exact Or.inr ⟨htB, fun h => htS (Finset.mem_inter.mpr h)⟩
    · rintro (⟨_htN, htB⟩ | ⟨htB, _htNotS⟩) <;> exact htB
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro t htS htT
    exact (Finset.mem_sdiff.mp htT).2 htS
  have hdefectCount : defectRows.card + specialDefects = 5 := by
    have hbtype :=
      squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hbParts.1
    dsimp only at hbtype
    have hsplit : D.neighborFinset b ∩ B 0 =
        (D.neighborFinset b ∩ S) ∪ (D.neighborFinset b ∩ T) := by
      rw [hB0split, Finset.inter_union_distrib_left]
    have hcards := congrArg Finset.card hsplit
    rw [Finset.card_union_of_disjoint
      (hST.mono Finset.inter_subset_right Finset.inter_subset_right)] at hcards
    rw [hbtype.1] at hcards
    rw [hdefectEq]
    omega
  have hcoreCount : coreRows.card = 15 :=
    squareOrderNine_threeHigh_secondProfile_unmarked_core_resolved_rows_card
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hb
  have hDR : Disjoint defectRows residualRows := by
    rw [Finset.disjoint_left]
    intro t htD htR
    have htDParts := Finset.mem_filter.mp htD
    have htRParts := Finset.mem_filter.mp htR
    have hzero :=
      squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_defect_iff_no_centers
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx htDParts.1 hb
    dsimp only at hzero
    have hAempty := Finset.card_eq_zero.mp (hzero.mp htDParts.2).1
    have hbad : (∅ : Finset V).Nonempty := hAempty ▸ htRParts.2
    simpa using hbad
  have hDC : Disjoint defectRows coreRows := by
    rw [Finset.disjoint_left]
    intro t htD htC
    have htDParts := Finset.mem_filter.mp htD
    have htCParts := Finset.mem_filter.mp htC
    have hzero :=
      squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_defect_iff_no_centers
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx htDParts.1 hb
    dsimp only at hzero
    have hCempty := Finset.card_eq_zero.mp (hzero.mp htDParts.2).2
    have hbad : (∅ : Finset V).Nonempty := hCempty ▸ htCParts.2
    simpa using hbad
  have hRC : Disjoint residualRows coreRows := by
    rw [Finset.disjoint_left]
    intro t htR htC
    have htRParts := Finset.mem_filter.mp htR
    have htCParts := Finset.mem_filter.mp htC
    have hthree :=
      squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_three_way_resolution
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx htRParts.1 hb
    dsimp only at hthree
    rcases hthree with hD | hA | hC
    · have hAempty := Finset.card_eq_zero.mp hD.2.1
      have hbad : (∅ : Finset V).Nonempty := hAempty ▸ htRParts.2
      simpa using hbad
    · have hCempty := Finset.card_eq_zero.mp hA.2.2
      have hbad : (∅ : Finset V).Nonempty := hCempty ▸ htCParts.2
      simpa using hbad
    · have hAempty := Finset.card_eq_zero.mp hC.2.1
      have hbad : (∅ : Finset V).Nonempty := hAempty ▸ htRParts.2
      simpa using hbad
  have hpartition : T = (defectRows ∪ residualRows) ∪ coreRows := by
    ext t
    constructor
    · intro htT
      have hthree :=
        squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_three_way_resolution
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx htT hb
      dsimp only at hthree
      rcases hthree with hDcase | hAcase | hCcase
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨htT, hDcase.1⟩))
      · have hpos : 0 < (A t).card := by
          rw [hAcase.2.1]
          norm_num
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨htT, Finset.card_pos.mp hpos⟩))
      · have hpos : 0 < (C t).card := by
          rw [hCcase.2.2]
          norm_num
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨htT, Finset.card_pos.mp hpos⟩)
    · intro ht
      rcases Finset.mem_union.mp ht with htDR | htC
      · rcases Finset.mem_union.mp htDR with htD | htR
        · exact (Finset.mem_filter.mp htD).1
        · exact (Finset.mem_filter.mp htR).1
      · exact (Finset.mem_filter.mp htC).1
  have hDRC : Disjoint (defectRows ∪ residualRows) coreRows := by
    rw [Finset.disjoint_left]
    intro t htDR htC
    rcases Finset.mem_union.mp htDR with htD | htR
    · exact (Finset.disjoint_left.mp hDC) htD htC
    · exact (Finset.disjoint_left.mp hRC) htR htC
  have hcards := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hDRC,
    Finset.card_union_of_disjoint hDR,
    hTcard, hcoreCount] at hcards
  have hresidualCount : residualRows.card = 27 + specialDefects := by omega
  exact ⟨hdefectCount, hcoreCount, hresidualCount⟩

/-- The total special-defect mass across the 24 U1 columns is branch-sharp:
zero in the three-triangle branch and six in the four-triangle branch. -/
theorem squareOrderNine_threeHigh_secondProfile_special_defect_mass_dichotomy
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧
        (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 0) ∨
      ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧
        (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 6) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let R := S \ D.neighborFinset x
  have hrow : ∀ y ∈ S,
      (D.neighborFinset y ∩ U1).card = if y ∈ R then 3 else 0 := by
    intro y hyS
    have hyParts := Finset.mem_inter.mp hyS
    have hDMzero : D.neighborFinset y ∩ M = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hmAll := Finset.mem_inter.mp hm
      have hmParts := Finset.mem_inter.mp hmAll.2
      have hDym := (D.mem_neighborFinset y m).mp
        hmAll.1
      have hym : y ≠ m := D.ne_of_adj hDym
      have hyx : G.Adj y x := (G.adj_comm x y).mp
        ((G.mem_neighborFinset x y).mp hyParts.1)
      have hmx : G.Adj m x := (G.adj_comm x m).mp
        ((G.mem_neighborFinset x m).mp hmParts.1)
      exact (not_secondOrderDefect_adj_of_commonNeighbor
        G hfree hym hyx hmx) hDym
    have hsplit : D.neighborFinset y ∩ B 1 =
        (D.neighborFinset y ∩ M) ∪ (D.neighborFinset y ∩ U1) := by
      ext z
      constructor
      · intro hz
        have hzParts := Finset.mem_inter.mp hz
        by_cases hzM : z ∈ G.neighborFinset x ∩ B 1
        · exact Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hzParts.1, hzM⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hzParts.1,
              Finset.mem_sdiff.mpr ⟨hzParts.2, hzM⟩⟩)
      · intro hz
        rcases Finset.mem_union.mp hz with hzM | hzU
        · have hzParts := Finset.mem_inter.mp hzM
          exact Finset.mem_inter.mpr ⟨hzParts.1,
            (Finset.mem_inter.mp hzParts.2).2⟩
        · have hzParts := Finset.mem_inter.mp hzU
          exact Finset.mem_inter.mpr ⟨hzParts.1,
            (Finset.mem_sdiff.mp hzParts.2).1⟩
    rw [hDMzero, Finset.empty_union] at hsplit
    have hcards := congrArg Finset.card hsplit
    by_cases hyR : y ∈ R
    · have hyRParts := Finset.mem_sdiff.mp hyR
      have hreg :=
        squareOrderNine_threeHigh_secondProfile_nondefect_binZero_is_regular
          G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
            (Finset.mem_sdiff.mpr ⟨hyS, hyRParts.2⟩)
      dsimp only at hreg
      simp only [if_pos hyR]
      rw [hreg.2.1] at hcards
      omega
    · have hyDx : y ∈ D.neighborFinset x := by
        by_contra hyNotDx
        exact hyR (Finset.mem_sdiff.mpr ⟨hyS, hyNotDx⟩)
      have htype :=
        squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
          G hfree hmin hcover hcard hp hhigh hc2 hc4 hyParts.2
      dsimp only at htype
      have hDxy : D.Adj x y := (D.mem_neighborFinset x y).mp hyDx
      rcases htype with hreg | hexc
      · have hxInter : x ∈ D.neighborFinset y ∩ B 3 :=
          Finset.mem_inter.mpr ⟨(D.mem_neighborFinset y x).mpr
            ((D.adj_comm x y).mp hDxy), hx⟩
        have hpos : 0 < (D.neighborFinset y ∩ B 3).card :=
          Finset.card_pos.mpr ⟨x, hxInter⟩
        rw [hreg.2.2] at hpos
        omega
      · simp only [if_neg hyR]
        rw [hexc.2.1] at hcards
        exact hcards.symm
  have hsumSwap := sum_card_neighborFinset_inter_comm D U1 S
  have hsumRow : (∑ y ∈ S, (D.neighborFinset y ∩ U1).card) =
      3 * R.card := by
    calc
      _ = ∑ y ∈ S, if y ∈ R then 3 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hrow y hy
      _ = 3 * R.card := by
        have hRsub : R ⊆ S := Finset.sdiff_subset
        rw [← Finset.sum_filter]
        have hfilter : S.filter (fun y => y ∈ R) = R := by
          ext y
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hRsub h, h⟩⟩
        rw [hfilter]
        simp [Nat.mul_comm]
  have htotal : (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) =
      3 * R.card := hsumSwap.trans hsumRow
  have hbranch :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  change ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ R.card = 0) ∨
    ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ R.card = 2) at hbranch
  rcases hbranch with h3 | h4
  · left
    have hmass : (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 0 := by
      rw [htotal, h3.2]
    exact ⟨h3.1, hmass⟩
  · right
    have hmass : (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 6 := by
      rw [htotal, h4.2]
    exact ⟨h4.1, hmass⟩

/-- A special endpoint outside the defect fiber of `x` has a seven-point
ordinary B0 support. -/
theorem squareOrderNine_threeHigh_secondProfile_nondefect_special_support_card_seven
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
    ((G.neighborFinset y ∩ B 0) \ S).card = 7 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let D := secondOrderDefectGraph G
  let R := S \ D.neighborFinset x
  let F := G.neighborFinset y ∩ B 0
  have hyR : y ∈ R := hy
  have hyS := (Finset.mem_sdiff.mp hy).1
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
  have hErase : (R.erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hyR, hRcard]
  obtain ⟨z, hzErase⟩ := Finset.card_pos.mp (by omega : 0 < (R.erase y).card)
  have hzR := (Finset.mem_erase.mp hzErase).2
  have hyz : y ≠ z := by
    intro h
    subst z
    exact (Finset.mem_erase.mp hzErase).1 rfl
  have hyzAdj :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hyR hzR hyz
        (by rcases hbranch with h3 | h4 <;> omega)
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpack
  have hFcard : F.card = 8 := hpack.1 y hyS
  have hInterLe : (F ∩ S).card ≤ 1 := by
    apply (Finset.card_le_card ?_).trans
      ((not_containsC4_iff_forall_common_le_one G).mp hfree y x ?_)
    · intro w hw
      have hwParts := Finset.mem_inter.mp hw
      have hwS := Finset.mem_inter.mp hwParts.2
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwParts.1).1, hwS.1⟩
    · intro hyx
      subst y
      exact G.loopless.irrefl x
        ((G.mem_neighborFinset x x).mp (Finset.mem_inter.mp hyS).1)
  have hzInter : z ∈ F ∩ S := by
    have hzS := (Finset.mem_sdiff.mp hzR).1
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset y z).mpr hyzAdj, (Finset.mem_inter.mp hzS).2⟩, hzS⟩
  have hInterPos : 0 < (F ∩ S).card := Finset.card_pos.mpr ⟨z, hzInter⟩
  have hInterCard : (F ∩ S).card = 1 := by omega
  have hInterCard' : (S ∩ F).card = 1 := by
    rw [Finset.inter_comm]
    exact hInterCard
  rw [Finset.card_sdiff, hFcard, hInterCard']

/-- Pointwise puncture law.  For each nondefect special endpoint, its three
U1 defect neighbors are exactly the three rows missing its seven-point
ordinary support. -/
theorem squareOrderNine_threeHigh_secondProfile_nondefect_special_defect_eq_missing_rows
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
    (secondOrderDefectGraph G).neighborFinset y ∩ U1 =
      U1.filter fun b => (G.neighborFinset b ∩ F).card = 0 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  let D := secondOrderDefectGraph G
  let A := antipodalNeighbors G y ∩ B 1
  have hyBase := (Finset.mem_sdiff.mp hy).1
  have hF7 : F.card = 7 :=
    squareOrderNine_threeHigh_secondProfile_nondefect_special_support_card_seven
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  have hanti :=
    squareOrderNine_threeHigh_secondProfile_antipodal_fiber_eq_missing_rows
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy hF7
  dsimp only at hanti
  change A = U1.filter fun b => (G.neighborFinset b ∩ F).card = 0 at hanti
  rw [← hanti]
  ext b
  constructor
  · intro hbD
    have hbParts := Finset.mem_inter.mp hbD
    have hbU := Finset.mem_sdiff.mp hbParts.2
    have hDyb := (D.mem_neighborFinset y b).mp hbParts.1
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj y b at hDyb
    rcases hDyb with hantiY | htf
    · exact Finset.mem_inter.mpr ⟨
        (antipodalGraph_adj G y b).mp hantiY, hbU.1⟩
    · have hyb := ((mem_triangleFreeNeighbors G y b).mp
          ((triangleFreeEdgeGraph_adj G y b).mp htf)).1
      exfalso
      exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
        G hfree hhigh hx (Finset.mem_inter.mp hyBase).2 hbU.1
          ((G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyBase).1)) hyb
  · intro hbA
    have hbParts := Finset.mem_inter.mp hbA
    have hfiber :=
      squareOrderNine_threeHigh_secondProfile_special_antipodal_binOne_fiber
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyBase hbA
    dsimp only at hfiber
    exact Finset.mem_inter.mpr ⟨
      (D.mem_neighborFinset y b).mpr (Or.inl
        ((antipodalGraph_adj G y b).mpr hbParts.1)),
      Finset.mem_sdiff.mpr ⟨hbParts.2, hfiber.1⟩⟩
end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_row_mass_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_row_center_weight_sums
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_row_zero_centers
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_neighbor_center_partition
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_equation
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_weighted_row_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_special_marked_center_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_aligned_weighted_row_branches
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_pair_defect_three
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_pair_pattern
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_pair_row_triple_completion_count
#print axioms Erdos85.squareOrderNine_pair_pattern_mem_comm
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_residual_neighbor_blocks_disjoint
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exceptional_row_exact_cardinalities
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exceptional_pair_reciprocity
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_residual_block_avoids_core
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_actual_pair_pattern_mem_allowed
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_pair_marked_defect_sum_odd
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_triple_marked_defect_sum_even
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_marked_common_eq_support_hit
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_marked_support_hit_or_defect
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_marked_support_internal_defects_odd
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_marked_support_external_defects_even
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_marked_support_fortyTwo_five_ledger
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_common_center_partition
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_defect_iff_no_centers
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_unmarked_three_way_resolution
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_resolution
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exceptional_residualBlocks_eq_coreComplement
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exceptional_block_partition_cardinalities
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_residual_core_trace_zero
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_incidence_residual_gram_zero
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_core_resolved_rows_card
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_mixed_column_counts
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_defect_mass_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_nondefect_special_support_card_seven
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_nondefect_special_defect_eq_missing_rows
#print axioms Erdos85.weighted_row_arithmetic_forces_pair_defect_three
