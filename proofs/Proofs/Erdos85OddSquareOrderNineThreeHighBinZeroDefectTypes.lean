import Proofs.Erdos85OddSquareOrderNineThreeHighTriangleCensus

/-! # Bin-zero defect types in the q = 9 three-high first profile

Node: B.3 / GAP B-CLASSIFY.  The 51 bin-zero vertices split pointwise into
types `(B₀,B₁,B₂)=(5,3,0)` and `(6,1,1)`.  Exactly fifteen vertices have the
second type, giving the precise reservoir reached by antipodal propagation
from the colored bin-one core.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every bin-zero vertex in the first three-high profile has defect-neighbor
type `(5,3,0)` or `(6,1,1)` across bins zero, one, and two. -/
theorem squareOrderNine_threeHigh_firstProfile_binZero_defect_neighbor_dichotomy
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 3 ∧
        (D.neighborFinset x ∩ B 2).card = 0) ∨
      ((D.neighborFinset x ∩ B 0).card = 6 ∧
        (D.neighborFinset x ∩ B 1).card = 1 ∧
        (D.neighborFinset x ∩ B 2).card = 1) := by
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
  change
    ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 3 ∧
        (D.neighborFinset x ∩ B 2).card = 0) ∨
      ((D.neighborFinset x ∩ B 0).card = 6 ∧
        (D.neighborFinset x ∩ B 1).card = 1 ∧
        (D.neighborFinset x ∩ B 2).card = 1)
  by_cases htwo : (D.neighborFinset x ∩ B 2).card = 0
  · left
    exact ⟨by omega, by omega, htwo⟩
  · right
    exact ⟨by omega, by omega, by omega⟩

/-- Exactly fifteen bin-zero vertices are adjacent in the defect graph to a
bin-two witness; equivalently, exactly fifteen have type `(6,1,1)`. -/
theorem squareOrderNine_threeHigh_firstProfile_special_binZero_card
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
    ((B 0).filter fun x => (D.neighborFinset x ∩ B 2).card = 1).card = 15 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 0).filter fun x =>
    ((secondOrderDefectGraph G).neighborFinset x ∩ B 2).card = 1
  have hB3 : B 3 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
  have he02 : squareOrderNineDefectBinEdgeCount G 0 2 = 15 := by
    rcases squareOrderNine_threeHigh_defectQuotient_census
        G hfree hmin hcover hcard hp hhigh with hfirst | hsecond
    · exact hfirst.2.2.1
    · have he03zero : squareOrderNineDefectBinEdgeCount G 0 3 = 0 := by
        simp [squareOrderNineDefectBinEdgeCount, B, hB3]
      omega
  have hpoint : ∀ x ∈ B 0,
      ((secondOrderDefectGraph G).neighborFinset x ∩ B 2).card = 0 ∨
        ((secondOrderDefectGraph G).neighborFinset x ∩ B 2).card = 1 := by
    intro x hx
    have ht :=
      squareOrderNine_threeHigh_firstProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc3 hc4 hx
    dsimp only at ht
    rcases ht with hregular | hspecial
    · exact Or.inl hregular.2.2
    · exact Or.inr hspecial.2.2
  change E.card = 15
  calc
    E.card = ∑ x ∈ B 0, if x ∈ E then 1 else 0 := by
      rw [Finset.card_eq_sum_ones]
      simp [E]
      congr 1
      ext x
      simp
    _ = ∑ x ∈ B 0,
        ((secondOrderDefectGraph G).neighborFinset x ∩ B 2).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases hpoint x hx with hzero | hone
      · have hxNotE : x ∉ E := by simp [E, hzero]
        simp [hxNotE, hzero]
      · have hxE : x ∈ E := by simp [E, hx, hone]
        simp [hxE, hone]
    _ = squareOrderNineDefectBinEdgeCount G 0 2 := by rfl
    _ = 15 := he02

/-- Every bin-zero vertex has at most one bin-two defect neighbor. -/
theorem squareOrderNine_threeHigh_firstProfile_binZero_binTwo_defect_card_le_one
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
    {y : V} (hy : y ∈ squareOrderNineLowIncidenceBin G 0) :
    ((secondOrderDefectGraph G).neighborFinset y ∩
      squareOrderNineLowIncidenceBin G 2).card ≤ 1 := by
  have ht :=
    squareOrderNine_threeHigh_firstProfile_binZero_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hy
  dsimp only at ht
  rcases ht with hregular | hspecial
  · omega
  · omega

/-- Each bin-two witness indexes exactly five vertices in the special
bin-zero reservoir. -/
theorem squareOrderNine_threeHigh_firstProfile_binTwo_binZero_fiber_card_eq_five
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 2) :
    ((secondOrderDefectGraph G).neighborFinset x ∩
      squareOrderNineLowIncidenceBin G 0).card = 5 := by
  exact (squareOrderNine_threeHigh_firstProfile_binTwo_neighbors
    G hfree hmin hcover hcard hp hhigh hc3 hc4 hx).1

/-- The five-point bin-zero defect fibers of distinct bin-two witnesses are
disjoint. -/
theorem squareOrderNine_threeHigh_firstProfile_binTwo_binZero_fibers_disjoint
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
    {x z : V}
    (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hz : z ∈ squareOrderNineLowIncidenceBin G 2)
    (hxz : x ≠ z) :
    Disjoint
      ((secondOrderDefectGraph G).neighborFinset x ∩
        squareOrderNineLowIncidenceBin G 0)
      ((secondOrderDefectGraph G).neighborFinset z ∩
        squareOrderNineLowIncidenceBin G 0) := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  rw [Finset.disjoint_left]
  intro y hyx hyz
  have hy0 : y ∈ B 0 := (Finset.mem_inter.mp hyx).2
  have hle :=
    squareOrderNine_threeHigh_firstProfile_binZero_binTwo_defect_card_le_one
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hy0
  have hxMem : x ∈ D.neighborFinset y ∩ B 2 :=
    Finset.mem_inter.mpr ⟨
      (D.mem_neighborFinset y x).mpr
        ((D.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyx).1).symm,
      hx⟩
  have hzMem : z ∈ D.neighborFinset y ∩ B 2 :=
    Finset.mem_inter.mpr ⟨
      (D.mem_neighborFinset y z).mpr
        ((D.mem_neighborFinset z y).mp (Finset.mem_inter.mp hyz).1).symm,
      hz⟩
  exact hxz (Finset.card_le_one.mp hle x hxMem z hzMem)

/-- The special bin-zero reservoir is exactly the union of the three
five-point defect fibers indexed by bin two. -/
theorem squareOrderNine_threeHigh_firstProfile_special_binZero_eq_biUnion_binTwo_fibers
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
    (B 0).filter (fun y => (D.neighborFinset y ∩ B 2).card = 1) =
      (B 2).biUnion fun x => D.neighborFinset x ∩ B 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  ext y
  constructor
  · intro hy
    have hyData := Finset.mem_filter.mp hy
    have hone : (D.neighborFinset y ∩ B 2).card = 1 := by
      simpa [D, B] using hyData.2
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
      0 < (D.neighborFinset y ∩ B 2).card)
    have hxData := Finset.mem_inter.mp hx
    rw [Finset.mem_biUnion]
    exact ⟨x, hxData.2, Finset.mem_inter.mpr ⟨
      (D.mem_neighborFinset x y).mpr
        ((D.mem_neighborFinset y x).mp hxData.1).symm,
      hyData.1⟩⟩
  · intro hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨x, hx2, hxy⟩ := hy
    have hxyData := Finset.mem_inter.mp hxy
    have hy0 : y ∈ B 0 := hxyData.2
    have hxMem : x ∈ D.neighborFinset y ∩ B 2 :=
      Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset y x).mpr
          ((D.mem_neighborFinset x y).mp hxyData.1).symm,
        hx2⟩
    have hpos : 0 < (D.neighborFinset y ∩ B 2).card :=
      Finset.card_pos.mpr ⟨x, hxMem⟩
    have hle :=
      squareOrderNine_threeHigh_firstProfile_binZero_binTwo_defect_card_le_one
        G hfree hmin hcover hcard hp hhigh hc3 hc4 hy0
    have hle' : (D.neighborFinset y ∩ B 2).card ≤ 1 := by
      simpa [D, B] using hle
    exact Finset.mem_filter.mpr ⟨hy0, by
      change (D.neighborFinset y ∩ B 2).card = 1
      omega⟩

end

end Erdos85

#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_binZero_defect_neighbor_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_firstProfile_special_binZero_card
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_binZero_binTwo_defect_card_le_one
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_binTwo_binZero_fiber_card_eq_five
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_binTwo_binZero_fibers_disjoint
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_special_binZero_eq_biUnion_binTwo_fibers
