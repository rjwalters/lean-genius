import Proofs.Erdos85OddSquareOrderNineSmallHighIncidenceCensus
import Proofs.Erdos85OddSquareOrderNineIncidenceQuotientArithmetic

/-! # Exact defect decomposition in the q=9 one-high horn

Node: B.3 / GAP B-CLASSIFY.  The unique scalar profile at `h=1` is lifted
to an exact pointwise two-bin structure for the defect graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- With one high vertex, the low defect graph has 70 zero-incidence and ten
one-incidence vertices.  Every zero-bin vertex has seven zero-bin and one
one-bin defect neighbors; every one-bin vertex has seven zero-bin and no
one-bin defect neighbors. -/
theorem squareOrderNine_oneHigh_defect_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 1) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (B 0).card = 70 ∧ (B 1).card = 10 ∧
      (∀ x ∈ B 0,
        (D.neighborFinset x ∩ B 0).card = 7 ∧
        (D.neighborFinset x ∩ B 1).card = 1) ∧
      (∀ x ∈ B 1,
        (D.neighborFinset x ∩ B 0).card = 7 ∧
        (D.neighborFinset x ∩ B 1).card = 0) := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G 9
  let B := squareOrderNineLowIncidenceBin G
  have hprofile := squareOrderNine_highIncidence_profile_of_one_high
    G hcard hp hhigh
  dsimp only at hprofile
  have hbzero := squareOrderNine_lowIncidenceBin_zero_card_add_high_card G hp
  have hb0 : (B 0).card = 70 := by
    change (squareOrderNineLowIncidenceBin G 0).card = 70
    rw [hhigh, hprofile.1] at hbzero
    omega

  have hb1 : (B 1).card = 10 := by
    change (squareOrderNineLowIncidenceBin G 1).card = 10
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (by omega), hprofile.2.1]
  have hb2 : (B 2).card = 0 := by
    change (squareOrderNineLowIncidenceBin G 2).card = 0
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (by omega), hprofile.2.2.1]
  have hb3 : (B 3).card = 0 := by
    change (squareOrderNineLowIncidenceBin G 3).card = 0
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (by omega), hprofile.2.2.2.1]
  have hb4 : (B 4).card = 0 := by
    change (squareOrderNineLowIncidenceBin G 4).card = 0
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (by omega), hprofile.2.2.2.2]
  have hB2 : B 2 = ∅ := Finset.card_eq_zero.mp hb2
  have hB3 : B 3 = ∅ := Finset.card_eq_zero.mp hb3
  have hB4 : B 4 = ∅ := Finset.card_eq_zero.mp hb4
  change squareOrderNineLowIncidenceBin G 2 = ∅ at hB2
  change squareOrderNineLowIncidenceBin G 3 = ∅ at hB3
  change squareOrderNineLowIncidenceBin G 4 = ∅ at hB4
  refine ⟨hb0, hb1, ?_, ?_⟩
  · intro x hx
    have hpart := squareOrderNine_defectNeighbor_bin_partition
      G hfree hmin hcard hp x
    dsimp only at hpart
    have hxdeg : D.degree x = 8 := by
      have hpdeg := squareOrder_defectDegree_add_highIncidence_eq_pred
        G hfree (by norm_num) hmin hcover hcard
        (by
          have hxlow := (Finset.mem_filter.mp hx).1
          have hxnot := (Finset.mem_sdiff.mp hxlow).2
          rcases hp.degree_dichotomy x with h | h
          · exact h
          · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, h⟩)).elim)
      change D.degree x + k x = 8 at hpdeg
      have hkx : k x = 0 := (Finset.mem_filter.mp hx).2
      omega
    have hxweight := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree (by norm_num) hmin hcard
      (by
        have hxlow := (Finset.mem_filter.mp hx).1
        have hxnot := (Finset.mem_sdiff.mp hxlow).2
        rcases hp.degree_dichotomy x with h | h
        · exact h
        · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, h⟩)).elim)
    change (∑ y ∈ D.neighborFinset x, k y) + k x = H.card at hxweight
    have hkx : k x = 0 := (Finset.mem_filter.mp hx).2
    change H.card = 1 at hhigh
    rw [hkx, hhigh] at hxweight
    change (secondOrderDefectGraph G).degree x = 8 at hxdeg
    change (∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      squareOrderHighIncidenceCount G 9 y) = 1 at hxweight
    norm_num [Finset.sum_range_succ] at hpart
    rw [hB2, hB3, hB4] at hpart
    simp only [Finset.inter_empty, Finset.card_empty, Nat.add_zero,
      Nat.mul_zero] at hpart
    omega
  · intro x hx
    have hpart := squareOrderNine_defectNeighbor_bin_partition
      G hfree hmin hcard hp x
    dsimp only at hpart
    have hxlow : G.degree x = 9 := by
      have hxL := (Finset.mem_filter.mp hx).1
      have hxnot := (Finset.mem_sdiff.mp hxL).2
      rcases hp.degree_dichotomy x with h | h
      · exact h
      · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, h⟩)).elim
    have hxdegEq := squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree (by norm_num) hmin hcover hcard hxlow
    change D.degree x + k x = 8 at hxdegEq
    have hkx : k x = 1 := (Finset.mem_filter.mp hx).2
    have hxweight := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree (by norm_num) hmin hcard hxlow
    change (∑ y ∈ D.neighborFinset x, k y) + k x = H.card at hxweight
    change H.card = 1 at hhigh
    rw [hkx, hhigh] at hxweight
    have hxdeg : (secondOrderDefectGraph G).degree x = 7 := by
      change (secondOrderDefectGraph G).degree x +
        squareOrderHighIncidenceCount G 9 x = 8 at hxdegEq
      change squareOrderHighIncidenceCount G 9 x = 1 at hkx
      omega
    have hxweight0 : (∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
        squareOrderHighIncidenceCount G 9 y) = 0 := by
      change (∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
        squareOrderHighIncidenceCount G 9 y) + 1 = 1 at hxweight
      omega
    norm_num [Finset.sum_range_succ] at hpart
    rw [hB2, hB3, hB4] at hpart
    simp only [Finset.inter_empty, Finset.card_empty, Nat.add_zero,
      Nat.mul_zero] at hpart
    omega

/-- The ten one-incidence vertices canonically partition the seventy
zero-incidence vertices by their defect neighborhoods, into ten blocks of
cardinality seven. -/
theorem squareOrderNine_oneHigh_defect_block_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 1) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let block := fun y => D.neighborFinset y ∩ B 0
    (∀ y ∈ B 1, (block y).card = 7) ∧
      (∀ y ∈ B 1, ∀ z ∈ B 1, y ≠ z → Disjoint (block y) (block z)) ∧
      (B 1).biUnion block = B 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let block := fun y => D.neighborFinset y ∩ B 0
  have hdec := squareOrderNine_oneHigh_defect_decomposition
    G hfree hmin hcover hcard hp hhigh
  dsimp only at hdec
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact (hdec.2.2.2 y hy).1
  · intro y hy z hz hyz
    rw [Finset.disjoint_left]
    intro x hxy hxz
    have hxB0 : x ∈ B 0 := (Finset.mem_inter.mp hxy).2
    have hyNeighbor : y ∈ D.neighborFinset x := by
      have h := (Finset.mem_inter.mp hxy).1
      exact (D.mem_neighborFinset x y).mpr
        ((D.mem_neighborFinset y x).mp h).symm
    have hzNeighbor : z ∈ D.neighborFinset x := by
      have h := (Finset.mem_inter.mp hxz).1
      exact (D.mem_neighborFinset x z).mpr
        ((D.mem_neighborFinset z x).mp h).symm
    have hyMem : y ∈ D.neighborFinset x ∩ B 1 :=
      Finset.mem_inter.mpr ⟨hyNeighbor, hy⟩
    have hzMem : z ∈ D.neighborFinset x ∩ B 1 :=
      Finset.mem_inter.mpr ⟨hzNeighbor, hz⟩
    have hcardOne : (D.neighborFinset x ∩ B 1).card = 1 :=
      (hdec.2.2.1 x hxB0).2
    have heq := Finset.card_le_one.mp (by omega :
      (D.neighborFinset x ∩ B 1).card ≤ 1) y hyMem z hzMem
    exact hyz heq
  · ext x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (Finset.mem_inter.mp hxy).2
    · intro hx
      have hcardOne : (D.neighborFinset x ∩ B 1).card = 1 :=
        (hdec.2.2.1 x hx).2
      have hpos : 0 < (D.neighborFinset x ∩ B 1).card := by omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      have hy' := Finset.mem_inter.mp hy
      refine ⟨y, hy'.2, ?_⟩
      refine Finset.mem_inter.mpr ⟨?_, hx⟩
      exact (D.mem_neighborFinset y x).mpr
        ((D.mem_neighborFinset x y).mp hy'.1).symm

end

end Erdos85

#print axioms Erdos85.squareOrderNine_oneHigh_defect_decomposition
#print axioms Erdos85.squareOrderNine_oneHigh_defect_block_partition
