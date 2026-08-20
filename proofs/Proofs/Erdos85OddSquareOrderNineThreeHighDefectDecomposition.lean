import Proofs.Erdos85OddSquareOrderNineThreeHighDefectQuotient

/-! # Pointwise defect structure in the q = 9 three-high profiles

Node: B.3 / GAP B-CLASSIFY.  The exact quotient census is sharpened to
pointwise neighbor types on the rare highest-incidence bins.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Pointwise version of the q=9 low-bin quotient ledger. -/
theorem squareOrderNine_lowIncidenceBin_pointwise_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    {i : ℕ} {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G i) :
    let H := squareOrderHighVertices G 9
    let D := secondOrderDefectGraph G
    let k := squareOrderHighIncidenceCount G 9
    D.degree x = 8 - i ∧
      (∑ y ∈ D.neighborFinset x, k y) = H.card - i := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G 9
  have hxlow : G.degree x = 9 := by
    have hxL := (Finset.mem_filter.mp hx).1
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hxL).2
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard x with hlo | hhi
    · exact hlo
    · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hki : k x = i := (Finset.mem_filter.mp hx).2
  have hd := squareOrder_defectDegree_add_highIncidence_eq_pred
    G hfree (by norm_num) hmin hcover hcard hxlow
  have hw := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
    G hfree (by norm_num) hmin hcard hxlow
  change D.degree x + k x = 8 at hd
  change (∑ y ∈ D.neighborFinset x, k y) + k x = H.card at hw
  rw [hki] at hd hw
  exact ⟨Nat.eq_sub_of_add_eq hd, Nat.eq_sub_of_add_eq hw⟩

/-- In the `(54,24,3,0,0)` three-high profile, each of the three bin-two
vertices has exactly five bin-zero and one bin-one defect neighbors, and no
bin-two defect neighbor. -/
theorem squareOrderNine_threeHigh_firstProfile_binTwo_neighbors
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
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 1 ∧
      (D.neighborFinset x ∩ B 2).card = 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hb3 : (B 3).card = 0 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : (B 4).card = 0 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 4) (by omega), hc4]
  have hB3 : B 3 = ∅ := Finset.card_eq_zero.mp hb3
  have hB4 : B 4 = ∅ := Finset.card_eq_zero.mp hb4
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
  change D.degree x = 8 - 2 ∧
    (∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y) = 3 - 2 at hpnt
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
  change (D.neighborFinset x ∩ B 0).card = 5 ∧
    (D.neighborFinset x ∩ B 1).card = 1 ∧
    (D.neighborFinset x ∩ B 2).card = 0
  omega

/-- In the `(53,27,0,1,0)` three-high profile, the unique bin-three vertex
has five bin-zero defect neighbors and no defect neighbor in bins one or
three. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_neighbors
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
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 0 ∧
      (D.neighborFinset x ∩ B 3).card = 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hb2 : (B 2).card = 0 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 2) (by omega), hc2]
  have hb3 : (B 3).card = 1 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : (B 4).card = 0 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 4) (by omega), hc4]
  have hB2 : B 2 = ∅ := Finset.card_eq_zero.mp hb2
  have hB4 : B 4 = ∅ := Finset.card_eq_zero.mp hb4
  have hself : (D.neighborFinset x ∩ B 3).card = 0 := by
    rw [Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hyD hyB
    have hyx : y = x := Finset.card_le_one.mp (by omega) y hyB x hx
    subst y
    exact D.loopless.irrefl x (by simpa [SimpleGraph.mem_neighborFinset] using hyD)
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
  change D.degree x = 8 - 3 ∧
    (∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y) = 3 - 3 at hpnt
  norm_num at hpnt
  have hweight :
      (∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    exact hpnt.2 y ((D.mem_neighborFinset x y).mp hy)
  have hbin1 : (D.neighborFinset x ∩ B 1).card = 0 := by
    rw [Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hyD hyB
    have hk0 := hpnt.2 y ((D.mem_neighborFinset x y).mp hyD)
    have hk1 : squareOrderHighIncidenceCount G 9 y = 1 :=
      (Finset.mem_filter.mp hyB).2
    omega
  have hpart := squareOrderNine_defectNeighbor_bin_partition
    G hfree hmin hcard hp x
  dsimp only at hpart
  change
    (∑ j ∈ Finset.range 5, (D.neighborFinset x ∩ B j).card) = D.degree x ∧
      (∑ j ∈ Finset.range 5, j * (D.neighborFinset x ∩ B j).card) =
        ∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y at hpart
  rw [hpnt.1, hweight] at hpart
  norm_num [Finset.sum_range_succ] at hpart
  rw [hB2, hB4] at hpart
  norm_num at hpart
  change (D.neighborFinset x ∩ B 0).card = 5 ∧
    (D.neighborFinset x ∩ B 1).card = 0 ∧
    (D.neighborFinset x ∩ B 3).card = 0
  exact ⟨by omega, hbin1, hself⟩

end


end Erdos85

#print axioms Erdos85.squareOrderNine_lowIncidenceBin_pointwise_ledger
#print axioms Erdos85.squareOrderNine_threeHigh_firstProfile_binTwo_neighbors
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_neighbors
