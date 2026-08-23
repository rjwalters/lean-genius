import Proofs.Erdos85OddSquareOrderNineNearRegularConnectivityTerminal
import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes

/-! # Component balance in the q=9 three-high second profile

This is the graph specialization of the generic `3 : 5` double count.  A
shore of the ordinary induced defect graph which omits the unique bin-three
vertex contains no exceptional bin-zero row: such a row is defect-adjacent
to that bin-three owner and relative closure would put the owner in the shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A relatively closed ordinary shore omitting the unique bin-three vertex
has exact bin balance `3 |B₀ ∩ S| = 5 |B₁ ∩ S|`. -/
theorem squareOrderNine_threeHigh_secondProfile_nonowner_shore_balance
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
    (owner : V) (hownerB3 : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S : Finset V)
    (hownerS : owner ∉ S)
    (hclosed : ∀ z ∈ S,
      (secondOrderDefectGraph G).neighborFinset z ∩
        ((Finset.univ : Finset V) \ squareOrderHighVertices G 9) ⊆ S) :
    3 * (squareOrderNineLowIncidenceBin G 0 ∩ S).card =
      5 * (squareOrderNineLowIncidenceBin G 1 ∩ S).card := by
  classical
  let D := secondOrderDefectGraph G
  let U := (Finset.univ : Finset V) \ squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  have hB3card : (B 3).card = 1 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hB3U : B 3 ⊆ U := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  apply three_mul_card_eq_five_mul_card_of_cross_degrees D (B 0 ∩ S) (B 1 ∩ S)
  · intro z hz
    have hzParts := Finset.mem_inter.mp hz
    have hzType :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hzParts.1
    dsimp only at hzType
    rcases hzType with hregular | hexceptional
    · have hinter : D.neighborFinset z ∩ (B 1 ∩ S) = D.neighborFinset z ∩ B 1 := by
        ext y
        simp only [Finset.mem_inter]
        constructor
        · exact fun hy => ⟨hy.1, hy.2.1⟩
        · intro hy
          have hyU : y ∈ U := (Finset.mem_filter.mp hy.2).1
          exact ⟨hy.1, hy.2,
            hclosed z hzParts.2
              (Finset.mem_inter.mpr ⟨hy.1, hyU⟩)⟩
      rw [hinter]
      exact hregular.2.1
    · exfalso
      have hnonempty : (D.neighborFinset z ∩ B 3).Nonempty := by
        apply Finset.card_pos.mp
        change 0 < ((secondOrderDefectGraph G).neighborFinset z ∩
          squareOrderNineLowIncidenceBin G 3).card
        rw [hexceptional.2.2]
        norm_num
      obtain ⟨w, hw⟩ := hnonempty
      have hwParts := Finset.mem_inter.mp hw
      have hwOwner : w = owner :=
        Finset.card_le_one.mp (by omega) w hwParts.2 owner hownerB3
      subst w
      have hownerU : owner ∈ U := hB3U hownerB3
      exact hownerS (hclosed z hzParts.2
        (Finset.mem_inter.mpr ⟨hwParts.1, hownerU⟩))
  · intro z hz
    have hzParts := Finset.mem_inter.mp hz
    have hzType := squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hzParts.1
    dsimp only at hzType
    have hinter : D.neighborFinset z ∩ (B 0 ∩ S) = D.neighborFinset z ∩ B 0 := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.1⟩
      · intro hy
        have hyU : y ∈ U := (Finset.mem_filter.mp hy.2).1
        exact ⟨hy.1, hy.2, hclosed z hzParts.2
          (Finset.mem_inter.mpr ⟨hy.1, hyU⟩)⟩
    rw [hinter]
    exact hzType.1

#print axioms squareOrderNine_threeHigh_secondProfile_nonowner_shore_balance

end

end Erdos85
