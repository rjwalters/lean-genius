import Proofs.Erdos85OrderNineNearRegularConnectivityCapstone
import Proofs.Erdos85OddSquareOrderNineNearRegularComponentBalance
import Proofs.Erdos85OddSquareOrderNineNearRegularComponentCard

/-! # Connectivity of the q=9 second-profile ordinary defect graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the q=9 three-high second profile, the second-order defect graph
induced on the 78 degree-nine vertices is connected. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinaryDefect_connected
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
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V) \ squareOrderHighVertices G 9) : Set V)).Connected := by
  classical
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let D := secondOrderDefectGraph G
  obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃, hH⟩ := Finset.card_eq_three.mp hhigh
  have hB3card : (B 3).card = 1 := by
    dsimp only [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  obtain ⟨owner, hownerB3⟩ : (B 3).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hownerO : owner ∈ (Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V) := by
    rw [← hH]
    exact (Finset.mem_filter.mp hownerB3).1
  have hOcard :
      ((Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V)).card = 78 := by
    rw [← hH]
    have hHsub : H ⊆ (Finset.univ : Finset V) := Finset.subset_univ H
    rw [Finset.card_sdiff_of_subset hHsub, Finset.card_univ, hcard]
    change H.card = 3 at hhigh
    omega
  have hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9 := by
    intro x hx
    have hxH : x ∉ H := by
      change x ∉ squareOrderHighVertices G 9
      rw [hH]
      exact hx
    rcases hp.degree_dichotomy x with hlo | hhi
    · exact hlo
    · exact (hxH (Finset.mem_filter.mpr ⟨Finset.mem_univ x, by norm_num at hhi ⊢; exact hhi⟩)).elim
  have hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10 := by
    intro h hh
    have hhH : h ∈ H := by
      change h ∈ squareOrderHighVertices G 9
      rw [hH]
      exact hh
    have := (Finset.mem_filter.mp hhH).2
    norm_num at this ⊢
    exact this
  have hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V) := by
    intro h hh
    rw [Finset.disjoint_left]
    intro y hyN hyH
    have hh' : h ∈ H := by
      change h ∈ squareOrderHighVertices G 9
      rw [hH]
      exact hh
    have hyH' : y ∈ H := by
      change y ∈ squareOrderHighVertices G 9
      rw [hH]
      exact hyH
    exact hp.high_independent hh' hyH'
      ((G.mem_neighborFinset h y).mp hyN)
  have hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      D.neighborFinset h = ∅ := by
    intro h hh
    have hd : D.degree h = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree (by norm_num) hmin hcard (by
          have := hdegHigh h hh
          omega)).1
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hd]
  rw [hH]
  apply orderNineNearRegular_ordinaryDefect_connected_of_nonowner_shore_data
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ owner (B 0) (B 1)
      hOcard hownerO hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
  · intro S hSsub hownerS
    apply squareOrderNine_threeHigh_secondProfile_nonowner_shore_card
      G hp hc2 hc3 hc4 owner hownerB3 S
    · simpa [hH] using hSsub
    · exact hownerS
  · intro S hownerS hclosed
    apply squareOrderNine_threeHigh_secondProfile_nonowner_shore_balance
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 owner hownerB3 S hownerS
    simpa [hH] using hclosed

#print axioms squareOrderNine_threeHigh_secondProfile_ordinaryDefect_connected

end

end Erdos85
