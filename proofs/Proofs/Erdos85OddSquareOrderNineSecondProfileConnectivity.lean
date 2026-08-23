import Proofs.Erdos85OrderNineNearRegularConnectivityCapstone
import Proofs.Erdos85OddSquareOrderNineNearRegularComponentCard
import Proofs.Erdos85OddSquareOrderNineNearRegularComponentBalance

/-! # Connectivity of the q=9 three-high second-profile defect core

This is the profile specialization of the graph-level near-regular
connectivity capstone.  The substantive shore partition and balance facts are
provided by the two component modules; the remaining proof identifies the
three high vertices and discharges their degree, independence, and defect
isolation properties.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the second q=9 three-high profile, the second-order defect graph
induced on the 78 low vertices is connected. -/
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
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (owner : V) (hownerB3 : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = ({h₁, h₂, h₃} : Finset V)) :
    ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V) \ squareOrderHighVertices G 9) : Set V)).Connected := by
  classical
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  have hOcard : ((Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V)).card = 78 := by
    rw [← hH, Finset.card_sdiff_of_subset (Finset.subset_univ H),
      Finset.card_univ, hcard, hhigh]
  have hownerO : owner ∈
      (Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V) := by
    rw [← hH]
    exact (Finset.mem_filter.mp hownerB3).1
  have hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9 := by
    intro x hx
    rcases hp.degree_dichotomy x with hlo | hhi
    · exact hlo
    · have hxH : x ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hhi⟩
      have hxTriple : x ∈ ({h₁, h₂, h₃} : Finset V) := by
        rw [← hH]
        exact hxH
      exact (hx hxTriple).elim
  have hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10 := by
    intro h hh
    have hhH : h ∈ H := by
      change h ∈ squareOrderHighVertices G 9
      rw [hH]
      exact hh
    exact (Finset.mem_filter.mp hhH).2
  have hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V) := by
    intro h hh
    rw [Finset.disjoint_left]
    intro x hxh hxH
    have hh' : h ∈ H := by
      change h ∈ squareOrderHighVertices G 9
      rw [hH]
      exact hh
    have hxH' : x ∈ H := by
      change x ∈ squareOrderHighVertices G 9
      rw [hH]
      exact hxH
    exact hp.high_independent hh' hxH' ((G.mem_neighborFinset h x).mp hxh)
  have hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅ := by
    intro h hh
    have hd : (secondOrderDefectGraph G).degree h = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree (by norm_num) hmin hcard (hdegHigh h hh)).1
    rw [← Finset.card_eq_zero,
      (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hd]
  have hconn := orderNineNearRegular_ordinaryDefect_connected_of_nonowner_shore_data
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ owner (B 0) (B 1)
      hOcard hownerO hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
      (fun S hSsub hownerS =>
        squareOrderNine_threeHigh_secondProfile_nonowner_shore_card
          G hp hc2 hc3 hc4 owner hownerB3 S (by simpa [hH] using hSsub) hownerS)
      (fun S hownerS hclosed =>
        squareOrderNine_threeHigh_secondProfile_nonowner_shore_balance
          G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 owner hownerB3 S
            hownerS (by simpa [hH] using hclosed))
  rw [hH]
  exact hconn

#print axioms squareOrderNine_threeHigh_secondProfile_ordinaryDefect_connected

end

end Erdos85
