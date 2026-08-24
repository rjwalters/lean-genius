import Proofs.Erdos85FinalDyadicNegativeHighEndpointCrossBlockGrid

/-!
# Half occupancy on the punctured second layer of an empty block

Around an empty center, every length-two endpoint other than the center is
nonexceptional: its shore occupancy is exactly half the degree.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If `e` is an empty center, `x∈N(e)`, and `z∈N(x)\{e}`, then `z` has
the middle final-dyadic occupancy `2^j`. -/
theorem finalDyadic_emptyCenter_puncturedSecondLayer_occupancy_eq_half
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e x z : V} (he : e ∈ emptyLineCenters G S)
    (hx : x ∈ G.neighborFinset e)
    (hz : z ∈ G.neighborFinset x) (hze : z ≠ e) :
    (G.neighborFinset z ∩ S).card = 2 ^ j := by
  have heOcc : (G.neighborFinset e ∩ S).card = 0 :=
    (mem_emptyLineCenters G S e).mp he
  have hxNotS : x ∉ S := by
    intro hxS
    have hxInter : x ∈ G.neighborFinset e ∩ S :=
      Finset.mem_inter.mpr ⟨hx, hxS⟩
    exact (Finset.card_ne_zero.mpr ⟨x, hxInter⟩) heOcc
  have hzNotFull : z ∉ fullLineCenters G S q := by
    intro hzFull
    have hzOcc := (mem_fullLineCenters G S q z).mp hzFull
    have hNzEq : G.neighborFinset z ∩ S = G.neighborFinset z := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [G.card_neighborFinset_eq_degree, hreg]
      omega
    have hxNz : x ∈ G.neighborFinset z :=
      (G.mem_neighborFinset z x).mpr
        ((G.mem_neighborFinset x z).mp hz).symm
    have hxInter : x ∈ G.neighborFinset z ∩ S := by
      rw [hNzEq]
      exact hxNz
    exact hxNotS (Finset.mem_inter.mp hxInter).2
  have hzNotEmpty : z ∉ emptyLineCenters G S := by
    intro hzEmpty
    have hezD := hemptyClique he hzEmpty hze.symm
    have hex : G.Adj e x := (G.mem_neighborFinset e x).mp hx
    have hzx : G.Adj z x :=
      ((G.mem_neighborFinset x z).mp hz).symm
    exact (not_secondOrderDefect_adj_of_commonNeighbor
      G hfree hze.symm hex hzx) hezD
  rcases finalDyadic_occupancy_trichotomy G hqa hreg S hdiv z with
    hzero | hhalf | hfull
  · exact (hzNotEmpty ((mem_emptyLineCenters G S z).mpr hzero)).elim
  · omega
  · exact (hzNotFull ((mem_fullLineCenters G S q z).mpr hfull)).elim

end


end Erdos85

#print axioms
  Erdos85.finalDyadic_emptyCenter_puncturedSecondLayer_occupancy_eq_half
