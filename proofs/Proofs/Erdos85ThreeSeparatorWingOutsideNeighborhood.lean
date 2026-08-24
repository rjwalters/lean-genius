import Proofs.Erdos85ThreeSeparatorEndpointWingMatching

/-! # Exact outside neighborhoods of endpoint wing points -/

open Finset SimpleGraph

namespace Erdos85

/-- A q-regular vertex with q-2 neighbors in Y and two known distinct
neighbors outside Y has exactly those two outside neighbors. -/
theorem neighborFinset_sdiff_eq_pair_of_inside_card_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r x w : V) (Y : Finset V) (q : ℕ) (hq : 2 ≤ q)
    (hdeg : G.degree r = q)
    (hinside : (G.neighborFinset r ∩ Y).card = q - 2)
    (hrx : G.Adj r x) (hrw : G.Adj r w)
    (hxY : x ∉ Y) (hwY : w ∉ Y) (hxw : x ≠ w) :
    G.neighborFinset r \ Y = {x, w} := by
  have houtCard : (G.neighborFinset r \ Y).card = 2 := by
    rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree, hdeg]
    have hinter : (Y ∩ G.neighborFinset r).card = q - 2 := by
      rw [Finset.inter_comm]
      exact hinside
    rw [hinter]
    omega
  have hpairSub : ({x, w} : Finset V) ⊆ G.neighborFinset r \ Y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzx | hzw
    · subst z
      exact Finset.mem_sdiff.mpr
        ⟨(G.mem_neighborFinset r x).mpr hrx, hxY⟩
    · subst z
      exact Finset.mem_sdiff.mpr
        ⟨(G.mem_neighborFinset r w).mpr hrw, hwY⟩
  have hpairCard : ({x, w} : Finset V).card = 2 := by simp [hxw]
  exact (Finset.eq_of_subset_of_card_le hpairSub (by rw [hpairCard, houtCard])).symm

/-- Family form used for the matched endpoint wings in B17W''''. -/
theorem wingPoints_outside_largeShore_eq_matched_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Rw Y : Finset V) (mate : V → V) (w : V) (q : ℕ) (hq : 2 ≤ q)
    (hdeg : ∀ r ∈ Rw, G.degree r = q)
    (hinside : ∀ r ∈ Rw, (G.neighborFinset r ∩ Y).card = q - 2)
    (hrmate : ∀ r ∈ Rw, G.Adj r (mate r))
    (hrw : ∀ r ∈ Rw, G.Adj r w)
    (hmateY : ∀ r ∈ Rw, mate r ∉ Y)
    (hwY : w ∉ Y) (hmatew : ∀ r ∈ Rw, mate r ≠ w) :
    ∀ r ∈ Rw, G.neighborFinset r \ Y = {mate r, w} := by
  intro r hr
  exact neighborFinset_sdiff_eq_pair_of_inside_card_sub_two
    G r (mate r) w Y q hq (hdeg r hr) (hinside r hr)
      (hrmate r hr) (hrw r hr) (hmateY r hr) hwY (hmatew r hr)

#print axioms neighborFinset_sdiff_eq_pair_of_inside_card_sub_two
#print axioms wingPoints_outside_largeShore_eq_matched_pair

end Erdos85
