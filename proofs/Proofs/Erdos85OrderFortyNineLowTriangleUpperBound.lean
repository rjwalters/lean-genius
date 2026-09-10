import Proofs.Erdos85OrderFortyNineHighIncidenceCensus

/-! The actual graph upper budget for all-low local triangle incidence. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Summing the local matching budget charges eight high incidences and
three removed low-vertex slots per high vertex. -/
theorem orderFortyNine_lowLow_sum_add_eleven_high_le_147
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (∑ x ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G x) +
      11 * (orderFortyNineHighVertices G).card ≤ 147 := by
  classical
  let L := orderFortyNineLowVertices G
  let H := orderFortyNineHighVertices G
  let t := fun x => (G.neighborFinset x ∩ H).card
  have hlow {x : V} (hx : x ∈ L) : G.degree x = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard x with h | h
    · exact h
    · exact ((Finset.mem_sdiff.mp hx).2 (by simp [orderFortyNineHighVertices, h])).elim
  have ht : ∀ x ∈ L, t x ≤ 3 := by
    intro x hx
    exact orderFortyNine_highNeighborCount_le_three G hfree hmin hcard (hlow hx)
  have hc := finset_census_le_three L t ht
  have hg := orderFortyNine_highIncidence_census G hfree hmin hcard
  change L.card = orderFortyNineHighIncidenceCount G 0 +
      orderFortyNineHighIncidenceCount G 1 + orderFortyNineHighIncidenceCount G 2 +
      orderFortyNineHighIncidenceCount G 3 ∧
    (∑ x ∈ L, t x) = orderFortyNineHighIncidenceCount G 1 +
      2 * orderFortyNineHighIncidenceCount G 2 + 3 * orderFortyNineHighIncidenceCount G 3 ∧ _ at hc
  have hs : (∑ x ∈ L, t x) = 8 * H.card := hc.2.1.trans hg.2.1
  have hsize : L.card + H.card = 49 := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H)
    simpa [L, orderFortyNineLowVertices, H, hcard] using hh
  have hb : (∑ x ∈ L, (t x + orderFortyNineLowLowLocalEdgeCount G x)) ≤
      ∑ _x ∈ L, (3 : ℕ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact orderFortyNine_high_add_lowLow_le_three G hfree hmin hcard (hlow hx)
  rw [Finset.sum_add_distrib, hs] at hb
  simp only [Finset.sum_const, smul_eq_mul] at hb
  change (∑ x ∈ L, orderFortyNineLowLowLocalEdgeCount G x) + 11 * H.card ≤ 147
  omega
end Erdos85
