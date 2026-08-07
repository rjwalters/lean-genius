import Proofs.Erdos85OrderFortyNineLowNeighborhoodPartition

/-!
# Odd high-incidence fibers at order 49

The graph-neighborhood partition law has a parity shadow: when the high
sector has odd cardinality, every low vertex has an odd number of neighbors
whose own high-incidence is odd.  This packages the invariant used by the
remaining `h=9` profile analysis without choosing a numerical profile.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Vertices incident with an odd number of high vertices. -/
def orderFortyNineOddHighIncidenceVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun x =>
    Odd ((G.neighborFinset x ∩ orderFortyNineHighVertices G).card)

/-- If the number of high vertices is odd, every low neighborhood meets the
odd-incidence fiber in odd cardinality. -/
theorem orderFortyNine_odd_card_neighbors_oddHighIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHighOdd : Odd (orderFortyNineHighVertices G).card) {y : V}
    (hy : G.degree y = 7) :
    Odd ((G.neighborFinset y ∩
      orderFortyNineOddHighIncidenceVertices G).card) := by
  let k : V → ℕ := fun x =>
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card
  have hsum := orderFortyNine_sum_highIncidence_over_lowNeighborhood
    G hfree hmin hcard hy
  change (∑ x ∈ G.neighborFinset y, k x) =
    (orderFortyNineHighVertices G).card at hsum
  have hoddSum : Odd (∑ x ∈ G.neighborFinset y, k x) := by
    rw [hsum]
    exact hHighOdd
  rw [Finset.odd_sum_iff_odd_card_odd] at hoddSum
  convert hoddSum using 1
  congr 1
  ext x
  simp [orderFortyNineOddHighIncidenceVertices, k]

/-- At nine highs, every low vertex has a positive odd number of neighbors
in the odd-incidence fiber. -/
theorem orderFortyNine_card_neighbors_oddHighIncidence_pos_of_nine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) {y : V}
    (hy : G.degree y = 7) :
    0 < (G.neighborFinset y ∩
      orderFortyNineOddHighIncidenceVertices G).card := by
  have hodd := orderFortyNine_odd_card_neighbors_oddHighIncidence
    G hfree hmin hcard (by rw [hHigh]; norm_num) hy
  exact Nat.pos_of_ne_zero fun hzero => by
    rw [hzero] at hodd
    norm_num at hodd

/-- In every high neighborhood at `h=9`, the number of one-high lows equals
the number of three-high lows.  This is the local balance behind the
canonical block description of the remaining profiles. -/
theorem orderFortyNine_highNeighborhood_count_one_eq_count_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {v : V} (hv : G.degree v = 8) :
    ((G.neighborFinset v).filter fun x =>
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 1).card =
    ((G.neighborFinset v).filter fun x =>
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 3).card := by
  rcases orderFortyNine_highNeighborhood_profile_of_nine_high
      G hfree hmin hcard hHigh hv with hp | hp | hp | hp | hp
  all_goals
    dsimp only at hp
    omega

end

end Erdos85
