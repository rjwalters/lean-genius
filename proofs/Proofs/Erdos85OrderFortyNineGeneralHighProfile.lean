import Proofs.Erdos85OrderFortyNinePBDClassification

/-!
# Universal high-neighborhood profile at order 49

The local incidence profile around a high vertex is governed by a single
parameter, the number of triple blocks through that high.  This formulation
works uniformly for every possible high count and replaces separate profile
enumerations for `h = 3,5,7,9`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Universal local PBD profile.**  Let `a i` be the number of neighbors
of a high vertex whose own high-support has size `i`, and let `h` be the
number of high vertices.  Then

`a₁ + h = a₃ + 9` and `a₂ + 2a₃ + 1 = h`.

Equivalently, with `t = a₃`, the profile is
`(a₁,a₂,a₃) = (t + 9 - h, h - 1 - 2t, t)`. -/
theorem orderFortyNine_highNeighborhood_general_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8) :
    let H := orderFortyNineHighVertices G
    let a := fun i => ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = i).card
    a 1 + H.card = a 3 + 9 ∧
      a 2 + 2 * a 3 + 1 = H.card := by
  dsimp only
  let H := orderFortyNineHighVertices G
  let k : V → ℕ := fun x => (orderFortyNineHighSupport G x).card
  let a0 := ((G.neighborFinset v).filter fun x => k x = 0).card
  let a1 := ((G.neighborFinset v).filter fun x => k x = 1).card
  let a2 := ((G.neighborFinset v).filter fun x => k x = 2).card
  let a3 := ((G.neighborFinset v).filter fun x => k x = 3).card
  change a1 + H.card = a3 + 9 ∧ a2 + 2 * a3 + 1 = H.card
  have hk : ∀ x ∈ G.neighborFinset v, k x ≤ 3 := by
    intro x hx
    have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp hx
    have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hvx
    simpa [k, orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three G hfree hmin hcard hx7
  have hcensus := finset_census_le_three (G.neighborFinset v) k hk
  change G.degree v = a0 + a1 + a2 + a3 ∧
      (∑ x ∈ G.neighborFinset v, k x) = a1 + 2 * a2 + 3 * a3 ∧
      (∑ x ∈ G.neighborFinset v, (k x) ^ 2) =
        a1 + 4 * a2 + 9 * a3 at hcensus
  have ha0 : a0 = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxmem := (Finset.mem_filter.mp hx).1
    have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp hxmem
    have hvH : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hvSupport : v ∈ orderFortyNineHighSupport G x := by
      apply Finset.mem_inter.mpr
      refine ⟨?_, hvH⟩
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hvx
    have hkpos : 0 < k x := Finset.card_pos.mpr ⟨v, hvSupport⟩
    exact hkpos.ne' (Finset.mem_filter.mp hx).2
  have hsum := orderFortyNine_sum_highIncidence_over_highNeighborhood
    G hfree hmin hcard hv
  change (∑ x ∈ G.neighborFinset v, k x) = H.card + 7 at hsum
  rw [hv, ha0, hsum] at hcensus
  omega

/-- The triple multiplicity at a high vertex is bounded uniformly by the
size of the high sector: `2a₃ + 1 ≤ h`. -/
theorem orderFortyNine_twice_tripleMultiplicity_add_one_le_highCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8) :
    2 * ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3).card + 1 ≤
        (orderFortyNineHighVertices G).card := by
  have hp := orderFortyNine_highNeighborhood_general_profile
    G hfree hmin hcard hv
  dsimp only at hp
  omega

/-- **Universal global PBD profile.**  Put `nᵢ` for the number of low
vertices with high-support size `i`, `h` for the number of highs, and
`t = n₃`.  The three moment equations reduce to the following identities:

* `2n₂ + 6t = h(h-1)` (pair coverage),
* `n₁ = h(9-h) + 3t`,
* `2n₀ = h² - 19h + 98 - 2t`.

They are stated without truncated subtraction, so they remain convenient in
all five possible high-count strata. -/
theorem orderFortyNine_highIncidence_general_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    let H := orderFortyNineHighVertices G
    let n := orderFortyNineHighIncidenceCount G
    2 * n 2 + 6 * n 3 + H.card = H.card * H.card ∧
      n 1 + H.card * H.card = 9 * H.card + 3 * n 3 ∧
      2 * n 0 + 2 * n 3 + 19 * H.card =
        H.card * H.card + 98 := by
  dsimp only
  let H := orderFortyNineHighVertices G
  let n := orderFortyNineHighIncidenceCount G
  change 2 * n 2 + 6 * n 3 + H.card = H.card * H.card ∧
    n 1 + H.card * H.card = 9 * H.card + 3 * n 3 ∧
    2 * n 0 + 2 * n 3 + 19 * H.card = H.card * H.card + 98
  have hcensus := orderFortyNine_highIncidence_census
    G hfree hmin hcard
  change n 0 + n 1 + n 2 + n 3 = 49 - H.card ∧
    n 1 + 2 * n 2 + 3 * n 3 = 8 * H.card ∧
    n 1 + 4 * n 2 + 9 * n 3 = H.card * (H.card + 7) at hcensus
  have hHle : H.card ≤ 9 := by
    simpa [H] using orderFortyNine_card_high_le_nine G hfree hmin hcard
  have hprod : H.card * (H.card + 7) =
      H.card * H.card + 7 * H.card := by ring
  rw [hprod] at hcensus
  have htotal : n 0 + n 1 + n 2 + n 3 + H.card = 49 := by
    omega
  omega

end

end Erdos85
