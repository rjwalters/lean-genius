import Proofs.Erdos85OrderFortyNineHighPartnerBound
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus
import Proofs.Erdos85BranchDeficitSymmetry

/-!
# Weighted incidence in the order-49 defect graph

The perfect-code identity for high neighborhoods has a useful pointwise
consequence.  Weight each low vertex by its number of high neighbors.  The
sum of these weights over the defect neighbors of a low vertex is the number
of high vertices not adjacent to it.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Pointwise weighted defect identity.**  For a low vertex `y`, its high
incidence together with the total high incidence of its defect neighbors is
the total number of high vertices.  In matrix notation, if `B` is the
high--low incidence matrix, `D` the low defect adjacency matrix, and
`k = Bᵀ 1`, this is `(D + I) k = h 1`. -/
theorem orderFortyNine_sum_highIncidence_over_defectNeighbors_add_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {y : V}
    (hy : G.degree y = 7) :
    (∑ x ∈ (secondOrderDefectGraph G).neighborFinset y,
        (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) +
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card =
        (orderFortyNineHighVertices G).card := by
  let D := secondOrderDefectGraph G
  let H := orderFortyNineHighVertices G
  have hswap := sum_card_neighbor_inter_comm G (D.neighborFinset y) H
  have hterm : ∀ v ∈ H,
      (G.neighborFinset v ∩ D.neighborFinset y).card =
        if G.Adj v y then 0 else 1 := by
    intro v hv
    have hv8 : G.degree v = 8 := (Finset.mem_filter.mp hv).2
    exact orderFortyNine_card_highNeighbors_inter_defectNeighbors
      G hfree hmin hcard hv8 hy
  have hsum :
      (∑ x ∈ D.neighborFinset y,
          (G.neighborFinset x ∩ H).card) =
        (H \ G.neighborFinset y).card := by
    rw [hswap]
    calc
      (∑ v ∈ H, (G.neighborFinset v ∩ D.neighborFinset y).card) =
          ∑ v ∈ H, if G.Adj v y then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hterm v hv
      _ = (H \ G.neighborFinset y).card := by
        have hbool : ∀ v : V,
            (if G.Adj v y then 0 else 1) =
              (if ¬ G.Adj y v then 1 else 0) := by
          intro v
          by_cases hvy : G.Adj v y
          · have hyv : G.Adj y v := by simpa [G.adj_comm] using hvy
            simp [hvy, hyv]
          · have hyv : ¬ G.Adj y v := by simpa [G.adj_comm] using hvy
            simp [hvy, hyv]
        simp_rw [hbool]
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext v
        simp [SimpleGraph.mem_neighborFinset]
  rw [hsum, Finset.card_sdiff]
  change H.card - (G.neighborFinset y ∩ H).card +
      (G.neighborFinset y ∩ H).card = H.card
  exact Nat.sub_add_cancel (Finset.card_le_card Finset.inter_subset_right)

/-- With nine high vertices, every low vertex and its defect neighbors carry
total high-incidence weight nine. -/
theorem orderFortyNine_sum_highIncidence_over_defectNeighbors_eq_nine_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) {y : V}
    (hy : G.degree y = 7) :
    (∑ x ∈ (secondOrderDefectGraph G).neighborFinset y,
        (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) =
      9 - (G.neighborFinset y ∩ orderFortyNineHighVertices G).card := by
  have hpoint :=
    orderFortyNine_sum_highIncidence_over_defectNeighbors_add_self
      G hfree hmin hcard hy
  rw [hHigh] at hpoint
  omega

/-- The first of the five numerical `h=9` incidence profiles cannot occur.
If every low high-incidence is zero or two, the weighted sum over every
defect neighborhood is even.  At a zero-incidence low vertex, however, the
pointwise weighted identity says that this sum is nine. -/
theorem orderFortyNine_not_highIncidence_profile_nine_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    ¬ (orderFortyNineHighIncidenceCount G 0 = 4 ∧
       orderFortyNineHighIncidenceCount G 1 = 0 ∧
       orderFortyNineHighIncidenceCount G 2 = 36 ∧
       orderFortyNineHighIncidenceCount G 3 = 0) := by
  let D := secondOrderDefectGraph G
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  rintro ⟨hn0, hn1, _hn2, hn3⟩
  have hn0' : (L.filter fun x => k x = 0).card = 4 := by
    simpa [L, k, H, orderFortyNineHighIncidenceCount] using hn0
  have hn1' : (L.filter fun x => k x = 1) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [L, k, H, orderFortyNineHighIncidenceCount] using hn1
  have hn3' : (L.filter fun x => k x = 3) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [L, k, H, orderFortyNineHighIncidenceCount] using hn3
  have hypos : 0 < (L.filter fun x => k x = 0).card := by omega
  rcases Finset.card_pos.mp hypos with ⟨y, hy⟩
  have hyL : y ∈ L := (Finset.mem_filter.mp hy).1
  have hky : k y = 0 := (Finset.mem_filter.mp hy).2
  have hy7 : G.degree y = 7 := by
    have hynot : y ∉ H := (Finset.mem_sdiff.mp hyL).2
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y with hy7 | hy8
    · exact hy7
    · exact (hynot (by simp [H, orderFortyNineHighVertices, hy8])).elim
  have hneighborLow : ∀ x ∈ D.neighborFinset y, x ∈ L := by
    intro x hxD
    have hDxy : D.Adj x y := by
      simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hxD
    have hx7 : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · have hxDzero : D.degree x = 0 :=
          (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
            G hfree hmin hcard hx8).1
        have hxDempty : D.neighborFinset x = ∅ := by
          rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hxDzero]
        have : y ∈ D.neighborFinset x := by
          simpa [SimpleGraph.mem_neighborFinset] using hDxy
        rw [hxDempty] at this
        exact (Finset.notMem_empty y this).elim
    have hxnot : x ∉ H := by
      intro hxH
      have hx8 : G.degree x = 8 := (Finset.mem_filter.mp hxH).2
      omega
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxnot⟩
  have hkeven : ∀ x ∈ D.neighborFinset y, Even (k x) := by
    intro x hxD
    have hxL := hneighborLow x hxD
    have hx7 : G.degree x = 7 := by
      have hxnot : x ∉ H := (Finset.mem_sdiff.mp hxL).2
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · exact (hxnot (by simp [H, orderFortyNineHighVertices, hx8])).elim
    have hk_le : k x ≤ 3 := by
      simpa [k, H] using orderFortyNine_highNeighborCount_le_three
        G hfree hmin hcard hx7
    have hk1 : k x ≠ 1 := by
      intro hkx
      have : x ∈ L.filter fun z => k z = 1 :=
        Finset.mem_filter.mpr ⟨hxL, hkx⟩
      rw [hn1'] at this
      exact Finset.notMem_empty x this
    have hk3 : k x ≠ 3 := by
      intro hkx
      have : x ∈ L.filter fun z => k z = 3 :=
        Finset.mem_filter.mpr ⟨hxL, hkx⟩
      rw [hn3'] at this
      exact Finset.notMem_empty x this
    rcases (show k x = 0 ∨ k x = 2 by omega) with hk0 | hk2
    · exact ⟨0, by simp [hk0]⟩
    · exact ⟨1, by simp [hk2]⟩
  have hsumEven : Even (∑ x ∈ D.neighborFinset y, k x) := by
    exact Finset.even_sum _ fun x hx => hkeven x hx
  have hsumNine : (∑ x ∈ D.neighborFinset y, k x) = 9 := by
    have hpoint :=
      orderFortyNine_sum_highIncidence_over_defectNeighbors_eq_nine_sub
        G hfree hmin hcard hHigh hy7
    simpa [D, k, H, hky] using hpoint
  rw [hsumNine] at hsumEven
  norm_num at hsumEven

/-- Consequently only four of the five moment-census profiles survive when
there are nine high vertices. -/
theorem orderFortyNine_highIncidence_profile_of_nine_high_reduced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    let n := orderFortyNineHighIncidenceCount G
    (n 0 = 3 ∧ n 1 = 3 ∧ n 2 = 33 ∧ n 3 = 1) ∨
    (n 0 = 2 ∧ n 1 = 6 ∧ n 2 = 30 ∧ n 3 = 2) ∨
    (n 0 = 1 ∧ n 1 = 9 ∧ n 2 = 27 ∧ n 3 = 3) ∨
    (n 0 = 0 ∧ n 1 = 12 ∧ n 2 = 24 ∧ n 3 = 4) := by
  dsimp only
  rcases orderFortyNine_highIncidence_profile_of_nine_high
      G hfree hmin hcard hHigh with hp | hp | hp | hp | hp
  · exact (orderFortyNine_not_highIncidence_profile_nine_zero
      G hfree hmin hcard hHigh hp).elim
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hp))

end

end Erdos85
