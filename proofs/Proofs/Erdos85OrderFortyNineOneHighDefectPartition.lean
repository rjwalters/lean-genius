import Proofs.Erdos85OrderFortyNineDefectWeightedIncidence
import Proofs.Erdos85OrderFortyNineOneThreeHighProfile

/-!
# The one-high defect partition at order 49

When the degree-eight sector is a singleton, its eight low neighbors form an
independent side in the second-order defect graph.  Every other low vertex
has exactly one defect neighbor in that side.  This is the small equitable
partition needed by a symmetry-aware terminal search.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the one-high stratum, let `A` be the low vertices adjacent to the
unique high vertex.  Then `|A|=8`; a low vertex `y` has defect degree
`6-k(y)` and exactly `1-k(y)` defect neighbors in `A`. -/
theorem orderFortyNine_oneHigh_defect_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1) :
    let H := orderFortyNineHighVertices G
    let L := orderFortyNineLowVertices G
    let D := secondOrderDefectGraph G
    let k := fun x => (G.neighborFinset x ∩ H).card
    let A := L.filter fun x => k x = 1
    let B := L.filter fun x => k x = 0
    A.card = 8 ∧ B.card = 40 ∧ ∀ y ∈ L,
      D.degree y = 6 - k y ∧
      (D.neighborFinset y ∩ A).card = 1 - k y := by
  dsimp only
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let D := secondOrderDefectGraph G
  let k := fun x => (G.neighborFinset x ∩ H).card
  let A := L.filter fun x => k x = 1
  let B := L.filter fun x => k x = 0
  have hprofile := orderFortyNine_highIncidence_profile_of_one_high
    G hfree hmin hcard hHigh
  dsimp only at hprofile
  have hAcard : A.card = 8 := by
    simpa [A, L, k, H, orderFortyNineHighIncidenceCount] using hprofile.2.1
  have hBcard : B.card = 40 := by
    simpa [B, L, k, H, orderFortyNineHighIncidenceCount] using hprofile.1
  refine ⟨hAcard, hBcard, ?_⟩
  intro y hyL
  have hyNotHigh : y ∉ H := (Finset.mem_sdiff.mp hyL).2
  have hy7 : G.degree y = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y with hy7 | hy8
    · exact hy7
    · exact (hyNotHigh (by simp [H, orderFortyNineHighVertices, hy8])).elim
  have hyBudget := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
    G hfree hmin hcard hy7
  have hyWeighted :=
    orderFortyNine_sum_highIncidence_over_defectNeighbors_add_self
      G hfree hmin hcard hy7
  change (∑ x ∈ D.neighborFinset y, k x) + k y = H.card at hyWeighted
  rw [hHigh] at hyWeighted
  have hykLe : k y ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_right).trans_eq hHigh
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
    have hxNotHigh : x ∉ H := by
      intro hxH
      have hx8 : G.degree x = 8 := (Finset.mem_filter.mp hxH).2
      omega
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxNotHigh⟩
  have hkLeOne : ∀ x ∈ D.neighborFinset y, k x ≤ 1 := by
    intro x _hx
    exact (Finset.card_le_card Finset.inter_subset_right).trans_eq hHigh
  have hsumCard :
      (∑ x ∈ D.neighborFinset y, k x) =
        (D.neighborFinset y ∩ A).card := by
    calc
      (∑ x ∈ D.neighborFinset y, k x) =
          ∑ x ∈ D.neighborFinset y, if k x = 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxle := hkLeOne x hx
        by_cases hx1 : k x = 1
        · simp [hx1]
        · have hx0 : k x = 0 := by omega
          simp [hx0]
      _ = ((D.neighborFinset y).filter fun x => k x = 1).card := by
        rw [Finset.card_filter]
      _ = (D.neighborFinset y ∩ A).card := by
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_inter]
        constructor
        · rintro ⟨hxD, hx1⟩
          exact ⟨hxD, Finset.mem_filter.mpr ⟨hneighborLow x hxD, hx1⟩⟩
        · rintro ⟨hxD, hxA⟩
          exact ⟨hxD, (Finset.mem_filter.mp hxA).2⟩
  refine ⟨?_, ?_⟩
  · change D.degree y = 6 - k y
    change D.degree y + k y = 6 at hyBudget
    omega
  · calc
      (D.neighborFinset y ∩ A).card =
          ∑ x ∈ D.neighborFinset y, k x := hsumCard.symm
      _ = 1 - k y := by omega

end

end Erdos85
