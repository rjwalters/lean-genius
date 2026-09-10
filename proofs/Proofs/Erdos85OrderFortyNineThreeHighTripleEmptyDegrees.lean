import Proofs.Erdos85OrderFortyNineThreeHighSupportDegreeLedger
import Proofs.Erdos85OrderFortyNineThreeHighOneFiber

/-! Actual empty-neighbor degrees in the H3 triple-support profile. -/
namespace Erdos85
open SimpleGraph
noncomputable section

variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
  (hone : orderFortyNineHighIncidenceCount G 3 = 1)
include hfree hmin

private theorem positive_support_mem_low {x : Fin 49}
    (hx : 0 < (orderFortyNineHighSupport G x).card) :
    x ∈ orderFortyNineLowVertices G := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  intro hH
  have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hH
  change (orderFortyNineHighSupport G x).card = 0 at hz
  omega

include hHigh hone

private theorem triple_profile_no_pair_support (x : Fin 49) :
    (orderFortyNineHighSupport G x).card ≠ 2 := by
  intro hx
  have hlow := positive_support_mem_low G hfree hmin (show 0 < (orderFortyNineHighSupport G x).card by omega)
  have hc := (threeHigh_t1_global_incidence G hfree hmin hHigh hone).2.2
  have hempty : ((orderFortyNineLowVertices G).filter fun y =>
      (orderFortyNineHighSupport G y).card = 2) = ∅ := Finset.card_eq_zero.mp hc
  have hm : x ∈ (orderFortyNineLowVertices G).filter (fun y => (orderFortyNineHighSupport G y).card = 2) := Finset.mem_filter.mpr ⟨hlow, hx⟩
  rw [hempty] at hm
  exact Finset.notMem_empty x hm

omit hHigh in
private theorem triple_profile_support_three_iff
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) (x : Fin 49) :
    (orderFortyNineHighSupport G x).card = 3 ↔ x = z := by
  obtain ⟨w, hw, huniq⟩ := threeHigh_t1_exists_unique_triple_support G hone
  have hzlow := positive_support_mem_low G hfree hmin (show 0 < (orderFortyNineHighSupport G z).card by omega)
  have hzw := huniq z ⟨hzlow, hz⟩
  constructor
  · intro hx
    have hxlow := positive_support_mem_low G hfree hmin (show 0 < (orderFortyNineHighSupport G x).card by omega)
    exact (huniq x ⟨hxlow, hx⟩).trans hzw.symm
  · rintro rfl
    exact hz

theorem threeHigh_triple_empty_neighbor_degree
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {v : Fin 49} (hv : G.degree v = 7) :
    (G.neighborFinset v ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0)).card +
      (orderFortyNineHighSupport G v).card = 4 + 2 * (if G.Adj v z then 1 else 0) := by
  classical
  have hpair : ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact triple_profile_no_pair_support G hfree hmin hHigh hone x (Finset.mem_filter.mp hx).2
  have htriple : ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3) =
      if G.Adj v z then {z} else ∅ := by
    ext x
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      triple_profile_support_three_iff G hfree hmin hone z hz x]
    by_cases h : G.Adj v z <;> simp [h] <;> aesop
  have h := threeHigh_empty_support_neighbor_ledger G hfree hmin hHigh hv
  rw [hpair, htriple] at h
  by_cases hAdj : G.Adj v z <;> simpa [hAdj] using h

theorem threeHigh_triple_root_empty_neighbor_count
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) :
    (G.neighborFinset z ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0)).card = 1 := by
  have hzlow := positive_support_mem_low G hfree hmin (show 0 < (orderFortyNineHighSupport G z).card by omega)
  have hz7 : G.degree z = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) z with h | h
    · exact h
    · have hznot := (Finset.mem_sdiff.mp hzlow).2
      exact (hznot (by simp [orderFortyNineHighVertices, h])).elim
  have h := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hz7
  simp only [hz, G.loopless.irrefl, if_false, mul_zero, Nat.add_zero] at h
  omega


theorem threeHigh_triple_empty_degree_histogram
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) :
    let E := (orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0
    (E.filter fun x => (G.neighborFinset x ∩ E).card = 6).card = 1 ∧
      (E.filter fun x => (G.neighborFinset x ∩ E).card = 4).card = 23 := by
  classical
  let E := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 0
  change (E.filter fun x => (G.neighborFinset x ∩ E).card = 6).card = 1 ∧
    (E.filter fun x => (G.neighborFinset x ∩ E).card = 4).card = 23
  have hE : E.card = 24 := (threeHigh_t1_global_incidence G hfree hmin hHigh hone).1
  have hd (x : Fin 49) (hx : x ∈ E) :
      (G.neighborFinset x ∩ E).card = 4 + 2 * (if G.Adj x z then 1 else 0) := by
    have hp := Finset.mem_filter.mp hx
    have hx7 : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) x with h | h
      · exact h
      · exact ((Finset.mem_sdiff.mp hp.1).2 (by simp [orderFortyNineHighVertices, h])).elim
    have hh := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
    simpa only [hp.2, Nat.add_zero] using hh
  have h6 : (E.filter fun x => (G.neighborFinset x ∩ E).card = 6) = E ∩ G.neighborFinset z := by
    ext x
    by_cases hx : x ∈ E
    · have hh := hd x hx
      by_cases ha : G.Adj x z
      · simp [hx, hh, ha, ha.symm]
      · have hrev : ¬ G.Adj z x := fun h => ha h.symm
        simp [hx, hh, ha, hrev]
    · simp [hx]
  have h4 : (E.filter fun x => (G.neighborFinset x ∩ E).card = 4) = E \ G.neighborFinset z := by
    ext x
    by_cases hx : x ∈ E
    · have hh := hd x hx
      by_cases ha : G.Adj x z
      · simp [hx, hh, ha, ha.symm]
      · have hrev : ¬ G.Adj z x := fun h => ha h.symm
        simp [hx, hh, ha, hrev]
    · simp [hx]
  have hroot : (E ∩ G.neighborFinset z).card = 1 := by
    rw [Finset.inter_comm]
    exact threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
  rw [h6, h4]
  refine ⟨hroot, ?_⟩
  have hc := Finset.card_sdiff_add_card_inter E (G.neighborFinset z)
  rw [hroot, hE] at hc
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_neighbor_degree
#print axioms Erdos85.threeHigh_triple_root_empty_neighbor_count

#print axioms Erdos85.threeHigh_triple_empty_degree_histogram
