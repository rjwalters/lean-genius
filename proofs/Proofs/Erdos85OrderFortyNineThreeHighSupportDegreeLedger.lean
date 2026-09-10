import Proofs.Erdos85OrderFortyNineThreeHighLargeSupportNeighbors

/-! Actual H3 neighbor degree ledger, with high vertices removed from empty support. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem support_zero_indicator_identity (k : Nat) (hk : k ≤ 3) :
    (if k = 0 then 1 else 0) + k =
      1 + (if k = 2 then 1 else 0) + 2 * (if k = 3 then 1 else 0) := by
  interval_cases k <;> decide

variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
include hfree hmin hHigh

theorem threeHigh_zero_support_neighbor_ledger
    {v : Fin 49} (hv : G.degree v = 7) :
    ((G.neighborFinset v).filter fun x => (orderFortyNineHighSupport G x).card = 0).card =
      4 + ((G.neighborFinset v).filter fun x => (orderFortyNineHighSupport G x).card = 2).card +
      2 * ((G.neighborFinset v).filter fun x => (orderFortyNineHighSupport G x).card = 3).card := by
  classical
  have hweight := orderFortyNine_sum_highIncidence_over_lowNeighborhood
    G hfree hmin (Fintype.card_fin 49) hv
  change (∑ x ∈ G.neighborFinset v, (orderFortyNineHighSupport G x).card) = _ at hweight
  rw [hHigh] at hweight
  have hsum := Finset.sum_congr (s₁ := G.neighborFinset v) rfl (fun x _ =>
    support_zero_indicator_identity (orderFortyNineHighSupport G x).card (by
      have h := Finset.card_le_card (show orderFortyNineHighSupport G x ⊆
        orderFortyNineHighVertices G from Finset.inter_subset_right)
      omega))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.card_filter, Finset.sum_const, smul_eq_mul, mul_one,
    G.card_neighborFinset_eq_degree, hv, hweight] at hsum
  omega

theorem threeHigh_empty_support_neighbor_ledger
    {v : Fin 49} (hv : G.degree v = 7) :
    (G.neighborFinset v ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0)).card +
      (orderFortyNineHighSupport G v).card =
      4 + ((G.neighborFinset v).filter fun x => (orderFortyNineHighSupport G x).card = 2).card +
      2 * ((G.neighborFinset v).filter fun x => (orderFortyNineHighSupport G x).card = 3).card := by
  classical
  let Z := (G.neighborFinset v).filter fun x => (orderFortyNineHighSupport G x).card = 0
  have hzH : Z ∩ orderFortyNineHighVertices G = orderFortyNineHighSupport G v := by
    ext x
    constructor
    · intro hx
      have hp := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp.1).1, hp.2⟩
    · intro hx
      have hp := Finset.mem_inter.mp hx
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hp.1, ?_⟩, hp.2⟩
      simpa [orderFortyNineHighSupport] using
        orderFortyNine_highNeighborCount_eq_zero_of_high G hfree hmin (Fintype.card_fin 49) hp.2
  have hzL : Z \ orderFortyNineHighVertices G =
      G.neighborFinset v ∩ ((orderFortyNineLowVertices G).filter fun x =>
        (orderFortyNineHighSupport G x).card = 0) := by
    ext x
    simp only [Z, orderFortyNineLowVertices, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_inter, Finset.mem_univ, true_and]
    tauto
  have hc := Finset.card_sdiff_add_card_inter Z (orderFortyNineHighVertices G)
  rw [hzH, hzL] at hc
  rw [hc]
  exact threeHigh_zero_support_neighbor_ledger G hfree hmin hHigh hv


theorem threeHigh_empty_vertex_empty_degree_bounds
    {v : Fin 49} (hv : G.degree v = 7)
    (hs : (orderFortyNineHighSupport G v).card = 0) :
    let E := (orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0
    4 ≤ (G.neighborFinset v ∩ E).card ∧
      (G.neighborFinset v ∩ E).card ≤ 6 := by
  classical
  dsimp only
  have hledger := threeHigh_empty_support_neighbor_ledger G hfree hmin hHigh hv
  rw [hs, Nat.add_zero] at hledger
  have hweight := orderFortyNine_sum_highIncidence_over_lowNeighborhood
    G hfree hmin (Fintype.card_fin 49) hv
  change (∑ x ∈ G.neighborFinset v, (orderFortyNineHighSupport G x).card) = _ at hweight
  rw [hHigh] at hweight
  have hbound : (∑ x ∈ G.neighborFinset v,
      (2 * (if (orderFortyNineHighSupport G x).card = 2 then 1 else 0) +
      3 * (if (orderFortyNineHighSupport G x).card = 3 then 1 else 0))) ≤
      ∑ x ∈ G.neighborFinset v, (orderFortyNineHighSupport G x).card := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases h2 : (orderFortyNineHighSupport G x).card = 2
    · simp [h2]
    · by_cases h3 : (orderFortyNineHighSupport G x).card = 3
      · simp [h3]
      · simp [h2, h3]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
    hweight] at hbound
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_zero_support_neighbor_ledger
#print axioms Erdos85.threeHigh_empty_support_neighbor_ledger

#print axioms Erdos85.threeHigh_empty_vertex_empty_degree_bounds
