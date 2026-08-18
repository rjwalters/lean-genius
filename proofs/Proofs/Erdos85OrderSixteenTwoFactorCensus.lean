import Proofs.Erdos85IsCyclesComponentCharpoly
import Proofs.Erdos85OrderSixteenCyclePartition

/-! # Graph-facing cycle census at order sixteen -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The connected-component orders of a 2-regular graph on sixteen vertices,
provided no component has order four, form one of the twelve explicit cycle
partitions.  The returned list retains multiplicity and is sorted decreasingly. -/
theorem exists_orderSixteenCyclePartition_of_twoRegular
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = 16)
    (hdeg : ∀ x, G.degree x = 2)
    (hfour : ∀ c : G.ConnectedComponent, c.supp.ncard ≠ 4) :
    ∃ rs : List ℕ,
      OrderSixteenCyclePartition rs ∧
      (↑rs : Multiset ℕ) =
        (Finset.univ : Finset G.ConnectedComponent).val.map
          (fun c ↦ c.supp.ncard) := by
  classical
  let sizes : Multiset ℕ :=
    (Finset.univ : Finset G.ConnectedComponent).val.map
      (fun c ↦ c.supp.ncard)
  let rs := sizes.sort (· ≥ ·)
  have hrsizes : (↑rs : Multiset ℕ) = sizes := by
    exact Multiset.sort_eq sizes (· ≥ ·)
  have hsumComponents :
      (∑ c : G.ConnectedComponent, c.supp.ncard) = Fintype.card V := by
    calc
      (∑ c : G.ConnectedComponent, c.supp.ncard) =
          ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c _hc
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
  have hrsum : rs.sum = 16 := by
    calc
      rs.sum = sizes.sum := by
        change (↑rs : Multiset ℕ).sum = sizes.sum
        rw [hrsizes]
      _ = ∑ c : G.ConnectedComponent, c.supp.ncard := by
        simp [sizes]
      _ = 16 := hsumComponents.trans hcard
  have hrparts : ∀ r ∈ rs, 3 ≤ r ∧ r ≠ 4 := by
    intro r hr
    have hrsizesMem : r ∈ sizes := by
      rw [← hrsizes]
      exact hr
    obtain ⟨c, _hc, rfl⟩ := Multiset.mem_map.mp hrsizesMem
    obtain ⟨q, hqthree, hqsize, _hqpoly⟩ :=
      twoRegular_component_charpoly_chebyshev G hdeg c
    exact ⟨hqsize ▸ hqthree, hfour c⟩
  have hrsorted : rs.Pairwise (· ≥ ·) :=
    Multiset.pairwise_sort sizes (· ≥ ·)
  refine ⟨rs,
    orderSixteen_cycle_partition_classification rs hrsum hrparts hrsorted, ?_⟩
  exact hrsizes

/-- C4-freeness supplies the no-order-four hypothesis automatically. -/
theorem exists_orderSixteenCyclePartition_of_twoRegular_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = 16)
    (hdeg : ∀ x, G.degree x = 2) (hfree : ¬ containsC4 V G) :
    ∃ rs : List ℕ,
      OrderSixteenCyclePartition rs ∧
      (↑rs : Multiset ℕ) =
        (Finset.univ : Finset G.ConnectedComponent).val.map
          (fun c ↦ c.supp.ncard) := by
  apply exists_orderSixteenCyclePartition_of_twoRegular G hcard hdeg
  intro c hc4
  exact hfree (twoRegular_containsC4_of_component_order_four G hdeg c hc4)

end

end Erdos85
