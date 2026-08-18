import Proofs.Erdos85OrderSixteenTwoFactorCensus
import Proofs.Erdos85MuThreeAllTfNativeCnf

/-! # The three even C4-free cycle shapes at order sixteen -/

namespace Erdos85

open SimpleGraph

/-- The cycle partitions represented by the three all-TF certificate shapes. -/
def IsMu3AllTfCyclePartition (l : List Nat) : Prop :=
  l = [16] ∨ l = [10, 6] ∨ l = [8, 8]

theorem mu3AllTfShape_of_cyclePartition
    (l : List Nat) (hpart : OrderSixteenCyclePartition l)
    (heven : ∀ r ∈ l, Even r) :
    IsMu3AllTfCyclePartition l := by
  rcases hpart with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [IsMu3AllTfCyclePartition, Nat.even_iff] at *

theorem exists_mu3AllTfShape_of_cyclePartition
    (l : List Nat) (hpart : OrderSixteenCyclePartition l)
    (heven : ∀ r ∈ l, Even r) :
    ∃ shape : Mu3AllTfShape,
      l = match shape with
        | .c16 => [16]
        | .c10c6 => [10, 6]
        | .c8c8 => [8, 8] := by
  rcases mu3AllTfShape_of_cyclePartition l hpart heven with h | h | h
  · exact ⟨.c16, h⟩
  · exact ⟨.c10c6, h⟩
  · exact ⟨.c8c8, h⟩

/-- A C4-free 2-factor on sixteen vertices whose components all have even
order has exactly one of the three certificate cycle shapes. -/
theorem exists_mu3AllTfShape_of_twoRegular_evenComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hdeg : ∀ x, G.degree x = 2)
    (hfree : ¬ containsC4 V G)
    (heven : ∀ c : G.ConnectedComponent, Even c.supp.ncard) :
    ∃ (shape : Mu3AllTfShape) (rs : List Nat),
      (rs = match shape with
        | .c16 => [16]
        | .c10c6 => [10, 6]
        | .c8c8 => [8, 8]) ∧
      (↑rs : Multiset Nat) =
        (Finset.univ : Finset G.ConnectedComponent).val.map
          (fun c => c.supp.ncard) := by
  obtain ⟨rs, hrs, hrsizes⟩ :=
    exists_orderSixteenCyclePartition_of_twoRegular_of_not_containsC4
      G hcard hdeg hfree
  have hrEven : ∀ r ∈ rs, Even r := by
    intro r hr
    have hr' : r ∈ (↑rs : Multiset Nat) := hr
    rw [hrsizes] at hr'
    obtain ⟨c, _hc, rfl⟩ := Multiset.mem_map.mp hr'
    exact heven c
  obtain ⟨shape, hshape⟩ :=
    exists_mu3AllTfShape_of_cyclePartition rs hrs hrEven
  exact ⟨shape, rs, hshape, hrsizes⟩

end Erdos85
