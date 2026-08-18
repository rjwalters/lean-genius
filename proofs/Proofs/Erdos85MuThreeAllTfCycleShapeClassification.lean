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

/-- A `{±1}` labeling flipped by every edge is an explicit bipartite
coloring.  This is the abstract content of the adjacency eigenvalue `-2` on
a 2-regular internal factor. -/
def signedFlipColoring
    {V : Type*} (G : SimpleGraph V) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, G.Adj x y → s x = -s y) :
    G.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk
    (fun x => if s x = 1 then 0 else 1)
    (by
      intro x y hxy
      have hx := hsign x
      have hy := hsign y
      have hf := hflip hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        simp_all)

theorem signedFlip_isBipartite
    {V : Type*} (G : SimpleGraph V) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, G.Adj x y → s x = -s y) :
    G.IsBipartite :=
  ⟨signedFlipColoring G s hsign hflip⟩

/-- Every component of a bipartite 2-factor has even order. -/
theorem twoRegular_bipartite_component_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 2) (hbip : G.IsBipartite)
    (c : G.ConnectedComponent) : Even c.supp.ncard := by
  obtain ⟨x, p, hp, hpverts, _hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph G hdeg c
  have hloopEven : Even p.length :=
    (SimpleGraph.two_colorable_iff_forall_loop_even.mp hbip) x p
  have hlen : p.length = c.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
  rwa [hlen] at hloopEven

/-- Shape classification directly from an alternating signed labeling. -/
theorem exists_mu3AllTfShape_of_twoRegular_signedFlip
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hdeg : ∀ x, G.degree x = 2)
    (hfree : ¬ containsC4 V G)
    (s : V → ℤ) (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, G.Adj x y → s x = -s y) :
    ∃ (shape : Mu3AllTfShape) (rs : List Nat),
      (rs = match shape with
        | .c16 => [16]
        | .c10c6 => [10, 6]
        | .c8c8 => [8, 8]) ∧
      (↑rs : Multiset Nat) =
        (Finset.univ : Finset G.ConnectedComponent).val.map
          (fun c => c.supp.ncard) := by
  apply exists_mu3AllTfShape_of_twoRegular_evenComponents G hcard hdeg hfree
  exact twoRegular_bipartite_component_even G hdeg
    (signedFlip_isBipartite G s hsign hflip)

end Erdos85
