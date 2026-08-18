import Proofs.Erdos85BinarySquareOppositeOwnerBowtieCrossExclusions

/-! # Internal size-two edges forced by the `[4,2,2]` bowtie -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The first-owner pair of canonical centers lies inside the closing
component and supplies two ambient internal edges. -/
def HasFirstOwnerInternalBowtiePair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c f : (secondOrderDefectGraph G).ConnectedComponent) (hcf : c ≠ f) : Prop :=
  ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
    y₁.1 ≠ y₂.1 ∧
    let u₁ := crossCommonNeighbor G hfree hcf x y₁
    let u₂ := crossCommonNeighbor G hfree hcf z y₂
    u₁ ∈ f.supp ∧ u₂ ∈ f.supp ∧ G.Adj y₁.1 u₁ ∧ G.Adj y₂.1 u₂

/-- The second-owner pair of canonical centers lies inside the closing
component and supplies two ambient internal edges. -/
def HasSecondOwnerInternalBowtiePair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c f : (secondOrderDefectGraph G).ConnectedComponent) (hcf : c ≠ f) : Prop :=
  ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
    y₁.1 ≠ y₂.1 ∧
    let v₁ := crossCommonNeighbor G hfree hcf z y₁
    let v₂ := crossCommonNeighbor G hfree hcf x y₂
    v₁ ∈ f.supp ∧ v₂ ∈ f.supp ∧ G.Adj y₁.1 v₁ ∧ G.Adj y₂.1 v₂

/-- Every displayed internal edge in a normalized size-two component extends
through its endpoint to a second, distinct internal neighbor. -/
theorem binarySquare_regular_sizeTwoPart_exists_other_internalNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (y u : c.supp)
    (hyu : G.Adj y.1 u.1) :
    ∃ w : c.supp, w ≠ u ∧ G.Adj y.1 w.1 := by
  let H := G.induce c.supp
  have hdeg : H.degree y = 2 :=
    binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree hq hreg hcard c hc y
  have hu : u ∈ H.neighborFinset y := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hyu
  by_contra hnone
  push Not at hnone
  have hsub : H.neighborFinset y ⊆ {u} := by
    intro w hw
    simp only [Finset.mem_singleton]
    by_contra hwu
    exact hnone w hwu ((H.mem_neighborFinset y w).mp hw)
  have hle := Finset.card_le_card hsub
  change (H.neighborFinset y).card = 2 at hdeg
  rw [hdeg, Finset.card_singleton] at hle
  omega

/-- In the `[4,2,2]` labeling, the non-`c` closing component is one of the
two normalized size-two owner components. -/
theorem orderSixtyFour_fourTwoTwo_closing_eq_first_or_secondOwner
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (a b c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hfc : f ≠ c) :
    f = a ∨ f = b := by
  rcases eq_first_or_second_or_third_of_card_eq_three
    hcount a b c f hab hac hbc with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hfc h).elim

/-- The opposite-orientation `[4,2,2]` bowtie necessarily consumes two
internal ambient edges of one of the two size-two components. -/
theorem orderSixtyFour_fourTwoTwo_oppositeBowtie_internalEdgePair
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (a b c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m a = 2) (hmb : m b = 2) (hfc : f ≠ c)
    (hopp : HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) c f) :
    (m f = 2 ∧ HasFirstOwnerInternalBowtiePair G hfree c f hfc.symm) ∨
      (m f = 2 ∧ HasSecondOwnerInternalBowtiePair G hfree c f hfc.symm) := by
  have hf := orderSixtyFour_fourTwoTwo_closing_eq_first_or_secondOwner
    G hcount a b c f hab hac hbc hfc
  obtain ⟨x, z, y₁, y₂, hy, hAxy₁, hBy₁z, hAzy₂, hBy₂x, _hCxz, _hrest⟩ :=
    hasOppositeThirdEdgeInBlock_routingSkeleton
      G hfree hfc.symm hac hbc hab hopp
  rcases hf with rfl | rfl
  · left
    refine ⟨hma, x, z, y₁, y₂, hy, ?_⟩
    have hu₁mem := crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfc.symm x y₁ hAxy₁
    have hu₂mem := crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfc.symm z y₂ hAzy₂
    exact ⟨hu₁mem, hu₂mem,
      (crossCommonNeighbor_spec G hfree hfc.symm x y₁).2,
      (crossCommonNeighbor_spec G hfree hfc.symm z y₂).2⟩
  · right
    refine ⟨hmb, x, z, y₁, y₂, hy, ?_⟩
    have hv₁mem := crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfc.symm z y₁
        (by exact ((componentOwnerGraph G (secondOrderDefectGraph G) f).adj_comm
          z.1 y₁.1).mpr hBy₁z)
    have hv₂mem := crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfc.symm x y₂
        (by exact ((componentOwnerGraph G (secondOrderDefectGraph G) f).adj_comm
          x.1 y₂.1).mpr hBy₂x)
    exact ⟨hv₁mem, hv₂mem,
      (crossCommonNeighbor_spec G hfree hfc.symm z y₁).2,
      (crossCommonNeighbor_spec G hfree hfc.symm x y₂).2⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_fourTwoTwo_closing_eq_first_or_secondOwner
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_exists_other_internalNeighbor
#print axioms Erdos85.orderSixtyFour_fourTwoTwo_oppositeBowtie_internalEdgePair
