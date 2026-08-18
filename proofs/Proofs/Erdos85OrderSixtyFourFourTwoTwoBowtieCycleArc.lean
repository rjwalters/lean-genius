import Proofs.Erdos85OrderSixtyFourFourTwoTwoBowtieSelectorRectangle

/-! # Exact internal-cycle arcs in the `[4,2,2]` bowtie

The selector-rectangle package only records that the relevant selector
intersections are nonempty.  Four-cycle freeness upgrades those intersections
to singletons.  Thus each corner of the opposite-owner bowtie selects a
unique arc-center in the normalized size-two closing component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a cross-component pair is owned by its second component, the
intersection of its two selectors into that component is exactly its
canonical common neighbor. -/
theorem componentNeighborFinset_inter_eq_singleton_crossCommonNeighbor_of_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c f : (secondOrderDefectGraph G).ConnectedComponent}
    (hcf : c ≠ f) (x : c.supp) (y : f.supp)
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj x.1 y.1) :
    componentNeighborFinset G (secondOrderDefectGraph G) f x.1 ∩
        componentNeighborFinset G (secondOrderDefectGraph G) f y.1 =
      {crossCommonNeighbor G hfree hcf x y} := by
  classical
  let u := crossCommonNeighbor G hfree hcf x y
  have humem : u ∈ f.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hcf x y howner
  have huspec := crossCommonNeighbor_spec G hfree hcf x y
  obtain ⟨w₀, hw₀, hw₀unique⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hcf x y
  ext w
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro hw
    have hxw : G.Adj x.1 w :=
      (G.mem_neighborFinset x.1 w).mp (Finset.mem_filter.mp hw.1).1
    have hyw : G.Adj y.1 w :=
      (G.mem_neighborFinset y.1 w).mp (Finset.mem_filter.mp hw.2).1
    exact (hw₀unique w ⟨hxw, hyw⟩).trans
      (hw₀unique u huspec).symm
  · intro hwu
    subst w
    constructor <;> rw [componentNeighborFinset, Finset.mem_filter]
    · exact ⟨(G.mem_neighborFinset x.1 u).mpr huspec.1,
        (ConnectedComponent.mem_supp_iff f u).mp humem⟩
    · exact ⟨(G.mem_neighborFinset y.1 u).mpr huspec.2,
        (ConnectedComponent.mem_supp_iff f u).mp humem⟩

/-- In the exceptional opposite-orientation bowtie, the two displayed
internal arcs of the size-two closing component are not merely witnessed by
nonempty selector intersections: the intersections are the two canonical
centers exactly.  The two alternatives record which size-two owner is the
closing component. -/
theorem orderSixtyFour_fourTwoTwo_oppositeBowtie_exact_internalCycleArcs
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
    (f = a ∧ m f = 2 ∧
      ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
        let u₁ := crossCommonNeighbor G hfree hfc.symm x y₁
        let u₂ := crossCommonNeighbor G hfree hfc.symm z y₂
        u₁ ≠ u₂ ∧
        componentNeighborFinset G (secondOrderDefectGraph G) f x.1 ∩
            componentNeighborFinset G (secondOrderDefectGraph G) f y₁.1 = {u₁} ∧
        componentNeighborFinset G (secondOrderDefectGraph G) f z.1 ∩
            componentNeighborFinset G (secondOrderDefectGraph G) f y₂.1 = {u₂}) ∨
    (f = b ∧ m f = 2 ∧
      ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
        let v₁ := crossCommonNeighbor G hfree hfc.symm z y₁
        let v₂ := crossCommonNeighbor G hfree hfc.symm x y₂
        v₁ ≠ v₂ ∧
        componentNeighborFinset G (secondOrderDefectGraph G) f y₁.1 ∩
            componentNeighborFinset G (secondOrderDefectGraph G) f z.1 = {v₁} ∧
        componentNeighborFinset G (secondOrderDefectGraph G) f y₂.1 ∩
            componentNeighborFinset G (secondOrderDefectGraph G) f x.1 = {v₂}) := by
  obtain ⟨x, z, y₁, y₂, _hy, hAxy₁, hBy₁z, hAzy₂, hBy₂x, _hCxz,
      hsep, _hexcl⟩ :=
    hasOppositeThirdEdgeInBlock_routingSkeleton
      G hfree hfc.symm hac hbc hab hopp
  have hf := orderSixtyFour_fourTwoTwo_closing_eq_first_or_secondOwner
    G hcount a b c f hab hac hbc hfc
  rcases hf with rfl | rfl
  · left
    refine ⟨rfl, hma, x, z, y₁, y₂, hsep.1, ?_, ?_⟩
    · exact componentNeighborFinset_inter_eq_singleton_crossCommonNeighbor_of_owner
        G hfree hfc.symm x y₁ hAxy₁
    · exact componentNeighborFinset_inter_eq_singleton_crossCommonNeighbor_of_owner
        G hfree hfc.symm z y₂ hAzy₂
  · right
    refine ⟨rfl, hmb, x, z, y₁, y₂, hsep.2.1, ?_, ?_⟩
    · have hzy₁ :
          (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj z.1 y₁.1 :=
        ((componentOwnerGraph G (secondOrderDefectGraph G) f).adj_comm
          y₁.1 z.1).mp hBy₁z
      simpa [Finset.inter_comm] using
        (componentNeighborFinset_inter_eq_singleton_crossCommonNeighbor_of_owner
          G hfree hfc.symm z y₁ hzy₁)
    · have hxy₂ :
          (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj x.1 y₂.1 :=
        ((componentOwnerGraph G (secondOrderDefectGraph G) f).adj_comm
          y₂.1 x.1).mp hBy₂x
      simpa [Finset.inter_comm] using
        (componentNeighborFinset_inter_eq_singleton_crossCommonNeighbor_of_owner
          G hfree hfc.symm x y₂ hxy₂)

end

end Erdos85

#print axioms Erdos85.componentNeighborFinset_inter_eq_singleton_crossCommonNeighbor_of_owner
#print axioms Erdos85.orderSixtyFour_fourTwoTwo_oppositeBowtie_exact_internalCycleArcs
