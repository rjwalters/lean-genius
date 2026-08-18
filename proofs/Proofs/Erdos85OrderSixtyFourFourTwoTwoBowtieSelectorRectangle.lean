import Proofs.Erdos85OrderSixtyFourFourTwoTwoBowtieInternalEdges
import Proofs.Erdos85BinarySquareSizeTwoOwnerLineGraph

/-! # Selector rectangles forced by the `[4,2,2]` bowtie -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every component-neighbor selector is an independent set in the
second-order defect graph: its elements share the ambient selector root. -/
theorem componentNeighborFinset_pair_not_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x : V)
    {u v : V}
    (hu : u ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x)
    (hv : v ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x)
    (huv : u ≠ v) :
    ¬ (secondOrderDefectGraph G).Adj u v := by
  have hxu : G.Adj x u :=
    (G.mem_neighborFinset x u).mp (Finset.mem_filter.mp hu).1
  have hxv : G.Adj x v :=
    (G.mem_neighborFinset x v).mp (Finset.mem_filter.mp hv).1
  exact not_secondOrderDefect_adj_of_commonNeighbor
    G hfree huv hxu.symm hxv.symm

/-- Selector pattern when the bowtie closing component is its first owner. -/
def HasForwardBowtieSelectorRectangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c f : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
    let S := componentNeighborFinset G (secondOrderDefectGraph G) f
    (S x.1).card = 2 ∧ (S z.1).card = 2 ∧
    (S y₁.1).card = 2 ∧ (S y₂.1).card = 2 ∧
    (S x.1 ∩ S y₁.1).Nonempty ∧ (S z.1 ∩ S y₂.1).Nonempty ∧
    Disjoint (S x.1) (S z.1) ∧
    Disjoint (S y₁.1) (S z.1) ∧ Disjoint (S y₂.1) (S x.1)

/-- Selector pattern when the bowtie closing component is its second owner. -/
def HasReverseBowtieSelectorRectangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c f : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
    let S := componentNeighborFinset G (secondOrderDefectGraph G) f
    (S x.1).card = 2 ∧ (S z.1).card = 2 ∧
    (S y₁.1).card = 2 ∧ (S y₂.1).card = 2 ∧
    (S y₁.1 ∩ S z.1).Nonempty ∧ (S y₂.1 ∩ S x.1).Nonempty ∧
    Disjoint (S x.1) (S z.1) ∧
    Disjoint (S x.1) (S y₁.1) ∧ Disjoint (S z.1) (S y₂.1)

/-- The opposite `[4,2,2]` bowtie becomes one of two exact rectangles of
two-element selectors in its normalized size-two closing component. -/
theorem orderSixtyFour_fourTwoTwo_oppositeBowtie_selectorRectangle
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m a = 2) (hmb : m b = 2) (hfc : f ≠ c)
    (hopp : HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) c f) :
    HasForwardBowtieSelectorRectangle G c f ∨
      HasReverseBowtieSelectorRectangle G c f := by
  have hf := orderSixtyFour_fourTwoTwo_closing_eq_first_or_secondOwner
    G hcount a b c f hab hac hbc hfc
  obtain ⟨x, z, y₁, y₂, _hy, hAxy₁, hBy₁z, hAzy₂, hBy₂x, hCxz, _hrest⟩ :=
    hasOppositeThirdEdgeInBlock_routingSkeleton
      G hfree hfc.symm hac hbc hab hopp
  have hcard (v : Fin 64) :
      (componentNeighborFinset G (secondOrderDefectGraph G) f v).card = 2 := by
    apply binarySquare_regular_sizeTwoPart_selector_card
      G hfree (q := 8) (by norm_num) hreg (by norm_num) f
    rcases hf with hf | hf
    · simpa [hf, hma] using hm f
    · simpa [hf, hmb] using hm f
  have hCzx : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 z.1 :=
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adj_comm x.1 z.1).mpr hCxz
  rcases hf with rfl | rfl
  · left
    refine ⟨x, z, y₁, y₂, hcard x.1, hcard z.1,
      hcard y₁.1, hcard y₂.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact (componentOwnerGraph_adj G (secondOrderDefectGraph G) f _ _).mp hAxy₁ |>.2
    · exact (componentOwnerGraph_adj G (secondOrderDefectGraph G) f _ _).mp hAzy₂ |>.2
    · exact componentOwnerGraph_adj_implies_other_selector_disjoint
        G hfree hac.symm hCzx
    · exact componentOwnerGraph_adj_implies_other_selector_disjoint
        G hfree hab.symm hBy₁z
    · exact componentOwnerGraph_adj_implies_other_selector_disjoint
        G hfree hab.symm hBy₂x
  · right
    refine ⟨x, z, y₁, y₂, hcard x.1, hcard z.1,
      hcard y₁.1, hcard y₂.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact (componentOwnerGraph_adj G (secondOrderDefectGraph G) f _ _).mp hBy₁z |>.2
    · exact (componentOwnerGraph_adj G (secondOrderDefectGraph G) f _ _).mp hBy₂x |>.2
    · exact componentOwnerGraph_adj_implies_other_selector_disjoint
        G hfree hbc.symm hCzx
    · exact componentOwnerGraph_adj_implies_other_selector_disjoint
        G hfree hab hAxy₁
    · exact componentOwnerGraph_adj_implies_other_selector_disjoint
        G hfree hab hAzy₂

/-- Enriched exact package: the selector rectangle lives over a 2-regular
ambient block and a 7-regular commuting defect block. -/
theorem orderSixtyFour_fourTwoTwo_oppositeBowtie_selectorRectangle_commutingBlock
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m a = 2) (hmb : m b = 2) (hfc : f ≠ c)
    (hopp : HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) c f) :
    (HasForwardBowtieSelectorRectangle G c f ∨
      HasReverseBowtieSelectorRectangle G c f) ∧
    (∀ x : f.supp, (G.induce f.supp).degree x = 2) ∧
    (∀ x : f.supp,
      ((secondOrderDefectGraph G).induce f.supp).degree x = 7) ∧
    (G.induce f.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce f.supp).adjMatrix ℤ =
      ((secondOrderDefectGraph G).induce f.supp).adjMatrix ℤ *
        (G.induce f.supp).adjMatrix ℤ := by
  have hrect := orderSixtyFour_fourTwoTwo_oppositeBowtie_selectorRectangle
    G hfree hreg hcount m hm a b c f hab hac hbc hma hmb hfc hopp
  have hf := orderSixtyFour_fourTwoTwo_closing_eq_first_or_secondOwner
    G hcount a b c f hab hac hbc hfc
  have hmf : m f = 2 := by
    rcases hf with rfl | rfl
    · exact hma
    · exact hmb
  have hblock := binarySquare_regular_sizeTwoPart_commuting_regular_blocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) f (by simpa [hmf] using hm f)
  simpa using And.intro hrect hblock

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_fourTwoTwo_oppositeBowtie_selectorRectangle
#print axioms Erdos85.componentNeighborFinset_pair_not_secondOrderDefect_adj
#print axioms Erdos85.orderSixtyFour_fourTwoTwo_oppositeBowtie_selectorRectangle_commutingBlock
