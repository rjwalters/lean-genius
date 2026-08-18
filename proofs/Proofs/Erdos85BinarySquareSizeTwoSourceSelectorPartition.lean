import Proofs.Erdos85BinarySquareSizeTwoOwnerLineGraph

/-! # Source-component partition of a size-two selector graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The edges of a size-two selector graph whose unique ambient selector
vertex belongs to a specified source defect component. -/
def sourceIndexedSizeTwoSelectorGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph owner.supp where
  Adj u v := u ≠ v ∧ ∃ x : source.supp,
    componentNeighborFinset G (secondOrderDefectGraph G) owner x.1 =
      {u.1, v.1}
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨x, hx⟩ := h.2
    exact ⟨x, by simpa [Finset.pair_comm] using hx⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

noncomputable instance sourceIndexedSizeTwoSelectorGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (sourceIndexedSizeTwoSelectorGraph G source owner).Adj :=
  Classical.decRel _

/-- **Source-edge partition.**  Every edge of a normalized size-two selector
graph belongs to exactly one source defect component: the component of its
unique ambient selector vertex. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_adj_iff_existsUnique_source
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * 2) (u v : owner.supp) :
    (sizeTwoSelectorGraph G (secondOrderDefectGraph G) owner).Adj u v ↔
      ∃! source : (secondOrderDefectGraph G).ConnectedComponent,
        (sourceIndexedSizeTwoSelectorGraph G source owner).Adj u v := by
  let D := secondOrderDefectGraph G
  constructor
  · rintro ⟨huv, x, hx⟩
    have hnotD :=
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard owner howner u v huv).mp ⟨x, hx⟩
    have hunique :=
      (binarySquare_regular_sizeTwoPart_existsUnique_pair_iff_not_defectAdj
        G hfree hq hreg hcard owner howner u v huv).mpr hnotD
    let source := D.connectedComponentMk x
    have hxmem : x ∈ source.supp := ConnectedComponent.connectedComponentMk_mem
    refine ⟨source, ⟨huv, ⟨⟨x, hxmem⟩, hx⟩⟩, ?_⟩
    intro source' hs'
    obtain ⟨y, hy⟩ := hs'.2
    have hyx : y.1 = x := hunique.unique hy hx
    have hycomp : D.connectedComponentMk y.1 = source' :=
      (ConnectedComponent.mem_supp_iff source' y.1).mp y.2
    rw [hyx] at hycomp
    exact hycomp.symm
  · rintro ⟨source, hs, _hunique⟩
    exact ⟨hs.1, ⟨hs.2.choose.1, hs.2.choose_spec⟩⟩

/-- Distinct source components contribute edge-disjoint subgraphs of the
size-two selector graph. -/
theorem sourceIndexedSizeTwoSelectorGraph_adj_disjoint_of_source_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * 2)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) {u v : owner.supp} :
    (sourceIndexedSizeTwoSelectorGraph G source owner).Adj u v →
      ¬ (sourceIndexedSizeTwoSelectorGraph G target owner).Adj u v := by
  intro hs ht
  have hall :=
    (binarySquare_regular_sizeTwoSelectorGraph_adj_iff_existsUnique_source
      G hfree hq hreg hcard owner howner u v).mp
      ⟨hs.1, ⟨hs.2.choose.1, hs.2.choose_spec⟩⟩
  exact hst (hall.unique ht hs).symm

end

end Erdos85
