import Proofs.Erdos85BinarySquareSizeTwoCrossIndexedBlocks
import Proofs.Erdos85BinarySquareSizeTwoSelectorGraph

/-! # Owner-color 2-factorization on a size-two component -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restrict one global owner-color graph to the ground set of a source
defect component. -/
def restrictedComponentOwnerGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph source.supp :=
  (componentOwnerGraph G (secondOrderDefectGraph G) owner).induce source.supp

noncomputable instance restrictedComponentOwnerGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (restrictedComponentOwnerGraph G source owner).Adj :=
  Classical.decRel _

/-- Exact degree of an owner color restricted to one source component. -/
theorem binarySquare_regular_restrictedComponentOwnerGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    {m_source m_owner : ℕ}
    (hsource : source.supp.ncard = q * m_source)
    (howner : owner.supp.ncard = q * m_owner) (x : source.supp) :
    (restrictedComponentOwnerGraph G source owner).degree x =
      m_owner * (m_source - 1) := by
  have hcount := binarySquare_regular_sameComponent_ownerCoordinate_card
    G hfree hq hreg hcard source owner howner hsource x
  rw [← hcount]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hy' :=
      ((restrictedComponentOwnerGraph G source owner).mem_neighborFinset x y).mp hy
    apply Finset.mem_filter.mpr
    refine ⟨by simpa using y.2, ?_, ?_⟩
    · intro hval
      exact hy'.ne (Subtype.ext hval).symm
    · exact (componentOwnerGraph_adj
        G (secondOrderDefectGraph G) owner x.1 y.1).mp hy' |>.2
  · intro y₁ h₁ y₂ h₂ hy
    exact Subtype.ext hy
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hySupp : y ∈ source.supp := by simpa using hy'.1
    refine ⟨⟨y, hySupp⟩, ?_, rfl⟩
    apply ((restrictedComponentOwnerGraph G source owner).mem_neighborFinset
      x ⟨y, hySupp⟩).mpr
    exact (componentOwnerGraph_adj
      G (secondOrderDefectGraph G) owner x.1 y).mpr
        ⟨hy'.2.1.symm, hy'.2.2⟩

/-- If both source and owner coordinates have normalized size two, the
restricted owner color is a 2-regular factor. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (howner : owner.supp.ncard = q * 2) (x : source.supp) :
    (restrictedComponentOwnerGraph G source owner).degree x = 2 := by
  simpa using binarySquare_regular_restrictedComponentOwnerGraph_degree
    G hfree hq hreg hcard source owner hsource howner x

/-- The restricted owner colors uniquely edge-partition the selector
complement of the source defect block. -/
theorem selectorComplement_adj_iff_existsUnique_restrictedOwner_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source : (secondOrderDefectGraph G).ConnectedComponent) (x y : source.supp) :
    (((secondOrderDefectGraph G).induce source.supp)ᶜ).Adj x y ↔
      ∃! owner : (secondOrderDefectGraph G).ConnectedComponent,
        (restrictedComponentOwnerGraph G source owner).Adj x y := by
  by_cases hxy : x = y
  · subst y
    simp
  have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hglobal := not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
    G hfree hxyVal
  simpa [SimpleGraph.compl_adj, SimpleGraph.induce_adj,
    restrictedComponentOwnerGraph, hxy] using hglobal

end

end Erdos85
