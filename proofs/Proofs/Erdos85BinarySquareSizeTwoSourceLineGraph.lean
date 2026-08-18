import Proofs.Erdos85BinarySquareSizeTwoSourceSelectorPartition
import Proofs.Erdos85BinarySquareSizeTwoOwnerFactorization

/-! # Source-restricted size-two owner line graphs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Within the global selector-edge model for a size-two owner component,
the edges whose unique ambient selector vertex lies in `source`. -/
def sourceIndexedSelectorEdgeSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    Set {s : Finset V // ∃ u v : owner.supp,
      u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧
        s = {u.1, v.1}} :=
  {s | ∃ x : source.supp,
    s.1 = componentNeighborFinset G (secondOrderDefectGraph G) owner x.1}

/-- Intersection graph induced on the selector edges colored by one source
defect component. -/
def sourceIndexedSelectorIntersectionGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph (sourceIndexedSelectorEdgeSet G source owner) :=
  (sizeTwoSelectorIntersectionGraph G owner).induce
    (sourceIndexedSelectorEdgeSet G source owner)

noncomputable instance sourceIndexedSelectorIntersectionGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (sourceIndexedSelectorIntersectionGraph G source owner).Adj :=
  Classical.decRel _

/-- **Restricted owner-line-graph identification.**  Restricting the global
owner graph to one source component is exactly the intersection (line) graph
of the source-colored selector edges. -/
theorem binarySquare_regular_sizeTwoPart_exists_restrictedOwnerGraph_iso_sourceIntersection
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
    (howner : owner.supp.ncard = q * 2) :
    ∃ E : restrictedComponentOwnerGraph G source owner ≃g
        sourceIndexedSelectorIntersectionGraph G source owner,
      ∀ x, (E x).1.1 =
        componentNeighborFinset G (secondOrderDefectGraph G) owner x.1 := by
  obtain ⟨e, he⟩ :=
    binarySquare_regular_sizeTwoPart_exists_ownerGraph_iso_selectorIntersectionGraph
      G hfree hq hreg hcard owner howner
  let f : source.supp → sourceIndexedSelectorEdgeSet G source owner := fun x =>
    ⟨e x.1, ⟨x, he x.1⟩⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  have hfsurj : Function.Surjective f := by
    intro s
    obtain ⟨x, hx⟩ := s.2
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (he x.1).trans hx.symm
  let E0 : source.supp ≃ sourceIndexedSelectorEdgeSet G source owner :=
    Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let E : restrictedComponentOwnerGraph G source owner ≃g
      sourceIndexedSelectorIntersectionGraph G source owner :=
    { toEquiv := E0
      map_rel_iff' := by
        intro x y
        change
          (sizeTwoSelectorIntersectionGraph G owner).Adj
              (E0 x).1 (E0 y).1 ↔
            (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x.1 y.1
        have hx : (E0 x).1 = e x.1 := rfl
        have hy : (E0 y).1 = e y.1 := rfl
        rw [hx, hy]
        exact e.map_rel_iff }
  refine ⟨E, ?_⟩
  intro x
  exact he x.1

end

end Erdos85
